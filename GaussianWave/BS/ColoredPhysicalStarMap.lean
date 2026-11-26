import GaussianWave.BS.PhysicalStarMap
import GaussianWave.BS.ColoredStarFrame

/-!
# Actual common-energy physical whitening in finitely many channels

The maps act on all channels jointly. Their block structure is geometric;
it imposes no independence assumption on a transported probability law.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianWave.BS

def channelLiftMatrix {I J : Type*} (r : ℕ) (A : Matrix I J ℝ) :
    Matrix (Fin r × I) (Fin r × J) ℝ := fun p q => if q.1 = p.1 then A p.2 q.2 else 0

@[simp] theorem channelLiftMatrix_mulVec {I J : Type*} [Fintype J]
    (r : ℕ) (A : Matrix I J ℝ) (x : (Fin r × J) → ℝ) (a : Fin r) (i : I) :
    (channelLiftMatrix r A).mulVec x (a, i) = A.mulVec (fun j => x (a, j)) i := by
  simp [channelLiftMatrix, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, ite_mul]

theorem channelLiftMatrix_mul {I J K : Type*} [Fintype J]
    (r : ℕ) (A : Matrix I J ℝ) (B : Matrix J K ℝ) :
    channelLiftMatrix r A * channelLiftMatrix r B = channelLiftMatrix r (A * B) := by
  ext p q
  rcases p with ⟨a, i⟩
  rcases q with ⟨b, k⟩
  by_cases hab : b = a
  · subst b
    simp [channelLiftMatrix, Matrix.mul_apply, Fintype.sum_prod_type, ite_mul]
  · simp [channelLiftMatrix, Matrix.mul_apply, Fintype.sum_prod_type, ite_mul, mul_ite, hab]

@[simp] theorem channelLiftMatrix_transpose {I J : Type*} (r : ℕ) (A : Matrix I J ℝ) :
    (channelLiftMatrix r A).transpose = channelLiftMatrix r A.transpose := by
  ext p q
  simp [channelLiftMatrix, Matrix.transpose_apply, eq_comm]

@[simp] theorem channelLiftMatrix_one {I : Type*} [DecidableEq I] (r : ℕ) :
    channelLiftMatrix r (1 : Matrix I I ℝ) = 1 := by
  ext p q
  rcases p with ⟨a, i⟩
  rcases q with ⟨b, j⟩
  by_cases hab : b = a
  · subst b
    simp [channelLiftMatrix, Matrix.one_apply, Prod.mk.injEq]
  · simp [channelLiftMatrix, Matrix.one_apply, Prod.mk.injEq, hab, Ne.symm hab]

def coloredPhysicalStarMatrix (d r : ℕ) (c : ℝ) :
    Matrix (Fin r × Fin (d + 1)) (Fin r × Fin d) ℝ := channelLiftMatrix r (physicalStarMatrix d c)

def coloredPhysicalStarInverseMatrix (d r : ℕ) (c : ℝ) :
    Matrix (Fin r × Fin d) (Fin r × Fin (d + 1)) ℝ := channelLiftMatrix r (physicalStarInverseMatrix d c)

def coloredPhysicalStarMap (d r : ℕ) (c : ℝ) :
    ((Fin r × Fin d) → ℝ) →ₗ[ℝ] ((Fin r × Fin (d + 1)) → ℝ) :=
  (coloredPhysicalStarMatrix d r c).mulVecLin

@[simp] theorem coloredPhysicalStarMap_apply
    (d r : ℕ) (c : ℝ) (y : (Fin r × Fin d) → ℝ) (a : Fin r) (j : Fin (d + 1)) :
    coloredPhysicalStarMap d r c y (a, j) = physicalStarMap d c (fun i => y (a, i)) j :=
  channelLiftMatrix_mulVec r (physicalStarMatrix d c) y a j

def coloredPhysicalStarHyperplane (d r : ℕ) (c : ℝ) : Submodule ℝ ((Fin r × Fin (d + 1)) → ℝ) where
  carrier := {z | ∀ a, (fun j => z (a, j)) ∈ physicalStarHyperplane d c}
  zero_mem' := fun a => (physicalStarHyperplane d c).zero_mem
  add_mem' hx hy := fun a => (physicalStarHyperplane d c).add_mem (hx a) (hy a)
  smul_mem' s x hx := fun a => (physicalStarHyperplane d c).smul_mem s (hx a)

def coloredPhysicalStarInverse (d r : ℕ) (c : ℝ)
    (z : (Fin r × Fin (d + 1)) → ℝ) : (Fin r × Fin d) → ℝ :=
  fun p => physicalStarInverse d c (fun j => z (p.1, j)) p.2

theorem coloredPhysicalStarInverse_left_inverse
    (d r : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1) (y : (Fin r × Fin d) → ℝ) :
    coloredPhysicalStarInverse d r c (coloredPhysicalStarMap d r c y) = y := by
  ext p
  rcases p with ⟨a, i⟩
  have h := congrFun (physicalStarInverse_left_inverse d hd c hc (fun j => y (a, j))) i
  simpa only [coloredPhysicalStarInverse, coloredPhysicalStarMap_apply] using h

theorem coloredPhysicalStarInverse_right_inverse
    (d r : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1)
    (z : (Fin r × Fin (d + 1)) → ℝ) (hz : z ∈ coloredPhysicalStarHyperplane d r c) :
    coloredPhysicalStarMap d r c (coloredPhysicalStarInverse d r c z) = z := by
  ext p
  rcases p with ⟨a, j⟩
  have h := congrFun (physicalStarInverse_right_inverse d hd c hc (fun k => z (a, k)) (hz a)) j
  simpa only [coloredPhysicalStarMap_apply, coloredPhysicalStarInverse] using h

def coloredPhysicalStarEquiv (d r : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1) :
    ((Fin r × Fin d) → ℝ) ≃ₗ[ℝ] coloredPhysicalStarHyperplane d r c where
  toFun y := ⟨coloredPhysicalStarMap d r c y, fun a => by
    change (fun j => coloredPhysicalStarMap d r c y (a, j)) ∈ physicalStarHyperplane d c
    simp only [coloredPhysicalStarMap_apply]
    exact physicalStarMap_eigenrelation d (by omega) c (fun j => y (a, j))⟩
  invFun z := coloredPhysicalStarInverse d r c z
  left_inv := coloredPhysicalStarInverse_left_inverse d r hd c hc
  right_inv z := Subtype.ext (coloredPhysicalStarInverse_right_inverse d r hd c hc z z.property)
  map_add' x y := Subtype.ext ((coloredPhysicalStarMap d r c).map_add x y)
  map_smul' s x := Subtype.ext ((coloredPhysicalStarMap d r c).map_smul s x)

@[simp] theorem coloredPhysicalStarEquiv_coe
    (d r : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1) (y : (Fin r × Fin d) → ℝ) :
    (coloredPhysicalStarEquiv d r hd c hc y : (Fin r × Fin (d + 1)) → ℝ) = coloredPhysicalStarMap d r c y := rfl

theorem coloredPhysicalStarInverseMatrix_left_inverse
    (d r : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1) :
    coloredPhysicalStarInverseMatrix d r c * coloredPhysicalStarMatrix d r c = 1 := by
  rw [coloredPhysicalStarInverseMatrix, coloredPhysicalStarMatrix, channelLiftMatrix_mul,
    physicalStarInverseMatrix_left_inverse d hd c hc, channelLiftMatrix_one]

def coloredPhysicalStarCovariance (d r : ℕ) (c : ℝ) :
    Matrix (Fin r × Fin (d + 1)) (Fin r × Fin (d + 1)) ℝ :=
  channelLiftMatrix r (RegularEigenData.starWaveCovariance d ((d : ℝ) * c))

theorem coloredPhysicalStarMatrix_gram
    (d r : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1) :
    coloredPhysicalStarMatrix d r c * (coloredPhysicalStarMatrix d r c).transpose =
      coloredPhysicalStarCovariance d r c := by
  rw [coloredPhysicalStarMatrix, channelLiftMatrix_transpose, channelLiftMatrix_mul,
    physicalStarMatrix_gram d hd c hc]
  rfl

def endpointLiftMatrix {I J : Type*} (r : ℕ) (A : Matrix I J ℝ) :
    Matrix (I × Fin r) (J × Fin r) ℝ := fun p q => if q.2 = p.2 then A p.1 q.1 else 0

@[simp] theorem endpointLiftMatrix_mulVec {I J : Type*} [Fintype J]
    (r : ℕ) (A : Matrix I J ℝ) (x : (J × Fin r) → ℝ) (i : I) (a : Fin r) :
    (endpointLiftMatrix r A).mulVec x (i, a) = A.mulVec (fun j => x (j, a)) i := by
  simp [endpointLiftMatrix, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, ite_mul]

theorem endpointLiftMatrix_mul {I J K : Type*} [Fintype J]
    (r : ℕ) (A : Matrix I J ℝ) (B : Matrix J K ℝ) :
    endpointLiftMatrix r A * endpointLiftMatrix r B = endpointLiftMatrix r (A * B) := by
  ext p q
  rcases p with ⟨i, a⟩
  rcases q with ⟨k, b⟩
  by_cases hab : b = a
  · subst b
    simp [endpointLiftMatrix, Matrix.mul_apply, Fintype.sum_prod_type, ite_mul]
  · simp [endpointLiftMatrix, Matrix.mul_apply, Fintype.sum_prod_type, ite_mul, mul_ite, hab]

@[simp] theorem endpointLiftMatrix_one {I : Type*} [DecidableEq I] (r : ℕ) :
    endpointLiftMatrix r (1 : Matrix I I ℝ) = 1 := by
  ext p q
  rcases p with ⟨i, a⟩
  rcases q with ⟨j, b⟩
  by_cases hab : b = a
  · subst b
    simp [endpointLiftMatrix, Matrix.one_apply, Prod.mk.injEq]
  · simp [endpointLiftMatrix, Matrix.one_apply, Prod.mk.injEq, hab, Ne.symm hab]

def coloredPhysicalEdgeMatrix (r : ℕ) (c : ℝ) : Matrix (Bool × Fin r) (Bool × Fin r) ℝ :=
  endpointLiftMatrix r (physicalEdgeMatrix c)

theorem coloredPhysicalEdgeMatrix_det_ne_zero (r : ℕ) (c : ℝ) (hc : |c| < 1) :
    (coloredPhysicalEdgeMatrix r c).det ≠ 0 := by
  have hM : (physicalEdgeMatrix c).det ≠ 0 := by rw [physicalEdgeMatrix_det c hc]; exact (rho_pos c hc).ne'
  have h := endpointLiftMatrix_mul r (physicalEdgeMatrix c) (physicalEdgeMatrix c)⁻¹
  rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hM), endpointLiftMatrix_one] at h
  exact Matrix.det_ne_zero_of_right_inverse h

def coloredPhysicalEdgeCoordinates {d r : ℕ} (i : Fin d)
    (z : (Fin r × Fin (d + 1)) → ℝ) : (Bool × Fin r) → ℝ :=
  fun p => physicalEdgeCoordinates i (fun j => z (p.2, j)) p.1

theorem measurable_coloredPhysicalEdgeCoordinates {d r : ℕ} (i : Fin d) :
    Measurable (coloredPhysicalEdgeCoordinates (r := r) i) := by
  apply measurable_pi_lambda
  rintro ⟨b, a⟩
  cases b <;> exact measurable_pi_apply _

theorem coloredPhysicalStarMap_edge
    (d r : ℕ) (c : ℝ) (hc : |c| < 1) (i : Fin d) (y : (Fin r × Fin d) → ℝ) :
    coloredPhysicalEdgeCoordinates i (coloredPhysicalStarMap d r c y) =
      (coloredPhysicalEdgeMatrix r c).mulVec ((coloredStarEdgeProjection d r c i).mulVec y) := by
  ext p
  rcases p with ⟨b, a⟩
  simp only [coloredPhysicalEdgeCoordinates, coloredPhysicalStarMap_apply,
    coloredPhysicalEdgeMatrix, endpointLiftMatrix_mulVec, coloredStarEdgeProjection_mulVec]
  exact congrFun (physicalStarMap_edge d c hc i (fun j => y (a, j))) b

def coloredPhysicalStarChartMatrix
    (d r : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1)
    (chart : coloredPhysicalStarHyperplane d r c ≃ₗ[ℝ] ((Fin r × Fin d) → ℝ)) :
    Matrix (Fin r × Fin d) (Fin r × Fin d) ℝ :=
  LinearMap.toMatrix' ((coloredPhysicalStarEquiv d r hd c hc).trans chart).toLinearMap

theorem coloredPhysicalStarChartMatrix_mulVec
    (d r : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1)
    (chart : coloredPhysicalStarHyperplane d r c ≃ₗ[ℝ] ((Fin r × Fin d) → ℝ)) (y : (Fin r × Fin d) → ℝ) :
    (coloredPhysicalStarChartMatrix d r hd c hc chart).mulVec y = chart (coloredPhysicalStarEquiv d r hd c hc y) := by
  change Matrix.toLin' (LinearMap.toMatrix' _) y = _
  rw [Matrix.toLin'_toMatrix']
  rfl

theorem coloredPhysicalStarChartMatrix_det_ne_zero
    (d r : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1)
    (chart : coloredPhysicalStarHyperplane d r c ≃ₗ[ℝ] ((Fin r × Fin d) → ℝ)) :
    (coloredPhysicalStarChartMatrix d r hd c hc chart).det ≠ 0 := by
  simpa only [coloredPhysicalStarChartMatrix, LinearMap.det_toMatrix'] using
    ((coloredPhysicalStarEquiv d r hd c hc).trans chart).isUnit_det'.ne_zero

end GaussianWave.BS
