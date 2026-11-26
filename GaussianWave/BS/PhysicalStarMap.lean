import GaussianWave.BS.StarFrame
import GaussianWave.BS.LinearEntropy
import GaussianWave.Covariance

/-!
# Actual whitening coordinates for a constrained physical star

The white-coordinate root/simplex frame is mapped bijectively onto the
physical eigenrelation hyperplane. Its two-coordinate edge map is the actual
invertible alpha/beta matrix, so the proved linear entropy Jacobian applies.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianWave.BS

def physicalStarMatrix (d : ℕ) (c : ℝ) : Matrix (Fin (d + 1)) (Fin d) ℝ :=
  Fin.cases (starRootDirection d)
    (fun i j => c * starRootDirection d j + rho c * starSimplexDirection d i j)

def physicalStarMap (d : ℕ) (c : ℝ) : (Fin d → ℝ) →ₗ[ℝ] (Fin (d + 1) → ℝ) :=
  (physicalStarMatrix d c).mulVecLin

@[simp] theorem physicalStarMap_root (d : ℕ) (c : ℝ) (y : Fin d → ℝ) :
    physicalStarMap d c y 0 = starRootForm y := starRootDirection_apply y

@[simp] theorem physicalStarMap_leaf (d : ℕ) (c : ℝ) (y : Fin d → ℝ) (i : Fin d) :
    physicalStarMap d c y i.succ = c * starRootForm y +
      rho c * (transverseScale d * starCenteredCoordinate y i) := by
  change (∑ j, (c * starRootDirection d j + rho c * starSimplexDirection d i j) * y j) = _
  simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum,
    starRootDirection_apply, starSimplexDirection_apply]

/-- The actual physical eigenrelation, with lambda=d*c. -/
theorem physicalStarMap_eigenrelation (d : ℕ) (hd : 0 < d) (c : ℝ) (y : Fin d → ℝ) :
    (∑ i : Fin d, physicalStarMap d c y i.succ) = (d : ℝ) * c * physicalStarMap d c y 0 := by
  simp_rw [physicalStarMap_leaf]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, sum_starCenteredCoordinate hd,
    mul_zero, add_zero, physicalStarMap_root]
  ring

def physicalStarHyperplane (d : ℕ) (c : ℝ) : Submodule ℝ (Fin (d + 1) → ℝ) where
  carrier := {z | (∑ i : Fin d, z i.succ) = (d : ℝ) * c * z 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, Pi.add_apply, Finset.sum_add_distrib] at hx hy ⊢
    rw [hx, hy]
    ring
  smul_mem' := by
    intro a x hx
    simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum] at hx ⊢
    rw [hx]
    ring

@[simp] theorem mem_physicalStarHyperplane (d : ℕ) (c : ℝ) (z : Fin (d + 1) → ℝ) :
    z ∈ physicalStarHyperplane d c ↔ (∑ i : Fin d, z i.succ) = (d : ℝ) * c * z 0 := Iff.rfl

def physicalStarInverse (d : ℕ) (c : ℝ) (z : Fin (d + 1) → ℝ) : Fin d → ℝ :=
  fun i => z 0 / Real.sqrt d + (z i.succ - c * z 0) / (rho c * transverseScale d)

theorem transverseScale_pos (d : ℕ) (hd : 2 ≤ d) : 0 < transverseScale d := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by
    have h : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  exact Real.sqrt_pos.mpr (div_pos hd0 hd1)

theorem starRootForm_div_sqrt {d : ℕ} (hd : 0 < d) (y : Fin d → ℝ) :
    starRootForm y / Real.sqrt d = (∑ j, y j) / d := by
  unfold starRootForm
  rw [div_div, ← pow_two, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ d)]

theorem physicalStarInverse_left_inverse
    (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1) (y : Fin d → ℝ) :
    physicalStarInverse d c (physicalStarMap d c y) = y := by
  have hr : rho c * transverseScale d ≠ 0 :=
    mul_ne_zero (rho_pos c hc).ne' (transverseScale_pos d hd).ne'
  ext i
  simp only [physicalStarInverse, physicalStarMap_root, physicalStarMap_leaf]
  rw [starRootForm_div_sqrt (by omega)]
  have he : c * starRootForm y + rho c * (transverseScale d * starCenteredCoordinate y i) -
      c * starRootForm y = (rho c * transverseScale d) * starCenteredCoordinate y i := by ring
  rw [he, mul_div_cancel_left₀ _ hr]
  unfold starCenteredCoordinate
  ring

theorem starRootForm_physicalStarInverse
    (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (z : Fin (d + 1) → ℝ)
    (hz : z ∈ physicalStarHyperplane d c) :
    starRootForm (physicalStarInverse d c z) = z 0 := by
  have hs : Real.sqrt (d : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < d)).ne'
  have hs2 : Real.sqrt (d : ℝ) ^ 2 = d := Real.sq_sqrt (by positivity)
  change (∑ i : Fin d, z i.succ) = (d : ℝ) * c * z 0 at hz
  unfold starRootForm physicalStarInverse
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_div, Finset.sum_sub_distrib]
  rw [hz]
  simp only [← mul_assoc, sub_self, zero_div, add_zero]
  field_simp [hs]

theorem physicalStarInverse_right_inverse
    (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1) (z : Fin (d + 1) → ℝ)
    (hz : z ∈ physicalStarHyperplane d c) :
    physicalStarMap d c (physicalStarInverse d c z) = z := by
  have hr : rho c * transverseScale d ≠ 0 :=
    mul_ne_zero (rho_pos c hc).ne' (transverseScale_pos d hd).ne'
  have hroot := starRootForm_physicalStarInverse d hd c z hz
  have hmean : (∑ j, physicalStarInverse d c z j) / d = z 0 / Real.sqrt d := by
    rw [← starRootForm_div_sqrt (by omega), hroot]
  ext a
  refine Fin.cases ?_ (fun i => ?_) a
  · simpa using hroot
  · rw [physicalStarMap_leaf, hroot]
    unfold starCenteredCoordinate
    rw [hmean]
    simp only [physicalStarInverse]
    have he : z 0 / Real.sqrt ↑d + (z i.succ - c * z 0) / (rho c * transverseScale d) -
        z 0 / Real.sqrt ↑d = (z i.succ - c * z 0) / (rho c * transverseScale d) := by ring
    rw [he]
    calc
      _ = c * z 0 + (rho c * transverseScale d) *
          ((z i.succ - c * z 0) / (rho c * transverseScale d)) := by ring
      _ = z i.succ := by rw [mul_div_cancel₀ _ hr]; ring

/-- The white d-space is actually linearly equivalent to the physical
eigenrelation hyperplane. -/
def physicalStarEquiv (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1) :
    (Fin d → ℝ) ≃ₗ[ℝ] physicalStarHyperplane d c where
  toFun y := ⟨physicalStarMap d c y, physicalStarMap_eigenrelation d (by omega) c y⟩
  invFun z := physicalStarInverse d c z
  left_inv := physicalStarInverse_left_inverse d hd c hc
  right_inv z := Subtype.ext (physicalStarInverse_right_inverse d hd c hc z z.property)
  map_add' x y := Subtype.ext ((physicalStarMap d c).map_add x y)
  map_smul' a x := Subtype.ext ((physicalStarMap d c).map_smul a x)

@[simp] theorem physicalStarEquiv_coe (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1)
    (y : Fin d → ℝ) : (physicalStarEquiv d hd c hc y : Fin (d + 1) → ℝ) = physicalStarMap d c y := rfl

/-- The physical endpoint matrix, with coordinates ordered by Bool. -/
def physicalEdgeMatrix (c : ℝ) : Matrix Bool Bool ℝ :=
  fun b b' => if b = b' then alpha c else beta c

theorem physicalEdgeMatrix_det (c : ℝ) (hc : |c| < 1) :
    (physicalEdgeMatrix c).det = rho c := by
  rw [← Matrix.det_reindex_self finTwoEquiv.symm (physicalEdgeMatrix c), Matrix.det_fin_two]
  norm_num [Matrix.reindex, Matrix.submatrix, physicalEdgeMatrix, finTwoEquiv]
  nlinarith [alpha_sq_sub_beta_sq c hc]

theorem physicalEdgeMatrix_mulVec_false (c : ℝ) (x : Bool → ℝ) :
    (physicalEdgeMatrix c).mulVec x false = alpha c * x false + beta c * x true := by
  simp [physicalEdgeMatrix, Matrix.mulVec, dotProduct, Fintype.sum_bool]
  ring

theorem physicalEdgeMatrix_mulVec_true (c : ℝ) (x : Bool → ℝ) :
    (physicalEdgeMatrix c).mulVec x true = beta c * x false + alpha c * x true := by
  simp [physicalEdgeMatrix, Matrix.mulVec, dotProduct, Fintype.sum_bool]
  ring

/-- The actual physical endpoints are an invertible linear image of the
orthonormal edge observations used in the upper proof. -/
theorem physicalStarMap_edge (d : ℕ) (c : ℝ) (hc : |c| < 1) (i : Fin d) (y : Fin d → ℝ) :
    (fun b : Bool => if b then physicalStarMap d c y i.succ else physicalStarMap d c y 0) =
      (physicalEdgeMatrix c).mulVec ((starEdgeProjection d c i).mulVec y) := by
  have ha := alpha_sq_add_beta_sq c hc
  have hab := two_alpha_mul_beta c hc
  have hr := alpha_sq_sub_beta_sq c hc
  ext b
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, physicalStarMap_root, physicalEdgeMatrix_mulVec_false]
    rw [starEdgeProjection_apply_false, starEdgeProjection_apply_true]
    simp only [scoreA, scoreB, smul_eq_mul]
    calc
      _ = (alpha c ^ 2 + beta c ^ 2) * starRootForm y := by rw [ha]; ring
      _ = _ := by ring
  · simp only [↓reduceIte, physicalStarMap_leaf, physicalEdgeMatrix_mulVec_true]
    rw [starEdgeProjection_apply_false, starEdgeProjection_apply_true]
    simp only [scoreA, scoreB, smul_eq_mul]
    calc
      _ = (2 * alpha c * beta c) * starRootForm y +
          (alpha c ^ 2 - beta c ^ 2) * (transverseScale d * starCenteredCoordinate y i) := by rw [hab, hr]
      _ = _ := by ring

theorem starSimplexDirection_dot (d : ℕ) (hd : 2 ≤ d) (i j : Fin d) :
    (∑ k, starSimplexDirection d i k * starSimplexDirection d j k) =
      if i = j then 1 else -1 / ((d : ℝ) - 1) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have h : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hbase : (∑ k : Fin d,
      ((if k = i then (1 : ℝ) else 0) - 1 / (d : ℝ)) *
        ((if k = j then (1 : ℝ) else 0) - 1 / (d : ℝ))) =
      (if i = j then (1 : ℝ) else 0) - 1 / (d : ℝ) := by
    simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, ite_mul, mul_ite,
      one_mul, zero_mul, mul_one, mul_zero]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    split_ifs <;> simp_all
  simp_rw [starSimplexDirection_entry]
  have hexpand (k : Fin d) :
      (transverseScale d * ((if k = i then 1 else 0) - 1 / (d : ℝ))) *
        (transverseScale d * ((if k = j then 1 else 0) - 1 / (d : ℝ))) =
      transverseScale d ^ 2 * (((if k = i then 1 else 0) - 1 / (d : ℝ)) *
        ((if k = j then 1 else 0) - 1 / (d : ℝ))) := by ring
  simp_rw [hexpand]
  rw [← Finset.mul_sum, hbase, transverseScale_sq d hd]
  split_ifs <;> field_simp <;> ring

private theorem physical_row_inner_expansion {J : Type*} [Fintype J]
    (w e f : J → ℝ) (c s : ℝ) :
    (∑ j, (c * w j + s * e j) * (c * w j + s * f j)) =
      c ^ 2 * (∑ j, w j ^ 2) +
        c * s * ((∑ j, w j * e j) + (∑ j, w j * f j)) + s ^ 2 * (∑ j, e j * f j) := by
  rw [Finset.mul_sum, Finset.mul_sum, mul_add, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The actual whitening matrix has precisely the canonical Gaussian-wave
star covariance as its Gram matrix. -/
theorem physicalStarMatrix_gram (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1) :
    physicalStarMatrix d c * (physicalStarMatrix d c).transpose =
      RegularEigenData.starWaveCovariance d ((d : ℝ) * c) := by
  have hdpos : 0 < d := by omega
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hdpos.ne'
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have h : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  ext a b
  refine Fin.cases ?_ (fun i => ?_) a
  · refine Fin.cases ?_ (fun j => ?_) b
    · simpa only [Matrix.mul_apply, Matrix.transpose_apply, physicalStarMatrix,
        Fin.cases_zero, RegularEigenData.starWaveCovariance, pow_two] using starRootDirection_norm_sq d hdpos
    · change (∑ k, starRootDirection d k *
        (c * starRootDirection d k + rho c * starSimplexDirection d j k)) = (d : ℝ) * c / d
      simp only [mul_add, Finset.sum_add_distrib]
      have h (k : Fin d) : starRootDirection d k * (c * starRootDirection d k) =
          c * starRootDirection d k ^ 2 := by ring
      simp_rw [h, mul_left_comm (starRootDirection d _) (rho c)]
      rw [← Finset.mul_sum, ← Finset.mul_sum, starRootDirection_norm_sq d hdpos,
        starRootDirection_dot_simplex d hdpos]
      field_simp
  · refine Fin.cases ?_ (fun j => ?_) b
    · change (∑ k, (c * starRootDirection d k + rho c * starSimplexDirection d i k) *
        starRootDirection d k) = (d : ℝ) * c / d
      have he : (∑ k, (c * starRootDirection d k + rho c * starSimplexDirection d i k) *
          starRootDirection d k) =
          (∑ k, starRootDirection d k *
            (c * starRootDirection d k + rho c * starSimplexDirection d i k)) := by
        apply Finset.sum_congr rfl
        intro k _
        ring
      rw [he]
      simp only [mul_add, Finset.sum_add_distrib]
      have h (k : Fin d) : starRootDirection d k * (c * starRootDirection d k) =
          c * starRootDirection d k ^ 2 := by ring
      simp_rw [h, mul_left_comm (starRootDirection d _) (rho c)]
      rw [← Finset.mul_sum, ← Finset.mul_sum, starRootDirection_norm_sq d hdpos,
        starRootDirection_dot_simplex d hdpos]
      field_simp
    · change (∑ k, (c * starRootDirection d k + rho c * starSimplexDirection d i k) *
        (c * starRootDirection d k + rho c * starSimplexDirection d j k)) =
        if i = j then 1 else (((d : ℝ) * c) ^ 2 - d) / ((d : ℝ) * (d - 1))
      rw [physical_row_inner_expansion, starRootDirection_norm_sq d hdpos,
        starRootDirection_dot_simplex d hdpos, starRootDirection_dot_simplex d hdpos,
        starSimplexDirection_dot d hd, rho_sq c hc]
      split_ifs <;> field_simp <;> ring

/-- The explicit rectangular inverse used to whiten actual physical laws. -/
def physicalStarInverseMatrix (d : ℕ) (c : ℝ) : Matrix (Fin d) (Fin (d + 1)) ℝ :=
  fun i => Fin.cases (1 / Real.sqrt d - c / (rho c * transverseScale d))
    (fun j => if j = i then 1 / (rho c * transverseScale d) else 0)

theorem physicalStarInverseMatrix_mulVec (d : ℕ) (c : ℝ) (z : Fin (d + 1) → ℝ) :
    (physicalStarInverseMatrix d c).mulVec z = physicalStarInverse d c z := by
  ext i
  simp only [physicalStarInverseMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    Fin.cases_zero, Fin.cases_succ, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, physicalStarInverse]
  ring

theorem physicalStarInverseMatrix_left_inverse
    (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1) :
    physicalStarInverseMatrix d c * physicalStarMatrix d c = 1 := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro y
  change (physicalStarInverseMatrix d c * physicalStarMatrix d c).mulVec y =
    (1 : Matrix (Fin d) (Fin d) ℝ).mulVec y
  rw [← Matrix.mulVec_mulVec, physicalStarInverseMatrix_mulVec, Matrix.one_mulVec]
  exact physicalStarInverse_left_inverse d hd c hc y

/-- Whitening followed by the physical map reconstructs every actual law
supported on the physical eigenrelation hyperplane. -/
theorem physicalStarMap_inverse_law
    (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1)
    (μ : Measure (Fin (d + 1) → ℝ))
    (hsupport : ∀ᵐ z ∂μ, z ∈ physicalStarHyperplane d c) :
    Measure.map (physicalStarMap d c)
      (Measure.map (fun z => (physicalStarInverseMatrix d c).mulVec z) μ) = μ := by
  rw [Measure.map_map (physicalStarMap d c).continuous_of_finiteDimensional.measurable
    (measurable_finiteMatrixAction (physicalStarInverseMatrix d c))]
  calc
    _ = Measure.map id μ := by
      apply Measure.map_congr
      filter_upwards [hsupport] with z hz
      change physicalStarMap d c ((physicalStarInverseMatrix d c).mulVec z) = z
      rw [physicalStarInverseMatrix_mulVec]
      exact physicalStarInverse_right_inverse d hd c hc z hz
    _ = μ := Measure.map_id

def physicalEdgeCoordinates {d : ℕ} (i : Fin d) (z : Fin (d + 1) → ℝ) : Bool → ℝ :=
  fun b => if b then z i.succ else z 0

theorem measurable_physicalEdgeCoordinates {d : ℕ} (i : Fin d) :
    Measurable (physicalEdgeCoordinates i) := by
  unfold physicalEdgeCoordinates
  apply measurable_pi_lambda
  intro b
  cases b <;> exact measurable_pi_apply _

/-- The physical edge law is the actual linear image of the proved
orthonormal edge law. -/
theorem physicalStarMap_edge_law (d : ℕ) (c : ℝ) (hc : |c| < 1) (i : Fin d)
    (μ : Measure (Fin d → ℝ)) :
    Measure.map (physicalEdgeCoordinates i) (Measure.map (physicalStarMap d c) μ) =
      Measure.map (fun x => (physicalEdgeMatrix c).mulVec x)
        (Measure.map (fun y => (starEdgeProjection d c i).mulVec y) μ) := by
  rw [Measure.map_map (measurable_physicalEdgeCoordinates i) (physicalStarMap d c).continuous_of_finiteDimensional.measurable,
    Measure.map_map (measurable_finiteMatrixAction (physicalEdgeMatrix c))
      (measurable_finiteMatrixAction (starEdgeProjection d c i))]
  congr 1
  funext y
  exact physicalStarMap_edge d c hc i y

theorem physicalEdge_entropy_change
    (c : ℝ) (hc : |c| < 1) {ν : Measure (Bool → ℝ)} [IsProbabilityMeasure ν]
    (f : FiniteEntropyDensity ν) :
    (f.linearImage (physicalEdgeMatrix c)
      (by rw [physicalEdgeMatrix_det c hc]; exact (rho_pos c hc).ne')).entropy =
      f.entropy + Real.log (rho c) := by
  rw [FiniteEntropyDensity.linearImage_entropy, physicalEdgeMatrix_det c hc,
    abs_of_pos (rho_pos c hc)]

/-- A chart on the physical eigenrelation hyperplane composed with actual
whitening is an honest square linear equivalence. For an intrinsic Euclidean
entropy chart, this chart is chosen orthonormally; the relative cancellation
below in fact holds for every linear chart. -/
def physicalStarChart (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1)
    (chart : physicalStarHyperplane d c ≃ₗ[ℝ] (Fin d → ℝ)) :
    (Fin d → ℝ) ≃ₗ[ℝ] (Fin d → ℝ) := (physicalStarEquiv d hd c hc).trans chart

def physicalStarChartMatrix (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1)
    (chart : physicalStarHyperplane d c ≃ₗ[ℝ] (Fin d → ℝ)) : Matrix (Fin d) (Fin d) ℝ :=
  LinearMap.toMatrix' (physicalStarChart d hd c hc chart).toLinearMap

theorem physicalStarChartMatrix_mulVec (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1)
    (chart : physicalStarHyperplane d c ≃ₗ[ℝ] (Fin d → ℝ)) (y : Fin d → ℝ) :
    (physicalStarChartMatrix d hd c hc chart).mulVec y = chart (physicalStarEquiv d hd c hc y) := by
  change Matrix.toLin' (LinearMap.toMatrix' (physicalStarChart d hd c hc chart).toLinearMap) y = _
  rw [Matrix.toLin'_toMatrix']
  rfl

theorem physicalStarChartMatrix_det_ne_zero (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1)
    (chart : physicalStarHyperplane d c ≃ₗ[ℝ] (Fin d → ℝ)) :
    (physicalStarChartMatrix d hd c hc chart).det ≠ 0 := by
  simpa only [physicalStarChartMatrix, LinearMap.det_toMatrix'] using
    (physicalStarChart d hd c hc chart).isUnit_det'.ne_zero

/-- Finite entropy in actual physical intrinsic coordinates, represented by
the chosen chart, is constructed from the white law by an actual Jacobian. -/
def FiniteEntropyDensity.physicalStarChart
    (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1)
    (chart : physicalStarHyperplane d c ≃ₗ[ℝ] (Fin d → ℝ))
    {μ : Measure (Fin d → ℝ)} [IsProbabilityMeasure μ] (f : FiniteEntropyDensity μ) :
    FiniteEntropyDensity (Measure.map (fun y => chart (physicalStarEquiv d hd c hc y)) μ) := by
  let h := f.linearImage (physicalStarChartMatrix d hd c hc chart)
    (physicalStarChartMatrix_det_ne_zero d hd c hc chart)
  refine ⟨h.density, h.measurable, h.nonneg, h.integrable, h.integral_eq_one, h.integrable_log, ?_⟩
  rw [← h.measure_eq]
  congr 1
  funext y
  exact (physicalStarChartMatrix_mulVec d hd c hc chart y).symm

/-- The full-star whitening Jacobian cancels from Gaussian-relative entropy
in every intrinsic chart, so no closed determinant formula is needed. -/
theorem physicalStarChart_entropy_difference
    (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1)
    (chart : physicalStarHyperplane d c ≃ₗ[ℝ] (Fin d → ℝ))
    {μ ν : Measure (Fin d → ℝ)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : FiniteEntropyDensity μ) (g : FiniteEntropyDensity ν) :
    (f.physicalStarChart d hd c hc chart).entropy -
      (g.physicalStarChart d hd c hc chart).entropy = f.entropy - g.entropy := by
  exact f.linearImage_entropy_difference g (physicalStarChartMatrix d hd c hc chart)
    (physicalStarChartMatrix_det_ne_zero d hd c hc chart)

end GaussianWave.BS
