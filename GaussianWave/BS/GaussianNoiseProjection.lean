import GaussianWave.BS.GaussianNoiseCoordinates

/-!
# Removing the redundant constant Gaussian sibling coordinates

The nonredundant factor followed by its adjoint is exactly the blockwise
centering projection.  The finite Gaussian reconstruction ignores those
constant directions, so removing them preserves the actual Gaussian law.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianWave.BS

def branchNoiseAdjoint (m : ℕ) : (k : ℕ) → (BranchNoise (m + 1) k → ℝ) →
    (BranchInnovation (m + 1) k → ℝ)
  | 0, _ => Empty.elim
  | k + 1, z => Sum.elim
      ((centeredNoiseFrame m).transpose.mulVec (fun i => z (Sum.inl i)))
      (fun aj => branchNoiseAdjoint m k (fun j => z (Sum.inr (aj.1, j))) aj.2)

def branchNoiseCenter (m : ℕ) : (k : ℕ) → (BranchNoise (m + 1) k → ℝ) →
    (BranchNoise (m + 1) k → ℝ)
  | 0, _ => Empty.elim
  | k + 1, z => Sum.elim (centeredNoise (fun i => z (Sum.inl i)))
      (fun aj => branchNoiseCenter m k (fun j => z (Sum.inr (aj.1, j))) aj.2)

theorem matrix_linearForm_adjoint {I J : Type*} [Fintype I] [Fintype J]
    (N : Matrix I J ℝ) (z : J → ℝ) (w : I → ℝ) :
    finiteLinearForm (N.mulVec z) w = finiteLinearForm z (N.transpose.mulVec w) := by
  change N.mulVec z ⬝ᵥ w = z ⬝ᵥ N.transpose.mulVec w
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, dotProduct_comm]

theorem branchOrthoNoiseLift_adjoint (m k : ℕ)
    (z : BranchInnovation (m + 1) k → ℝ) (w : BranchNoise (m + 1) k → ℝ) :
    finiteLinearForm (branchOrthoNoiseLift m k z) w =
      finiteLinearForm z (branchNoiseAdjoint m k w) := by
  induction k with
  | zero => simp [finiteLinearForm, BranchInnovation, BranchNoise]
  | succ k ih =>
      change (∑ j : Fin (m + 1) ⊕ (Fin (m + 1) × BranchNoise (m + 1) k),
        branchOrthoNoiseLift m (k + 1) z j * w j) =
        ∑ j : Fin m ⊕ (Fin (m + 1) × BranchInnovation (m + 1) k),
          z j * branchNoiseAdjoint m (k + 1) w j
      simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, branchOrthoNoiseLift,
        branchNoiseAdjoint, Sum.elim_inl, Sum.elim_inr]
      rw [show (∑ i, (centeredNoiseFrame m).mulVec (fun j => z (Sum.inl j)) i * w (Sum.inl i)) =
          ∑ j, z (Sum.inl j) * (centeredNoiseFrame m).transpose.mulVec (fun i => w (Sum.inl i)) j from
          matrix_linearForm_adjoint _ _ _]
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      exact ih (fun j => z (Sum.inr (a, j))) (fun j => w (Sum.inr (a, j)))

theorem centeredNoiseFrame_projection (m : ℕ) (z : Fin (m + 1) → ℝ) :
    (centeredNoiseFrame m).mulVec ((centeredNoiseFrame m).transpose.mulVec z) = centeredNoise z := by
  rw [Matrix.mulVec_mulVec]
  ext a
  change (∑ b, (centeredNoiseFrame m * (centeredNoiseFrame m).transpose) a b * z b) = _
  simp_rw [centeredNoiseFrame_gram]
  simpa only [finiteLinearForm, centeredNoiseRow, Nat.cast_add, Nat.cast_one, eq_comm] using
    centeredNoiseRow_apply (m + 1) a z

theorem branchOrthoNoiseLift_projection (m k : ℕ) (z : BranchNoise (m + 1) k → ℝ) :
    branchOrthoNoiseLift m k (branchNoiseAdjoint m k z) = branchNoiseCenter m k z := by
  induction k with
  | zero => ext j; exact Empty.elim j
  | succ k ih =>
      ext j
      cases j with
      | inl a => exact congrFun (centeredNoiseFrame_projection m (fun j => z (Sum.inl j))) a
      | inr aj => exact congrFun (ih (fun j => z (Sum.inr (aj.1, j)))) aj.2

theorem branchNoiseInnovation_center (m k : ℕ) (scale : ℝ)
    (z : BranchNoise (m + 1) k → ℝ) :
    branchNoiseInnovation m k scale (branchNoiseCenter m k z) = branchNoiseInnovation m k scale z := by
  induction k with
  | zero => ext j; exact Empty.elim j
  | succ k ih =>
      ext j
      cases j with
      | inl i =>
          simp only [branchNoiseInnovation, branchNoiseCenter, Sum.elim_inl, centeredNoise]
          ring
      | inr aj => exact congrFun (ih (fun j => z (Sum.inr (aj.1, j)))) aj.2

def forestNoiseLift (A : Type*) (m k : ℕ) :
    ((A ⊕ (A × BranchInnovation (m + 1) k)) → ℝ) →ₗ[ℝ]
      ((A ⊕ (A × BranchNoise (m + 1) k)) → ℝ) where
  toFun z := Sum.elim (fun a => z (Sum.inl a))
    (fun aj => branchOrthoNoiseLift m k (fun j => z (Sum.inr (aj.1, j))) aj.2)
  map_add' z w := by
    ext j
    cases j with
    | inl a => rfl
    | inr aj => exact congrFun (branchOrthoNoiseLift_add m k _ _) aj.2
  map_smul' a z := by
    ext j
    cases j with
    | inl b => rfl
    | inr bj => exact congrFun (branchOrthoNoiseLift_smul m k a _) bj.2

def forestNoiseAdjoint (A : Type*) (m k : ℕ)
    (z : (A ⊕ (A × BranchNoise (m + 1) k)) → ℝ) :
    (A ⊕ (A × BranchInnovation (m + 1) k)) → ℝ :=
  Sum.elim (fun a => z (Sum.inl a))
    (fun aj => branchNoiseAdjoint m k (fun j => z (Sum.inr (aj.1, j))) aj.2)

def forestNoiseCenter (A : Type*) (m k : ℕ)
    (z : (A ⊕ (A × BranchNoise (m + 1) k)) → ℝ) :
    (A ⊕ (A × BranchNoise (m + 1) k)) → ℝ :=
  Sum.elim (fun a => z (Sum.inl a))
    (fun aj => branchNoiseCenter m k (fun j => z (Sum.inr (aj.1, j))) aj.2)

theorem forestNoiseLift_adjoint (A : Type*) [Fintype A] (m k : ℕ)
    (z : (A ⊕ (A × BranchInnovation (m + 1) k)) → ℝ)
    (w : (A ⊕ (A × BranchNoise (m + 1) k)) → ℝ) :
    finiteLinearForm (forestNoiseLift A m k z) w = finiteLinearForm z (forestNoiseAdjoint A m k w) := by
  simp only [finiteLinearForm, Fintype.sum_sum_type, Fintype.sum_prod_type, forestNoiseLift,
    forestNoiseAdjoint, Sum.elim_inl, Sum.elim_inr, LinearMap.coe_mk, AddHom.coe_mk]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  exact branchOrthoNoiseLift_adjoint m k _ _

theorem forestNoiseLift_projection (A : Type*) (m k : ℕ)
    (z : (A ⊕ (A × BranchNoise (m + 1) k)) → ℝ) :
    forestNoiseLift A m k (forestNoiseAdjoint A m k z) = forestNoiseCenter A m k z := by
  ext j
  cases j with
  | inl a => rfl
  | inr aj => exact congrFun (branchOrthoNoiseLift_projection m k (fun j => z (Sum.inr (aj.1, j)))) aj.2

theorem transpose_toMatrix_apply_of_adjoint {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (T : (J → ℝ) →ₗ[ℝ] (I → ℝ)) (adj : (I → ℝ) → (J → ℝ))
    (h : ∀ z w, finiteLinearForm (T z) w = finiteLinearForm z (adj w)) (w : I → ℝ) :
    (LinearMap.toMatrix' T).transpose.mulVec w = adj w := by
  ext j
  have hj := h (fun j' => if j' = j then 1 else 0) w
  simpa only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, LinearMap.toMatrix'_apply,
    finiteLinearForm, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] using hj

theorem vertexGaussianMap_center (m k : ℕ) (energy : ℝ) (z : VertexGaussianInput m k → ℝ) :
    vertexGaussianMap m k energy (forestNoiseCenter (Fin (m + 2)) m k z) = vertexGaussianMap m k energy z := by
  apply congrArg (vertexBallBuild m k energy)
  ext j
  cases j with
  | inl a => rfl
  | inr aj => exact congrFun (branchNoiseInnovation_center m k _ (fun j => z (Sum.inr (aj.1, j)))) aj.2

theorem edgeGaussianMap_center (m k : ℕ) (energy : ℝ) (z : EdgeGaussianInput m k → ℝ) :
    edgeGaussianMap m k energy (forestNoiseCenter Bool m k z) = edgeGaussianMap m k energy z := by
  apply congrArg (edgeBallBuild m k energy)
  ext j
  cases j with
  | inl b => rfl
  | inr bj => exact congrFun (branchNoiseInnovation_center m k _ (fun j => z (Sum.inr (bj.1, j)))) bj.2

theorem toMatrix_mulVec_apply {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (T : (J → ℝ) →ₗ[ℝ] (I → ℝ)) (z : J → ℝ) :
    (LinearMap.toMatrix' T).mulVec z = T z :=
  congrArg (fun f => f z) (Matrix.toLin'_toMatrix' T)

theorem linearImageGaussian_eq_of_gram {I J V : Type*} [Fintype I] [Fintype J] [Fintype V]
    (M : Matrix V I ℝ) (L : Matrix V J ℝ) (h : M * M.transpose = L * L.transpose) :
    linearImageGaussian M = linearImageGaussian L := by
  apply measure_eq_of_linear_characteristic
  intro t
  change (∫ x, Complex.exp ((↑(finiteLinearForm t x) : ℂ) * Complex.I) ∂linearImageGaussian M) =
    ∫ x, Complex.exp ((↑(finiteLinearForm t x) : ℂ) * Complex.I) ∂linearImageGaussian L
  rw [linearImageGaussian_characteristic, linearImageGaussian_characteristic, h]

theorem map_standardVector_eq_linearImage {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (T : (J → ℝ) →ₗ[ℝ] (I → ℝ)) :
    Measure.map T (standardVector J) = linearImageGaussian (LinearMap.toMatrix' T) := by
  unfold linearImageGaussian
  congr 1
  exact (funext (toMatrix_mulVec_apply T)).symm

/-- Actual Gaussian source reduction through a computed orthogonal
projection; no Gaussian law or covariance conclusion is an input. -/
theorem gaussian_source_projection_reduction {I J V : Type*}
    [Fintype I] [Fintype J] [Fintype V] [DecidableEq I] [DecidableEq J]
    (f : (I → ℝ) →ₗ[ℝ] (V → ℝ)) (T : (J → ℝ) →ₗ[ℝ] (I → ℝ))
    (adj : (I → ℝ) → (J → ℝ)) (projection : (I → ℝ) → (I → ℝ))
    (hadj : ∀ z w, finiteLinearForm (T z) w = finiteLinearForm z (adj w))
    (hproj : ∀ w, T (adj w) = projection w)
    (hf : ∀ w, f (projection w) = f w) :
    Measure.map (f.comp T) (standardVector J) = Measure.map f (standardVector I) := by
  let M := LinearMap.toMatrix' f
  let L := LinearMap.toMatrix' T
  have hML : M * L * L.transpose = M := by
    apply Matrix.ext_of_mulVec_single
    intro i
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    dsimp only [M, L]
    rw [transpose_toMatrix_apply_of_adjoint T adj hadj]
    rw [toMatrix_mulVec_apply T, hproj, toMatrix_mulVec_apply f,
      toMatrix_mulVec_apply f, hf]
  have hgram : (M * L) * (M * L).transpose = M * M.transpose := by
    rw [Matrix.transpose_mul]
    calc
      _ = (M * L * L.transpose) * M.transpose := by simp only [Matrix.mul_assoc]
      _ = M * M.transpose := by rw [hML]
  rw [map_standardVector_eq_linearImage, map_standardVector_eq_linearImage,
    LinearMap.toMatrix'_comp]
  exact linearImageGaussian_eq_of_gram _ _ hgram

theorem vertexOrthoGaussianLaw_eq (m k : ℕ) (energy : ℝ) :
    Measure.map (vertexOrthoGaussianMap m k energy)
      (standardVector (VertexBallInnovation (m + 2) k)) = vertexGaussianBallLaw m k energy :=
  gaussian_source_projection_reduction (vertexGaussianMap m k energy) (vertexOrthoInputLift m k)
    (forestNoiseAdjoint (Fin (m + 2)) m k) (forestNoiseCenter (Fin (m + 2)) m k)
    (forestNoiseLift_adjoint _ m k) (forestNoiseLift_projection _ m k)
    (vertexGaussianMap_center m k energy)

theorem edgeOrthoGaussianLaw_eq (m k : ℕ) (energy : ℝ) :
    Measure.map (edgeOrthoGaussianMap m k energy)
      (standardVector (EdgeBallInnovation (m + 2) k)) = edgeGaussianBallLaw m k energy :=
  gaussian_source_projection_reduction (edgeGaussianMap m k energy) (edgeOrthoInputLift m k)
    (forestNoiseAdjoint Bool m k) (forestNoiseCenter Bool m k)
    (forestNoiseLift_adjoint _ m k) (forestNoiseLift_projection _ m k)
    (edgeGaussianMap_center m k energy)

end GaussianWave.BS
