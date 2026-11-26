import Mathlib
import GeneralizedBulk.Matrix.CovarianceDeterminant

/-! A sharp dimension-free Euclidean operator-norm bound from actual
nonnegative Hermitian quadratic forms. -/
noncomputable section
open scoped BigOperators Matrix.L2OpNorm

namespace GeneralizedBulk.Covariance

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem nonneg_toEuclideanCLM_of_quadratic (Q : Matrix I I ℝ) (hQ : Q.IsHermitian)
    (hpos : ∀ x : I → ℝ,0 ≤ dotProduct x (Q.mulVec x)) :
    0 ≤ Matrix.toEuclideanCLM (n := I) (𝕜 := ℝ) Q := by
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
  constructor
  · apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    exact Matrix.isHermitian_iff_isSymmetric.mp hQ
  · intro x
    rw [ContinuousLinearMap.reApplyInnerSelf_apply,EuclideanSpace.inner_eq_star_dotProduct]
    simp only [Matrix.piLp_equiv_toEuclideanCLM,Matrix.toLin'_apply,star_trivial]
    exact hpos ((WithLp.equiv 2 (I → ℝ)) x)

set_option maxHeartbeats 2000000 in
theorem hermitian_opNorm_le_of_quadratic (Q : Matrix I I ℝ) (hQ : Q.IsHermitian)
    (hi : ℝ) (hhi : 0 ≤ hi)
    (hpos : ∀ x : I → ℝ,0 ≤ dotProduct x (Q.mulVec x))
    (hupper : ∀ x : I → ℝ,dotProduct x (Q.mulVec x) ≤ hi*∑ i,x i^2) : ‖Q‖ ≤ hi := by
  let T := Matrix.toEuclideanCLM (n := I) (𝕜 := ℝ) Q
  let b := hQ.eigenvectorBasis
  have hsym : (T : EuclideanSpace ℝ I →ₗ[ℝ] EuclideanSpace ℝ I).IsSymmetric :=
    Matrix.isHermitian_iff_isSymmetric.mp hQ
  have heig (j : I) : T (b j) = hQ.eigenvalues j • b j := by
    apply (WithLp.equiv 2 (I → ℝ)).injective
    exact hQ.mulVec_eigenvectorBasis j
  have hrepr (x : EuclideanSpace ℝ I) (j : I) : b.repr (T x) j = hQ.eigenvalues j*b.repr x j := by
    have hh : @inner ℝ _ _ (T (b j)) x = @inner ℝ _ _ (b j) (T x) := hsym (b j) x
    rw [OrthonormalBasis.repr_apply_apply,OrthonormalBasis.repr_apply_apply,← hh,heig]
    simp [inner_smul_left]
  have hnorm (x : EuclideanSpace ℝ I) : ‖x‖^2 = ∑ i,x i^2 := by
    rw [← real_inner_self_eq_norm_sq,PiLp.inner_apply]
    simp only [RCLike.inner_apply,conj_trivial,pow_two]
  have hEigBound (j : I) : 0 ≤ hQ.eigenvalues j ∧ hQ.eigenvalues j ≤ hi :=
    eigenvalue_bounds_of_quadratic Q hQ 0 hi (fun x => ⟨by simpa only [zero_mul] using hpos x,hupper x⟩) j
  rw [Matrix.cstar_norm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ hhi
  intro x
  have hs : ‖T x‖^2 ≤ (hi*‖x‖)^2 := by
    rw [← b.repr.norm_map (T x),hnorm]
    simp_rw [hrepr,mul_pow]
    calc
      _ ≤ ∑ j,hi^2*(b.repr x j)^2 := Finset.sum_le_sum (fun j hj =>
        mul_le_mul_of_nonneg_right ((sq_le_sq₀ (hEigBound j).1 hhi).mpr (hEigBound j).2) (sq_nonneg _))
      _ = _ := by rw [← Finset.mul_sum,← hnorm,b.repr.norm_map]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hhi (norm_nonneg x))).mp hs

end GeneralizedBulk.Covariance
