import GeneralizedBulk.Matrix.CovarianceBounds

/-! A covariance close to identity has a concrete square-root factor close to
identity. Reference factors then give a coupling for arbitrary covariances. -/
noncomputable section
open scoped BigOperators Matrix
namespace GeneralizedBulk.Covariance
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem spectralCovariance_sub_one (U : Matrix I I ℝ) (hU : U.transpose * U = 1)
    (q : I → ℝ) : spectralCovariance U q - 1 = spectralCovariance U (fun i => q i - 1) := by
  have hd : Matrix.diagonal (fun i => q i - 1) = Matrix.diagonal q - 1 := by
    ext i j
    by_cases hh : i = j
    · subst j; simp
    · simp [Matrix.diagonal, Matrix.one_apply, hh]
  unfold spectralCovariance
  rw [hd, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.mul_eq_one_comm.mpr hU]

theorem spectralCovariance_action_sq (U : Matrix I I ℝ) (hU : U.transpose * U = 1)
    (q : I → ℝ) (x : I → ℝ) :
    (∑ i, (spectralCovariance U q *ᵥ x) i ^ 2) =
      ∑ i, (q i) ^ 2 * ((U.transpose *ᵥ x) i) ^ 2 := by
  have hh := transpose_mulVec_sq_sum U.transpose hU
    (Matrix.diagonal q *ᵥ (U.transpose *ᵥ x))
  simp only [Matrix.transpose_transpose] at hh
  unfold spectralCovariance
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hh]
  simp only [Matrix.mulVec_diagonal, mul_pow]

theorem abs_sqrt_sub_one_le {x e : ℝ} (hx : 0 ≤ x) (he : 0 ≤ e) (he' : e ≤ 1)
    (hc : |x - 1| ≤ e) : |Real.sqrt x - 1| ≤ e := by
  have hs := Real.sq_sqrt hx
  have hn := Real.sqrt_nonneg x
  obtain ⟨hlo, hhi⟩ := abs_le.mp hc
  have he2 : e ^ 2 ≤ e := by nlinarith [mul_nonneg he (sub_nonneg.mpr he')]
  apply abs_le.mpr
  constructor
  · by_contra hh
    have hh' : Real.sqrt x < 1 - e := by linarith
    have hp := mul_pos (sub_pos.mpr hh') (by linarith : 0 < 1 - e + Real.sqrt x)
    nlinarith
  · nlinarith [sq_nonneg (Real.sqrt x - (1 + e))]

def identityFactor (A : Matrix I I ℝ) (hA : A.PosDef) : Matrix I I ℝ :=
  hA.posSemidef.sqrt

theorem identityFactor_covariance (A : Matrix I I ℝ) (hA : A.PosDef) :
    identityFactor A hA * (identityFactor A hA).transpose = A := by
  have hsym : (identityFactor A hA).transpose = identityFactor A hA := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hA.posSemidef.posSemidef_sqrt.isHermitian
  rw [hsym]
  exact hA.posSemidef.sqrt_mul_self

/-- Relative quadratic error e≤1 controls the literal common-Gaussian
square-root coupling in every direction by e². -/
theorem identityFactor_coupling_bound (A : Matrix I I ℝ) (hA : A.PosDef)
    (e : ℝ) (he : 0 ≤ e) (he' : e ≤ 1)
    (hc : ∀ x : I → ℝ,
      (1 - e) * (∑ i, x i ^ 2) ≤ dotProduct x (A *ᵥ x) ∧
      dotProduct x (A *ᵥ x) ≤ (1 + e) * (∑ i, x i ^ 2)) (x : I → ℝ) :
    (∑ i, ((identityFactor A hA - 1) *ᵥ x) i ^ 2) ≤ e ^ 2 * ∑ i, x i ^ 2 := by
  let U : Matrix I I ℝ := hA.isHermitian.eigenvectorUnitary
  have hU : U.transpose * U = 1 := by
    simpa only [U, star, Matrix.conjTranspose_eq_transpose_of_trivial] using
      unitary.coe_star_mul_self hA.isHermitian.eigenvectorUnitary
  have hS : identityFactor A hA = spectralCovariance U (fun i => Real.sqrt (hA.isHermitian.eigenvalues i)) := by
    simp only [identityFactor, Matrix.PosSemidef.sqrt, spectralCovariance, U,
      Function.comp_apply, Function.comp_def, RCLike.ofReal_real_eq_id, id_eq,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hq (i : I) : |Real.sqrt (hA.isHermitian.eigenvalues i) - 1| ≤ e := by
    apply abs_sqrt_sub_one_le (hA.eigenvalues_pos i).le he he'
    have hh := eigenvalue_bounds_of_quadratic A hA.isHermitian (1 - e) (1 + e) hc i
    exact abs_le.mpr ⟨by linarith [hh.1], by linarith [hh.2]⟩
  rw [hS, spectralCovariance_sub_one U hU, spectralCovariance_action_sq U hU]
  have hn := transpose_mulVec_sq_sum U (Matrix.mul_eq_one_comm.mpr hU) x
  rw [← hn, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) he).mpr (hq i)

/-- The displayed squared-entry sum is an actual uniform energy bound
for every finite matrix. -/
theorem matrix_action_sq_le_frobenius (M : Matrix I I ℝ) (x : I → ℝ) :
    (∑ i, (M *ᵥ x) i ^ 2) ≤ (∑ i, ∑ j, M i j ^ 2) * ∑ j, x j ^ 2 := by
  calc
    _ ≤ ∑ i, (∑ j, M i j ^ 2) * ∑ j, x j ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (M i) x
    _ = _ := by rw [Finset.sum_mul]

def referenceFactor (M A : Matrix I I ℝ) (hA : A.PosDef) : Matrix I I ℝ :=
  M * identityFactor A hA

theorem referenceFactor_covariance (M A : Matrix I I ℝ) (hA : A.PosDef) :
    referenceFactor M A hA * (referenceFactor M A hA).transpose = M * A * M.transpose := by
  unfold referenceFactor
  rw [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (identityFactor A hA) _, identityFactor_covariance]

theorem referenceFactor_coupling_bound (M A : Matrix I I ℝ) (hA : A.PosDef)
    (e : ℝ) (he : 0 ≤ e) (he' : e ≤ 1)
    (hc : ∀ x : I → ℝ,
      (1 - e) * (∑ i, x i ^ 2) ≤ dotProduct x (A *ᵥ x) ∧
      dotProduct x (A *ᵥ x) ≤ (1 + e) * (∑ i, x i ^ 2)) (x : I → ℝ) :
    (∑ i, ((referenceFactor M A hA - M) *ᵥ x) i ^ 2) ≤
      (∑ i, ∑ j, M i j ^ 2) * e ^ 2 * ∑ i, x i ^ 2 := by
  have heq : referenceFactor M A hA - M = M * (identityFactor A hA - 1) := by
    simp only [referenceFactor, Matrix.mul_sub, Matrix.mul_one]
  rw [heq, ← Matrix.mulVec_mulVec]
  calc
    _ ≤ (∑ i, ∑ j, M i j ^ 2) * ∑ i, ((identityFactor A hA - 1) *ᵥ x) i ^ 2 :=
      matrix_action_sq_le_frobenius M _
    _ ≤ (∑ i, ∑ j, M i j ^ 2) * (e ^ 2 * ∑ i, x i ^ 2) :=
      mul_le_mul_of_nonneg_left (identityFactor_coupling_bound A hA e he he' hc x) (by positivity)
    _ = _ := by ring

end GeneralizedBulk.Covariance
