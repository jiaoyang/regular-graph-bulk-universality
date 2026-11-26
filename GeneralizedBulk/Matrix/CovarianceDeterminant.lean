import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Exact determinants, covariance factors, and logarithmic stability for
finite positive definite covariances. -/
noncomputable section
open scoped BigOperators Matrix
namespace GeneralizedBulk.Covariance
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A real orthogonal spectral covariance, using the displayed eigenbasis. -/
def spectralCovariance (U : Matrix I I ℝ) (q : I → ℝ) : Matrix I I ℝ :=
  U * Matrix.diagonal q * U.transpose

def spectralFactor (U : Matrix I I ℝ) (q : I → ℝ) : Matrix I I ℝ :=
  U * Matrix.diagonal (fun i => Real.sqrt (q i))

theorem spectralFactor_covariance (U : Matrix I I ℝ) (q : I → ℝ) (hq : ∀ i, 0 ≤ q i) :
    spectralFactor U q * (spectralFactor U q).transpose = spectralCovariance U q := by
  unfold spectralFactor spectralCovariance
  rw [Matrix.transpose_mul, Matrix.diagonal_transpose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Matrix.diagonal _) (Matrix.diagonal _),
    Matrix.diagonal_mul_diagonal]
  simp only [← sq, Real.sq_sqrt (hq _)]

theorem spectralCovariance_det (U : Matrix I I ℝ) (hU : U.transpose * U = 1) (q : I → ℝ) :
    (spectralCovariance U q).det = ∏ i, q i := by
  have hd : U.det * U.det = 1 := by
    simpa only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] using congrArg Matrix.det hU
  simp only [spectralCovariance, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
  calc
    U.det * (∏ i, q i) * U.det = (U.det * U.det) * ∏ i, q i := by ring
    _ = _ := by rw [hd, one_mul]

theorem spectralCovariance_posDef (U : Matrix I I ℝ) (hU : U.transpose * U = 1)
    (q : I → ℝ) (hq : ∀ i, 0 < q i) : (spectralCovariance U q).PosDef := by
  have hunit : IsUnit U := by
    exact ⟨⟨U, U.transpose, Matrix.mul_eq_one_comm.mpr hU, hU⟩, rfl⟩
  have hinj := Matrix.vecMul_injective_iff_isUnit.mpr hunit
  simpa only [spectralCovariance, Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Matrix.PosDef.diagonal hq).mul_mul_conjTranspose_same hinj

theorem spectralCovariance_logdet (U : Matrix I I ℝ) (hU : U.transpose * U = 1)
    (q : I → ℝ) (hq : ∀ i, 0 < q i) :
    Real.log (spectralCovariance U q).det = ∑ i, Real.log (q i) := by
  rw [spectralCovariance_det U hU]
  exact Real.log_prod _ _ (fun i _ => (hq i).ne')

theorem posDef_logdet (A : Matrix I I ℝ) (hA : A.PosDef) :
    Real.log A.det = ∑ i, Real.log (hA.isHermitian.eigenvalues i) := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues]
  exact Real.log_prod _ _ (fun i _ => (hA.eigenvalues_pos i).ne')

/-- A half-unit relative error controls the logarithm linearly. -/
theorem abs_log_le_twice_sub_one {x e : ℝ} (he : 0 ≤ e) (he' : e ≤ 1 / 2)
    (hx : |x - 1| ≤ e) : |Real.log x| ≤ 2 * e := by
  have hlo : 1 - e ≤ x := by linarith [(abs_le.mp hx).1]
  have hhi : x ≤ 1 + e := by linarith [(abs_le.mp hx).2]
  have hpos : 0 < x := by linarith
  have hu := Real.log_le_sub_one_of_pos hpos
  have hl := Real.one_sub_inv_le_log_of_pos hpos
  have hinv : x⁻¹ ≤ 1 + 2 * e := by
    rw [inv_eq_one_div, div_le_iff₀ hpos]
    have hh := mul_le_mul_of_nonneg_left hlo (by positivity : 0 ≤ 1 + 2 * e)
    nlinarith [mul_nonneg he (sub_nonneg.mpr he')]
  apply abs_le.mpr
  constructor <;> linarith

/-- Log-determinant stability from bounds on the genuine eigenvalues. -/
theorem logdet_stability_of_eigenvalues (A : Matrix I I ℝ) (hA : A.PosDef)
    (e : ℝ) (he : 0 ≤ e) (he' : e ≤ 1 / 2)
    (hclose : ∀ i, |hA.isHermitian.eigenvalues i - 1| ≤ e) :
    |Real.log A.det| ≤ 2 * Fintype.card I * e := by
  rw [posDef_logdet A hA]
  calc
    |∑ i, Real.log (hA.isHermitian.eigenvalues i)| ≤
        ∑ i, |Real.log (hA.isHermitian.eigenvalues i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : I, 2 * e := Finset.sum_le_sum (fun i _ => abs_log_le_twice_sub_one he he' (hclose i))
    _ = _ := by simp; ring

/-- Every genuine positive definite covariance has an actual real square-root
factor. The factor is constructed by the finite spectral theorem. -/
theorem exists_nonsingular_covariance_factor (A : Matrix I I ℝ) (hA : A.PosDef) :
    ∃ M : Matrix I I ℝ, M * M.transpose = A ∧ M.det ≠ 0 := by
  let M := hA.posSemidef.sqrt
  have hsym : M.transpose = M := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hA.posSemidef.posSemidef_sqrt.isHermitian
  have hMM : M * M.transpose = A := by
    rw [hsym]
    exact hA.posSemidef.sqrt_mul_self
  refine ⟨M, hMM, ?_⟩
  have hh := hA.det_pos
  rw [← hMM, Matrix.det_mul, Matrix.det_transpose] at hh
  intro hz
  simp only [hz, zero_mul, lt_self_iff_false] at hh

/-- A quadratic-form bound implies the same bound on every genuine
Hermitian eigenvalue. -/
theorem eigenvalue_bounds_of_quadratic (A : Matrix I I ℝ) (hA : A.IsHermitian)
    (lo hi : ℝ)
    (hbound : ∀ x : I → ℝ,
      lo * (∑ i, x i ^ 2) ≤ dotProduct x (A *ᵥ x) ∧
      dotProduct x (A *ᵥ x) ≤ hi * (∑ i, x i ^ 2)) (j : I) :
    lo ≤ hA.eigenvalues j ∧ hA.eigenvalues j ≤ hi := by
  let v := hA.eigenvectorBasis j
  have hn : ∑ i, (v i) ^ 2 = 1 := by
    have hh := PiLp.norm_sq_eq_of_L2 (fun _ : I => ℝ) v
    simpa only [v, hA.eigenvectorBasis.norm_eq_one j, one_pow, Real.norm_eq_abs,
      sq_abs] using hh.symm
  have he : hA.eigenvalues j = dotProduct (fun i => v i) (A *ᵥ (fun i => v i)) := by
    simpa only [v, RCLike.re_to_real, star_trivial] using hA.eigenvalues_eq j
  have hb := hbound (fun i => v i)
  simpa only [hn, mul_one, ← he] using hb

/-- Relative quadratic-form closeness to identity gives a dimension-explicit
log-determinant error. -/
theorem logdet_stability_of_quadratic (A : Matrix I I ℝ) (hA : A.PosDef)
    (e : ℝ) (he : 0 ≤ e) (he' : e ≤ 1 / 2)
    (hclose : ∀ x : I → ℝ,
      (1 - e) * (∑ i, x i ^ 2) ≤ dotProduct x (A *ᵥ x) ∧
      dotProduct x (A *ᵥ x) ≤ (1 + e) * (∑ i, x i ^ 2)) :
    |Real.log A.det| ≤ 2 * Fintype.card I * e := by
  apply logdet_stability_of_eigenvalues A hA e he he'
  intro i
  have hh := eigenvalue_bounds_of_quadratic A hA.isHermitian (1 - e) (1 + e) hclose i
  exact abs_le.mpr ⟨by linarith [hh.1], by linarith [hh.2]⟩

end GeneralizedBulk.Covariance
