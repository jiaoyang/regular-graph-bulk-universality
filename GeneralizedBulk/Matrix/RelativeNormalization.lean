import GeneralizedBulk.Matrix.RelativeStability
import GeneralizedBulk.Matrix.LocalCovariance

/-! Convert an absolute local covariance error into an explicit relative
square-root coupling, using the actual inverse of the reference factor. -/
noncomputable section
open scoped BigOperators Matrix
namespace GeneralizedBulk.Covariance
variable {I : Type*} [Fintype I] [DecidableEq I]

def normalizedCovariance (M Q : Matrix I I ℝ) : Matrix I I ℝ :=
  M⁻¹ * Q * M⁻¹.transpose

theorem normalizedCovariance_reconstruct (M Q : Matrix I I ℝ) (hM : M.det ≠ 0) :
    M * normalizedCovariance M Q * M.transpose = Q := by
  have hm := Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hM)
  unfold normalizedCovariance
  calc
    _ = (M * M⁻¹) * Q * (M * M⁻¹).transpose := by
      rw [Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hm, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem normalizedCovariance_posDef (M Q : Matrix I I ℝ) (hM : M.det ≠ 0) (hQ : Q.PosDef) :
    (normalizedCovariance M Q).PosDef := by
  have hm := Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hM)
  have mh := Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM)
  have hu : IsUnit M⁻¹ := ⟨⟨M⁻¹, M, mh, hm⟩, rfl⟩
  simpa only [normalizedCovariance, Matrix.conjTranspose_eq_transpose_of_trivial] using
    hQ.mul_mul_conjTranspose_same (Matrix.vecMul_injective_iff_isUnit.mpr hu)

theorem normalizedCovariance_sub_one (M Q : Matrix I I ℝ) (hM : M.det ≠ 0) :
    normalizedCovariance M Q - 1 = M⁻¹ * (Q - M * M.transpose) * M⁻¹.transpose := by
  have hm := Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM)
  have hh : M⁻¹ * (M * M.transpose) * M⁻¹.transpose = 1 := by
    calc
      _ = (M⁻¹ * M) * (M⁻¹ * M).transpose := by
        rw [Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hm, Matrix.transpose_one, Matrix.one_mul]
  rw [Matrix.mul_sub, Matrix.sub_mul, hh]
  rfl

def normalizationLoss (M : Matrix I I ℝ) (e : ℝ) : ℝ :=
  (Fintype.card I : ℝ) * e * (∑ i, ∑ j, M⁻¹.transpose i j ^ 2)

/-- A genuine entrywise covariance local law yields relative quadratic
closeness with an explicit reference-conditioning loss. -/
theorem normalizedCovariance_quadratic_closeness (M Q : Matrix I I ℝ) (hM : M.det ≠ 0)
    (e : ℝ) (he : 0 ≤ e) (hclose : ∀ i j, |(Q - M * M.transpose) i j| ≤ e) (x : I → ℝ) :
    (1 - normalizationLoss M e) * (∑ i, x i ^ 2) ≤ dotProduct x (normalizedCovariance M Q *ᵥ x) ∧
    dotProduct x (normalizedCovariance M Q *ᵥ x) ≤ (1 + normalizationLoss M e) * (∑ i, x i ^ 2) := by
  have hb := abs_quadratic_le_of_entrywise (Q - M * M.transpose) e he hclose (M⁻¹.transpose *ᵥ x)
  have hn := matrix_action_sq_le_frobenius M⁻¹.transpose x
  have hh : |dotProduct x ((normalizedCovariance M Q - 1) *ᵥ x)| ≤
      normalizationLoss M e * ∑ i, x i ^ 2 := by
    rw [normalizedCovariance_sub_one M Q hM, quadratic_compression]
    exact hb.trans (by
      dsimp [normalizationLoss]
      have ht := mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ (Fintype.card I : ℝ) * e)
      simpa only [normalizationLoss, mul_assoc] using ht)
  have hid : dotProduct x ((normalizedCovariance M Q - 1) *ᵥ x) =
      dotProduct x (normalizedCovariance M Q *ᵥ x) - ∑ i, x i ^ 2 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub]
    simp only [dotProduct, pow_two]
  rw [hid] at hh
  constructor <;> nlinarith [(abs_le.mp hh).1, (abs_le.mp hh).2]

end GeneralizedBulk.Covariance
