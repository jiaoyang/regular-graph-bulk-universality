import GeneralizedBulk.Entropy.MehlerLpEstimate

/-! A dimension-only entropy remainder bound for actual normalized finite signals. -/
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace GeneralizedBulk.Entropy.Mehler
open GeneralizedBulk.Entropy.Hermite
variable (I : Type*) [Fintype I]

def gaussianEnvelopeMoment : ℝ :=
  ∫ z : I → ℝ, Real.exp (3 * coordinateL1 z) * (1 + coordinateL1 z ^ 2) ^ 9 ∂standardGaussian I

def smoothingEntropyConstant : ℝ :=
  4 * smoothingPrefactor (Fintype.card I) ^ 3 * (gaussianEnvelopeMoment I + 1)

theorem gaussianEnvelopeMoment_nonneg : 0 ≤ gaussianEnvelopeMoment I :=
  integral_nonneg (fun _ => by positivity)

theorem smoothingEntropyConstant_pos : 0 < smoothingEntropyConstant I := by
  have hm := gaussianEnvelopeMoment_nonneg I
  have hdim : (0 : ℝ) ≤ Fintype.card I := Nat.cast_nonneg _
  unfold smoothingEntropyConstant smoothingPrefactor
  positivity

theorem integral_smoothingEnvelope_cube (B : ℝ) :
    (∫ z : I → ℝ, smoothingEnvelope (Fintype.card I) B z ^ 3 ∂standardGaussian I) =
      smoothingPrefactor (Fintype.card I) ^ 3 * (1 + B ^ 2) ^ 9 * gaussianEnvelopeMoment I := by
  calc
    _ = ∫ z : I → ℝ, (smoothingPrefactor (Fintype.card I) ^ 3 * (1 + B ^ 2) ^ 9) *
        (Real.exp (3 * coordinateL1 z) * (1 + coordinateL1 z ^ 2) ^ 9) ∂standardGaussian I := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [smoothingEnvelope_factorization]
      simp only [mul_pow, ← pow_mul, ← Real.exp_nat_mul]
      norm_num
    _ = _ := integral_const_mul _ _

variable {I} [DecidableEq I] {S : Type*} [Fintype S]

/-- The entire Taylor/L³ input for the actual finite Gaussian mixture is
proved here. The coarser fixed signal polynomial preserves the polynomial
rates in graph size under the external HY delocalization bound. -/
theorem uniform_small_noise_entropy_bound (weight : S → ℝ) (signal : S → I → ℝ)
    (hweight : ∀ s, 0 ≤ weight s) (hnorm : ∑ s, weight s = 1)
    (hmean : ∀ i, ∑ s, weight s * signal s i = 0)
    (hcov : ∀ i j, ∑ s, weight s * signal s i * signal s j = if i = j then 1 else 0)
    (B a : ℝ) (hB : 0 ≤ B) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2)
    (hsmall : a * B ≤ 1 / 2) (hsignal : ∀ s, coordinateL1 (signal s) ≤ B) :
    |relativeEntropy (standardGaussian I) (finiteMixtureKernel weight signal a) -
      (1 / 2 : ℝ) * ∫ z, (finiteMixtureKernel weight signal a z - 1) ^ 2 ∂standardGaussian I| ≤
      smoothingEntropyConstant I * (1 + B ^ 2) ^ 9 * a ^ 9 := by
  have ht := (finiteMixture_entropy_quadratic_bound weight signal hweight hnorm hmean hcov B a hB ha ha1 hsmall hsignal).2
  rw [integral_smoothingEnvelope_cube I B] at ht
  apply ht.trans
  have h := mul_le_mul_of_nonneg_left
    (show gaussianEnvelopeMoment I ≤ gaussianEnvelopeMoment I + 1 by linarith)
    (show 0 ≤ 4 * a ^ 9 * smoothingPrefactor (Fintype.card I) ^ 3 * (1 + B ^ 2) ^ 9 by
      unfold smoothingPrefactor
      positivity)
  convert h using 1 <;> dsimp [smoothingEntropyConstant] <;> ring

end GeneralizedBulk.Entropy.Mehler
