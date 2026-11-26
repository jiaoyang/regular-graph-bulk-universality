import GeneralizedBulk.Entropy.MehlerSmoothingEstimate
import GeneralizedBulk.Entropy.EntropyTaylor

/-! The genuine smoothed density has a proved cubic L³ error and an
integrable quadratic entropy expansion. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace GeneralizedBulk.Entropy.Mehler
open GeneralizedBulk.Entropy.Hermite
variable {I : Type*} [Fintype I]

def smoothingPrefactor (dim : ℝ) : ℝ :=
  5 * (2048 * (1 + dim)) ^ 3 * Real.exp dim

theorem smoothingEnvelope_factorization (dim B : ℝ) (z : I → ℝ) :
    smoothingEnvelope dim B z = smoothingPrefactor dim * (1 + B ^ 2) ^ 3 *
      (Real.exp (coordinateL1 z) * (1 + coordinateL1 z ^ 2) ^ 3) := by
  unfold smoothingEnvelope derivativeEnvelope smoothingPrefactor
  rw [Real.exp_add]
  ring

theorem smoothingEnvelope_power_integrable (dim B : ℝ) (p : ℕ) :
    Integrable (fun z : I → ℝ => smoothingEnvelope dim B z ^ p) (standardGaussian I) := by
  have hi := (integrable_polynomial_exp_coordinateL1 (I := I) (p : ℝ) (3 * p)).const_mul
    (smoothingPrefactor dim ^ p * (1 + B ^ 2) ^ (3 * p))
  convert hi using 1
  funext z
  rw [smoothingEnvelope_factorization]
  simp only [mul_pow, ← pow_mul, ← Real.exp_nat_mul]

variable {S : Type*} [Fintype S] [DecidableEq I]
variable (weight : S → ℝ) (signal : S → I → ℝ)
variable (hweight : ∀ s, 0 ≤ weight s) (hnorm : ∑ s, weight s = 1)
variable (hmean : ∀ i, ∑ s, weight s * signal s i = 0)
variable (hcov : ∀ i j, ∑ s, weight s * signal s i * signal s j = if i = j then 1 else 0)
variable (B a : ℝ) (hB : 0 ≤ B) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2)
variable (hsmall : a * B ≤ 1 / 2) (hsignal : ∀ s, coordinateL1 (signal s) ≤ B)

include hweight hnorm hmean hcov hB ha ha1 hsmall hsignal in
theorem finiteMixture_centered_abs_power_integrable (p : ℕ) :
    Integrable (fun z => |finiteMixtureKernel weight signal a z - 1| ^ p) (standardGaussian I) := by
  have hmajor := (smoothingEnvelope_power_integrable (I := I) (Fintype.card I) B p).mul_const (a ^ (3 * p))
  apply hmajor.mono' ?_ ?_
  · have hcont : Continuous (fun z => |finiteMixtureKernel weight signal a z - 1| ^ p) := by
      unfold finiteMixtureKernel
      exact ((continuous_finset_sum _ (fun s _ => continuous_const.mul (continuous_vectorKernel a (signal s)))).sub continuous_const).abs.pow p
    exact hcont.aestronglyMeasurable
  · filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
    have hh := pow_le_pow_left₀ (abs_nonneg (finiteMixtureKernel weight signal a z - 1))
      (finiteMixtureKernel_sub_one_abs_bound weight signal hweight hnorm hmean hcov B a hB ha ha1 hsmall hsignal z) p
    simpa only [mul_pow, ← pow_mul] using hh

include hweight hnorm hmean hcov hB ha ha1 hsmall hsignal in
theorem finiteMixture_centered_memLp_three :
    MemLp (fun z => finiteMixtureKernel weight signal a z - 1) 3 (standardGaussian I) := by
  apply (integrable_norm_rpow_iff ?_ (by norm_num : (3 : ENNReal) ≠ 0) (by norm_num : (3 : ENNReal) ≠ ⊤)).mp
  · have hh := finiteMixture_centered_abs_power_integrable weight signal hweight hnorm hmean hcov B a hB ha ha1 hsmall hsignal 3
    convert hh using 1
    funext z
    change |finiteMixtureKernel weight signal a z - 1| ^ ((3 : ℕ) : ℝ) =
      |finiteMixtureKernel weight signal a z - 1| ^ (3 : ℕ)
    exact Real.rpow_natCast _ _
  · have hc : Continuous (fun z => finiteMixtureKernel weight signal a z - 1) := by
      unfold finiteMixtureKernel
      exact (continuous_finset_sum _ (fun s _ => continuous_const.mul (continuous_vectorKernel a (signal s)))).sub continuous_const
    exact hc.aestronglyMeasurable

include hnorm ha ha1 in
theorem finiteMixture_centered_integral_zero :
    (∫ z, finiteMixtureKernel weight signal a z - 1 ∂standardGaussian I) = 0 := by
  have hden : 0 < 1 - a ^ 2 := by
    nlinarith [mul_nonneg ha (show 0 ≤ 1 / 2 - a by linarith)]
  rw [integral_sub (integrable_finiteMixtureKernel weight signal a hden) (integrable_const 1),
    integral_finiteMixtureKernel weight signal hnorm a hden]
  simp

include hweight hnorm hmean hcov hB ha ha1 hsmall hsignal in
theorem finiteMixture_entropy_quadratic_bound :
    Integrable (fun z => finiteMixtureKernel weight signal a z * Real.log (finiteMixtureKernel weight signal a z)) (standardGaussian I) ∧
    |relativeEntropy (standardGaussian I) (finiteMixtureKernel weight signal a) -
      (1 / 2 : ℝ) * ∫ z, (finiteMixtureKernel weight signal a z - 1) ^ 2 ∂standardGaussian I| ≤
      4 * a ^ 9 * ∫ z, smoothingEnvelope (Fintype.card I) B z ^ 3 ∂standardGaussian I := by
  have hu := finiteMixture_centered_memLp_three weight signal hweight hnorm hmean hcov B a hB ha ha1 hsmall hsignal
  have ht := relativeEntropy_quadratic_bound_of_memLp_three (standardGaussian I)
    (finiteMixtureKernel weight signal a) hu
    (ae_of_all _ (fun z => finiteMixtureKernel_nonneg weight signal hweight a z))
    (finiteMixture_centered_integral_zero weight signal hnorm a ha ha1)
  refine ⟨ht.1, ht.2.trans ?_⟩
  have hbound : (∫ z, |finiteMixtureKernel weight signal a z - 1| ^ 3 ∂standardGaussian I) ≤
      ∫ z, smoothingEnvelope (Fintype.card I) B z ^ 3 * a ^ 9 ∂standardGaussian I := by
    apply integral_mono_ae
      (finiteMixture_centered_abs_power_integrable weight signal hweight hnorm hmean hcov B a hB ha ha1 hsmall hsignal 3)
      ((smoothingEnvelope_power_integrable (Fintype.card I) B 3).mul_const (a ^ 9))
    filter_upwards [] with z
    have hh := pow_le_pow_left₀ (abs_nonneg (finiteMixtureKernel weight signal a z - 1))
      (finiteMixtureKernel_sub_one_abs_bound weight signal hweight hnorm hmean hcov B a hB ha ha1 hsmall hsignal z) 3
    simpa only [mul_pow, ← pow_mul] using hh
  rw [integral_mul_const] at hbound
  nlinarith

end GeneralizedBulk.Entropy.Mehler
