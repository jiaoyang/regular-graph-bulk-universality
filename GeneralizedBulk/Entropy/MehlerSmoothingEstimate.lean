import GeneralizedBulk.Entropy.MehlerDensity
import GeneralizedBulk.Entropy.MehlerThirdBound
import GeneralizedBulk.Entropy.GaussianEnvelope
import GeneralizedBulk.Analysis.ThirdOrderRemainder

/-! A proved uniform high-noise estimate for actual smoothed finite signals. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace GeneralizedBulk.Entropy.Mehler
open GeneralizedBulk.Entropy.Hermite GeneralizedBulk.Analysis
variable {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S]

def smoothingEnvelope (dim B : ℝ) (z : I → ℝ) : ℝ :=
  5 * derivativeEnvelope dim B (coordinateL1 z) ^ 3 * Real.exp (dim + coordinateL1 z)

theorem smoothingEnvelope_nonneg (dim B : ℝ) (z : I → ℝ) (hdim : 0 ≤ dim) :
    0 ≤ smoothingEnvelope dim B z := by
  unfold smoothingEnvelope derivativeEnvelope
  positivity

theorem finiteMixtureKernelD3_abs_bound (weight : S → ℝ) (signal : S → I → ℝ)
    (hweight : ∀ s, 0 ≤ weight s) (hnorm : ∑ s, weight s = 1)
    (B t : ℝ) (hB : 0 ≤ B) (ht : 0 ≤ t) (ht1 : t ≤ 1 / 2)
    (hsmall : t * B ≤ 1 / 2) (hsignal : ∀ s, coordinateL1 (signal s) ≤ B) (z : I → ℝ) :
    |finiteMixtureKernelD3 weight signal t z| ≤ smoothingEnvelope (Fintype.card I) B z := by
  have hden : 1 / 2 ≤ 1 - t ^ 2 := by
    nlinarith [mul_nonneg ht (show 0 ≤ 1 / 2 - t by linarith)]
  have hbound (s : S) :
      |kernelD3 (Fintype.card I) (∑ i, z i * signal s i)
        (∑ i, ((signal s i) ^ 2 + z i ^ 2)) t| ≤ smoothingEnvelope (Fintype.card I) B z := by
    have hc : |∑ i, z i * signal s i| ≤ B * coordinateL1 z :=
      (abs_cross_le_coordinateL1 (signal s) z).trans
        (mul_le_mul_of_nonneg_right (hsignal s) (coordinateL1_nonneg z))
    have he : (∑ i, ((signal s i) ^ 2 + z i ^ 2)) ≤ B ^ 2 + coordinateL1 z ^ 2 := by
      rw [Finset.sum_add_distrib]
      have hY := sum_sq_le_coordinateL1_sq (signal s)
      have hZ := sum_sq_le_coordinateL1_sq z
      have hsq := (sq_le_sq₀ (coordinateL1_nonneg (signal s)) hB).mpr (hsignal s)
      linarith
    exact kernelD3_abs_uniform_bound _ _ _ t B (coordinateL1 z) (Nat.cast_nonneg _)
      (Finset.sum_nonneg (fun _ _ => by positivity)) ht (by linarith) hden
      (coordinateL1_nonneg z) hc he hsmall
  unfold finiteMixtureKernelD3
  calc
    _ ≤ ∑ s, |weight s * kernelD3 (Fintype.card I) (∑ i, z i * signal s i)
        (∑ i, ((signal s i) ^ 2 + z i ^ 2)) t| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ s, weight s * |kernelD3 (Fintype.card I) (∑ i, z i * signal s i)
        (∑ i, ((signal s i) ^ 2 + z i ^ 2)) t| := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [abs_mul, abs_of_nonneg (hweight s)]
    _ ≤ ∑ s, weight s * smoothingEnvelope (Fintype.card I) B z := by
      apply Finset.sum_le_sum
      intro s hs
      exact mul_le_mul_of_nonneg_left (hbound s) (hweight s)
    _ = _ := by rw [← Finset.sum_mul, hnorm, one_mul]

/-- The actual relative density differs from one by a cubic smoothing error.
The signal-size loss is intentionally polynomial, sufficient when HY bounds
the signal by a polylogarithm of graph size. -/
theorem finiteMixtureKernel_sub_one_abs_bound (weight : S → ℝ) (signal : S → I → ℝ)
    (hweight : ∀ s, 0 ≤ weight s) (hnorm : ∑ s, weight s = 1)
    (hmean : ∀ i, ∑ s, weight s * signal s i = 0)
    (hcov : ∀ i j, ∑ s, weight s * signal s i * signal s j = if i = j then 1 else 0)
    (B a : ℝ) (hB : 0 ≤ B) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2)
    (hsmall : a * B ≤ 1 / 2) (hsignal : ∀ s, coordinateL1 (signal s) ≤ B) (z : I → ℝ) :
    |finiteMixtureKernel weight signal a z - 1| ≤
      smoothingEnvelope (Fintype.card I) B z * a ^ 3 := by
  have hden (t : ℝ) (ht : t ∈ Icc 0 a) : 1 - t ^ 2 ≠ 0 := by
    have hprod := mul_nonneg ht.1 (show 0 ≤ 1 / 2 - t by linarith [ht.2])
    have hp : 0 < 1 - t ^ 2 := by nlinarith
    exact ne_of_gt hp
  have h := third_order_remainder
    (fun t => finiteMixtureKernel weight signal t z)
    (fun t => finiteMixtureKernelD1 weight signal t z)
    (fun t => finiteMixtureKernelD2 weight signal t z)
    (fun t => finiteMixtureKernelD3 weight signal t z)
    a (smoothingEnvelope (Fintype.card I) B z) ha (smoothingEnvelope_nonneg _ _ z (Nat.cast_nonneg _))
    (fun t ht => hasDerivAt_finiteMixtureKernel weight signal t (hden t ht) z)
    (fun t ht => hasDerivAt_finiteMixtureKernelD1 weight signal t (hden t ht) z)
    (fun t ht => hasDerivAt_finiteMixtureKernelD2 weight signal t (hden t ht) z)
    (fun t ht => by
      exact finiteMixtureKernelD3_abs_bound weight signal hweight hnorm B t hB ht.1
        (by linarith [ht.2])
        ((mul_le_mul_of_nonneg_right ht.2 hB).trans hsmall) hsignal z)
    (finiteMixtureKernelD1_zero weight signal hmean z)
    (finiteMixtureKernelD2_zero weight signal hnorm hcov z)
  simpa only [finiteMixtureKernel_zero weight signal hnorm z, Real.norm_eq_abs] using h

end GeneralizedBulk.Entropy.Mehler
