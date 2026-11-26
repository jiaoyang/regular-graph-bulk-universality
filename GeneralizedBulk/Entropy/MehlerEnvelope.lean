import GeneralizedBulk.Entropy.MehlerKernelCalculus

/-! Uniform envelopes for the actual Mehler kernel at high noise. -/
noncomputable section

namespace GeneralizedBulk.Entropy.Mehler

/-- The denominator estimates are independent of the signal bound. -/
theorem quotient_abs_le (num den : ℝ) (hden : 1 / 2 ≤ den) (power : ℕ) :
    |num / den ^ power| ≤ (2 : ℝ) ^ power * |num| := by
  have hdpos : 0 < den := by linarith
  rw [abs_div, abs_pow, abs_of_pos hdpos, div_le_iff₀ (pow_pos hdpos power)]
  have h := one_le_pow₀ (show (1 : ℝ) ≤ 2 * den by linarith) (n := power)
  rw [mul_pow] at h
  nlinarith [mul_le_mul_of_nonneg_right h (abs_nonneg num)]

/-- On the high-noise scale, the exponential envelope is independent of the
signal size. Here `Y,Z` can be the coordinate ℓ¹ norms. -/
theorem logKernel_le_linear_envelope (dim cross energy a Y Z : ℝ)
    (hdim : 0 ≤ dim) (henergy : 0 ≤ energy) (ha : 0 ≤ a)
    (hden : 1 / 2 ≤ 1 - a ^ 2) (hZ : 0 ≤ Z)
    (hcross : |cross| ≤ Y * Z) (hsmall : a * Y ≤ 1 / 2) :
    logKernel dim cross energy a ≤ dim + Z := by
  have hdpos : 0 < 1 - a ^ 2 := by linarith
  have hinv : (1 - a ^ 2)⁻¹ ≤ 2 := (inv_le_iff_one_le_mul₀ hdpos).2 (by linarith)
  have hlog := Real.one_sub_inv_le_log_of_pos hdpos
  have hneglog : -(Real.log (1 - a ^ 2)) ≤ 1 := by linarith
  have hfirst : -(dim / 2) * Real.log (1 - a ^ 2) ≤ dim := by
    have hh := mul_le_mul_of_nonneg_left hneglog (show 0 ≤ dim / 2 by positivity)
    nlinarith
  have hcross' : cross ≤ Y * Z := (le_abs_self cross).trans hcross
  have hc := mul_le_mul_of_nonneg_left hcross' (show 0 ≤ 2 * a by positivity)
  have hs := mul_le_mul_of_nonneg_right hsmall hZ
  have hd := mul_le_mul_of_nonneg_right hden hZ
  have he := mul_nonneg (sq_nonneg a) henergy
  have hfrac : (2 * a * cross - a ^ 2 * energy) / (2 * (1 - a ^ 2)) ≤ Z := by
    apply (div_le_iff₀ (show 0 < 2 * (1 - a ^ 2) by positivity)).2
    nlinarith
  exact add_le_add hfirst hfrac

theorem kernel_le_linear_envelope (dim cross energy a Y Z : ℝ)
    (hdim : 0 ≤ dim) (henergy : 0 ≤ energy) (ha : 0 ≤ a)
    (hden : 1 / 2 ≤ 1 - a ^ 2) (hZ : 0 ≤ Z)
    (hcross : |cross| ≤ Y * Z) (hsmall : a * Y ≤ 1 / 2) :
    kernel dim cross energy a ≤ Real.exp (dim + Z) :=
  Real.exp_le_exp.mpr (logKernel_le_linear_envelope dim cross energy a Y Z
    hdim henergy ha hden hZ hcross hsmall)

end GeneralizedBulk.Entropy.Mehler
