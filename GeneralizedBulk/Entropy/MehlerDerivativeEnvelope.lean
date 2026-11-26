import GeneralizedBulk.Entropy.MehlerEnvelope

/-! Uniform polynomial estimates for the three logarithmic kernel derivatives. -/
noncomputable section
namespace GeneralizedBulk.Entropy.Mehler

variable (dim cross energy a : ℝ) (hdim : 0 ≤ dim) (henergy : 0 ≤ energy)
variable (ha : 0 ≤ a) (ha1 : a ≤ 1) (hden : 1 / 2 ≤ 1 - a ^ 2)

include hdim henergy ha ha1 hden in
theorem logKernelD1_abs_bound :
    |logKernelD1 dim cross energy a| ≤ 2 * dim + 8 * |cross| + 4 * a * energy := by
  have ha2 : a ^ 2 ≤ 1 := pow_le_one₀ ha ha1
  have hcoef : 0 ≤ 1 + a ^ 2 := by positivity
  have hnum : |(1 + a ^ 2) * cross - a * energy| ≤ 2 * |cross| + a * energy := by
    calc
      _ ≤ |(1 + a ^ 2) * cross| + |a * energy| := abs_sub _ _
      _ = (1 + a ^ 2) * |cross| + a * energy := by
        rw [abs_mul, abs_mul, abs_of_nonneg hcoef, abs_of_nonneg ha, abs_of_nonneg henergy]
      _ ≤ _ := by nlinarith [abs_nonneg cross]
  calc
    _ ≤ |dim * a / (1 - a ^ 2)| +
        |((1 + a ^ 2) * cross - a * energy) / (1 - a ^ 2) ^ 2| := abs_add _ _
    _ ≤ 2 * |dim * a| + 4 * |(1 + a ^ 2) * cross - a * energy| := by
      gcongr
      · convert quotient_abs_le (dim * a) (1 - a ^ 2) hden 1 using 1 <;> norm_num
      · convert quotient_abs_le ((1 + a ^ 2) * cross - a * energy) (1 - a ^ 2) hden 2 using 1 <;> norm_num
    _ ≤ _ := by
      rw [abs_mul, abs_of_nonneg hdim, abs_of_nonneg ha]
      nlinarith

include hdim henergy ha ha1 hden in
theorem logKernelD2_abs_bound :
    |logKernelD2 dim cross energy a| ≤ 8 * dim + 64 * |cross| + 32 * energy := by
  have ha2 : a ^ 2 ≤ 1 := pow_le_one₀ ha ha1
  have ha3 : a ^ 3 ≤ 1 := pow_le_one₀ ha ha1
  have hnum : |(6 * a + 2 * a ^ 3) * cross - (1 + 3 * a ^ 2) * energy| ≤
      8 * |cross| + 4 * energy := by
    calc
      _ ≤ |(6 * a + 2 * a ^ 3) * cross| + |(1 + 3 * a ^ 2) * energy| := abs_sub _ _
      _ = (6 * a + 2 * a ^ 3) * |cross| + (1 + 3 * a ^ 2) * energy := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 6 * a + 2 * a ^ 3),
          abs_of_nonneg (by positivity : 0 ≤ 1 + 3 * a ^ 2), abs_of_nonneg henergy]
      _ ≤ _ := by
        have h1 := mul_le_mul_of_nonneg_right (show 6 * a + 2 * a ^ 3 ≤ 8 by linarith) (abs_nonneg cross)
        have h2 := mul_le_mul_of_nonneg_right (show 1 + 3 * a ^ 2 ≤ 4 by linarith) henergy
        linarith
  calc
    _ ≤ |dim * (1 + a ^ 2) / (1 - a ^ 2) ^ 2| +
      |((6 * a + 2 * a ^ 3) * cross - (1 + 3 * a ^ 2) * energy) / (1 - a ^ 2) ^ 3| := abs_add _ _
    _ ≤ 4 * |dim * (1 + a ^ 2)| +
      8 * |(6 * a + 2 * a ^ 3) * cross - (1 + 3 * a ^ 2) * energy| := by
      gcongr
      · convert quotient_abs_le (dim * (1 + a ^ 2)) (1 - a ^ 2) hden 2 using 1 <;> norm_num
      · convert quotient_abs_le ((6 * a + 2 * a ^ 3) * cross - (1 + 3 * a ^ 2) * energy) (1 - a ^ 2) hden 3 using 1 <;> norm_num
    _ ≤ _ := by
      rw [abs_mul, abs_of_nonneg hdim, abs_of_nonneg (by positivity : 0 ≤ 1 + a ^ 2)]
      nlinarith

include hdim henergy ha ha1 hden in
theorem logKernelD3_abs_bound :
    |logKernelD3 dim cross energy a| ≤ 64 * dim + 768 * |cross| + 384 * energy := by
  have ha2 : a ^ 2 ≤ 1 := pow_le_one₀ ha ha1
  have ha3 : a ^ 3 ≤ 1 := pow_le_one₀ ha ha1
  have ha4 : a ^ 4 ≤ 1 := pow_le_one₀ ha ha1
  have hnum : |(6 + 36 * a ^ 2 + 6 * a ^ 4) * cross - (12 * a + 12 * a ^ 3) * energy| ≤
      48 * |cross| + 24 * energy := by
    calc
      _ ≤ |(6 + 36 * a ^ 2 + 6 * a ^ 4) * cross| + |(12 * a + 12 * a ^ 3) * energy| := abs_sub _ _
      _ = (6 + 36 * a ^ 2 + 6 * a ^ 4) * |cross| + (12 * a + 12 * a ^ 3) * energy := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 6 + 36 * a ^ 2 + 6 * a ^ 4),
          abs_of_nonneg (by positivity : 0 ≤ 12 * a + 12 * a ^ 3), abs_of_nonneg henergy]
      _ ≤ _ := by
        have h1 := mul_le_mul_of_nonneg_right (show 6 + 36 * a ^ 2 + 6 * a ^ 4 ≤ 48 by linarith) (abs_nonneg cross)
        have h2 := mul_le_mul_of_nonneg_right (show 12 * a + 12 * a ^ 3 ≤ 24 by linarith) henergy
        linarith
  calc
    _ ≤ |dim * (6 * a + 2 * a ^ 3) / (1 - a ^ 2) ^ 3| +
      |((6 + 36 * a ^ 2 + 6 * a ^ 4) * cross - (12 * a + 12 * a ^ 3) * energy) / (1 - a ^ 2) ^ 4| := abs_add _ _
    _ ≤ 8 * |dim * (6 * a + 2 * a ^ 3)| +
      16 * |(6 + 36 * a ^ 2 + 6 * a ^ 4) * cross - (12 * a + 12 * a ^ 3) * energy| := by
      gcongr
      · convert quotient_abs_le (dim * (6 * a + 2 * a ^ 3)) (1 - a ^ 2) hden 3 using 1 <;> norm_num
      · convert quotient_abs_le ((6 + 36 * a ^ 2 + 6 * a ^ 4) * cross - (12 * a + 12 * a ^ 3) * energy) (1 - a ^ 2) hden 4 using 1 <;> norm_num
    _ ≤ _ := by
      rw [abs_mul, abs_of_nonneg hdim, abs_of_nonneg (by positivity : 0 ≤ 6 * a + 2 * a ^ 3)]
      have hh := mul_le_mul_of_nonneg_left (show 6 * a + 2 * a ^ 3 ≤ 8 by linarith) hdim
      linarith

end GeneralizedBulk.Entropy.Mehler
