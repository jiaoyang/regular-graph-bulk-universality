import GeneralizedBulk.Entropy.ChannelWhitening
import GeneralizedBulk.Entropy.ColoredChannels
import GeneralizedBulk.Entropy.ScalarCoordinates

/-! Uniform signal-size bounds for whitening throughout the regular-graph bulk. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Channel

theorem bulk_whitening_lower (d : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2) :
    1 / (d : ℝ) ^ 2 ≤ min (1 + (d : ℝ) * c ^ 2)
      ((d : ℝ) * rho c ^ 2 / ((d : ℝ) - 1)) := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hd1 : 0 < (d : ℝ) - 1 := by linarith
  have hdsq : 0 < (d : ℝ) ^ 2 := sq_pos_of_pos hdpos
  have hc := (bulk_rho_lower d hd c hbulk).1
  have hrho := rho_sq c hc
  apply le_min
  · have hi : 1 / (d : ℝ) ^ 2 ≤ 1 := (div_le_iff₀ hdsq).2 (by nlinarith)
    exact hi.trans (by nlinarith [mul_nonneg hdpos.le (sq_nonneg c)])
  · apply (le_div_iff₀ hd1).2
    have hb := (lt_div_iff₀ hdsq).mp hbulk
    have hbm := mul_lt_mul_of_pos_left hb hdpos
    have hp := mul_nonneg (mul_nonneg hdpos.le hd1.le) (show 0 ≤ (d : ℝ) - 3 by linarith)
    have htarget : (d : ℝ) - 1 ≤ (d : ℝ) * rho c ^ 2 * (d : ℝ) ^ 2 := by
      rw [hrho]
      nlinarith
    convert (div_le_iff₀ hdsq).2 htarget using 1 <;> ring

theorem bulk_whitening_inverse_norm_le (d : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2) (y : WhiteStar d) :
    ‖y‖ ≤ (d : ℝ) * ‖physicalLinearMap d (by omega) c (rho c) y‖ := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hlo := (whitening_norm_sq_bounds d (by omega) c (rho c) y).1
  have hδ := mul_le_mul_of_nonneg_right (bulk_whitening_lower d hd c hbulk) (sq_nonneg ‖y‖)
  have hh : ‖y‖ ^ 2 / (d : ℝ) ^ 2 ≤ ‖physicalLinearMap d (by omega) c (rho c) y‖ ^ 2 := by
    convert hδ.trans hlo using 1 <;> ring
  have hs := (div_le_iff₀ (sq_pos_of_pos hdpos)).mp hh
  apply (sq_le_sq₀ (norm_nonneg y) (mul_nonneg hdpos.le (norm_nonneg _))).mp
  nlinarith

theorem physical_norm_le_of_coordinate_bound (d : ℕ) (x : Physical d) (B : ℝ)
    (hB : 0 ≤ B) (hx : ∀ i, |x i| ≤ B) : ‖x‖ ≤ ((d : ℝ) + 1) * B := by
  have hn : ‖x‖ ^ 2 = ∑ i, (x i) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
    simp only [RCLike.inner_apply, conj_trivial]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hsq : ‖x‖ ^ 2 ≤ ((d : ℝ) + 1) * B ^ 2 := by
    rw [hn]
    calc
      _ ≤ ∑ _ : Option (Fin d), B ^ 2 := Finset.sum_le_sum (fun i _ =>
        (sq_abs (x i)).symm ▸ pow_le_pow_left₀ (abs_nonneg _) (hx i) 2)
      _ = _ := by simp
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  apply (sq_le_sq₀ (norm_nonneg x) (by positivity)).mp
  nlinarith [mul_nonneg (mul_nonneg hd0 (show 0 ≤ (d : ℝ) + 1 by positivity)) (sq_nonneg B)]

theorem colored_norm_le_sum (d k : ℕ) (y : ColoredStar d k) : ‖y‖ ≤ ∑ a, ‖y a‖ := by
  apply (sq_le_sq₀ (norm_nonneg y) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))).mp
  rw [colored_norm_sq]
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun a (_ : a ∈ Finset.univ) => norm_nonneg (y a))

end GeneralizedBulk.Entropy.Channel
