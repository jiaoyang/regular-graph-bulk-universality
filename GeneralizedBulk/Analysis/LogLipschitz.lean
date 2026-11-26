import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Normed.Group.Basic

/-! Elementary logarithm stability from genuine positive lower bounds. -/
noncomputable section
namespace GeneralizedBulk.Analysis

theorem log_sub_le_abs_sub_div {x y kappa : ℝ} (hk : 0 < kappa) (hx : kappa ≤ x) (hy : kappa ≤ y) :
    Real.log x - Real.log y ≤ |x - y| / kappa := by
  have hxp := hk.trans_le hx
  have hyp := hk.trans_le hy
  rw [← Real.log_div hxp.ne' hyp.ne']
  calc
    Real.log (x / y) ≤ x / y - 1 := Real.log_le_sub_one_of_pos (div_pos hxp hyp)
    _ = (x - y) / y := by field_simp
    _ ≤ |x - y| / y := div_le_div_of_nonneg_right (le_abs_self _) hyp.le
    _ ≤ |x - y| / kappa := div_le_div_of_nonneg_left (abs_nonneg _) hk hy

theorem abs_log_sub_le_abs_sub_div {x y kappa : ℝ} (hk : 0 < kappa) (hx : kappa ≤ x) (hy : kappa ≤ y) :
    |Real.log x - Real.log y| ≤ |x - y| / kappa := by
  have hh := log_sub_le_abs_sub_div hk hx hy
  have ht := log_sub_le_abs_sub_div hk hy hx
  rw [abs_sub_comm y x] at ht
  exact abs_le.mpr ⟨by linarith, hh⟩

theorem abs_log_norm_sub_le {E : Type*} [NormedAddCommGroup E] (a b : E)
    (kappa : ℝ) (hk : 0 < kappa) (ha : kappa ≤ ‖a‖) (hb : kappa ≤ ‖b‖) :
    |Real.log ‖a‖ - Real.log ‖b‖| ≤ ‖a - b‖ / kappa :=
  (abs_log_sub_le_abs_sub_div hk ha hb).trans
    (div_le_div_of_nonneg_right (abs_norm_sub_norm_le a b) hk.le)

end GeneralizedBulk.Analysis
