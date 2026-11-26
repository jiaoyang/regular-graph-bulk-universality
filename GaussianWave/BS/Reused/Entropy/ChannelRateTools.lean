import Mathlib

/-! Elementary polynomial and stretched-exponential estimates used to make
the explicit graph entropy error quantitative. -/
noncomputable section
open Filter Asymptotics
open scoped Topology

namespace GaussianWave.BS.Reused.Entropy.ChannelRates

theorem nat_const_bigO_rpow (c a : ℝ) (ha : 0 ≤ a) :
    (fun _n : ℕ => c) =O[atTop] fun n => (n : ℝ)^a := by
  have h : (fun _n : ℕ => c) =O[atTop] fun _n => (1 : ℝ) := isBigO_const_const c one_ne_zero atTop
  apply h.trans
  apply Eventually.isBigO
  filter_upwards [eventually_ge_atTop 1] with n hn
  simpa only [Real.norm_eq_abs,abs_one] using Real.one_le_rpow (show (1 : ℝ) ≤ n by exact_mod_cast hn) ha

theorem nat_rpow_bigO_mono (a b : ℝ) (hab : a ≤ b) :
    (fun n : ℕ => (n : ℝ)^a) =O[atTop] (fun n => (n : ℝ)^b) := by
  apply Eventually.isBigO
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hab

theorem nat_rpow_mul_bigO {f g : ℕ → ℝ} {a b c : ℝ}
    (hf : f =O[atTop] fun n => (n : ℝ)^a) (hg : g =O[atTop] fun n => (n : ℝ)^b)
    (h : a+b ≤ c) : (fun n => f n*g n) =O[atTop] fun n => (n : ℝ)^c :=
  hf.mul_atTop_rpow_natCast_of_isBigO_rpow a b c hg h

theorem nat_rpow_sqrt_bigO {f : ℕ → ℝ} {a : ℝ}
    (hf : f =O[atTop] fun n => (n : ℝ)^a) :
    (fun n => Real.sqrt (f n)) =O[atTop] fun n => (n : ℝ)^(a/2) := by
  have h := hf.sqrt (Filter.Eventually.of_forall (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) a))
  apply h.congr_right
  intro n
  rw [Real.sqrt_eq_rpow,← Real.rpow_mul (Nat.cast_nonneg n)]
  congr 1
  ring

theorem nat_rpow_pow_bigO {f : ℕ → ℝ} {a : ℝ}
    (hf : f =O[atTop] fun n => (n : ℝ)^a) (k : ℕ) :
    (fun n => f n^k) =O[atTop] fun n => (n : ℝ)^(a*(k : ℝ)) := by
  apply (hf.pow k).congr_right
  intro n
  rw [← Real.rpow_natCast,← Real.rpow_mul (Nat.cast_nonneg n)]

theorem ceil_nat_rpow_bigO (a : ℝ) (ha : 0 ≤ a) :
    (fun n : ℕ => (Nat.ceil ((n : ℝ)^a) : ℝ)) =O[atTop] fun n => (n : ℝ)^a := by
  apply IsBigO.of_bound 2
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnp : 1 ≤ (n : ℝ)^a := Real.one_le_rpow (by exact_mod_cast hn) ha
  have hc := Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg n) a)
  rw [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _),Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) a)]
  linarith

set_option maxHeartbeats 1000000 in
theorem stretched_exp_littleO_nat_rpow (a b s : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (fun n : ℕ => Real.exp (-b*(n : ℝ)^a)) =o[atTop] fun n => (n : ℝ)^s := by
  have h := (isLittleO_exp_neg_mul_rpow_atTop hb (s/a)).comp_tendsto
    ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop)
  apply h.congr_right
  intro n
  simp only [Function.comp_apply]
  rw [← Real.rpow_mul (Nat.cast_nonneg n)]
  congr 1
  field_simp

theorem stretched_exp_eventually_le_nat_rpow (a b s : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∀ᶠ n : ℕ in atTop,Real.exp (-b*(n : ℝ)^a) ≤ (n : ℝ)^s := by
  have h := (stretched_exp_littleO_nat_rpow a b s ha hb).bound (c := 1) (by norm_num)
  simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _),one_mul] using h

theorem nat_rpow_bigO_eventually_le {f : ℕ → ℝ} {a b : ℝ}
    (hf : f =O[atTop] fun n => (n : ℝ)^a) (hab : a < b) :
    ∀ᶠ n in atTop,f n ≤ (n : ℝ)^b := by
  obtain ⟨C,hC,hbound⟩ := hf.exists_pos
  have hg := ((tendsto_rpow_atTop (sub_pos.mpr hab)).comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop C)
  filter_upwards [hbound.bound,hg,eventually_ge_atTop 1] with n hn hg hn1
  have hnp : 0 < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hn1
  calc
    f n ≤ |f n| := le_abs_self _
    _ ≤ C*(n : ℝ)^a := by simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hnp.le _)] using hn
    _ ≤ (n : ℝ)^(b-a)*(n : ℝ)^a := mul_le_mul_of_nonneg_right hg (Real.rpow_nonneg hnp.le _)
    _ = _ := by rw [← Real.rpow_add hnp]; congr 1; ring

end GaussianWave.BS.Reused.Entropy.ChannelRates
