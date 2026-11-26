import Mathlib

/-!
# Capped moment bounds from reversible tail recursion

The additive finite-size tail error is retained multiplied by the cap. It is
never integrated over an infinite interval. Integer-valued heights can be
obtained by discretizing a nonnegative resolvent height.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace GeneralizedBulk.Analysis

theorem geometric_tail_of_recursion (F : ℕ → ℝ) (epsilon : ℝ)
    (he : 0 ≤ epsilon) (hzero : F 0 ≤ 1)
    (hstep : ∀ n, F (n + 1) ≤ F n / 2 + epsilon) (n : ℕ) :
    F n ≤ (1 / 2 : ℝ) ^ n + 2 * epsilon := by
  induction n with
  | zero => simp only [pow_zero]; linarith
  | succ n ih =>
    have h := hstep n
    rw [pow_succ]
    linarith

/-- The recursion is required only below the cap. Finite-size estimates
available up to logarithmic height therefore suffice. -/
theorem geometric_tail_of_recursion_upto (F : ℕ → ℝ) (epsilon : ℝ)
    (he : 0 ≤ epsilon) (hzero : F 0 ≤ 1) (m : ℕ)
    (hstep : ∀ n, n < m → F (n + 1) ≤ F n / 2 + epsilon)
    (n : ℕ) (hn : n ≤ m) : F n ≤ (1 / 2 : ℝ) ^ n + 2 * epsilon := by
  induction n with
  | zero => simp only [pow_zero]; linarith
  | succ n ih =>
    have h := hstep n (Nat.lt_of_succ_le hn)
    have hi := ih (Nat.le_of_succ_le hn)
    rw [pow_succ]
    linarith

theorem capped_nat_pow_le (y m q : ℕ) :
    ((min y m : ℕ) : ℝ) ^ q ≤ 1 +
      ∑ k ∈ Finset.range m, if k < y then ((k + 1 : ℕ) : ℝ) ^ q else 0 := by
  classical
  by_cases hz : min y m = 0
  · rw [hz]
    have hs : 0 ≤ ∑ k ∈ Finset.range m,
        if k < y then ((k + 1 : ℕ) : ℝ) ^ q else 0 :=
      Finset.sum_nonneg (fun k _ => by split_ifs <;> positivity)
    cases q <;> simp_all <;> linarith
  · have hp : 0 < min y m := Nat.pos_of_ne_zero hz
    let k := min y m - 1
    have hk : k + 1 = min y m := Nat.sub_add_cancel hp
    have hkm : k < m := by omega
    have hky : k < y := by omega
    have hs := Finset.single_le_sum
      (f := fun k => if k < y then ((k + 1 : ℕ) : ℝ) ^ q else 0)
      (s := Finset.range m) (a := k)
      (fun a _ => by dsimp only; split_ifs <;> positivity) (Finset.mem_range.mpr hkm)
    dsimp only at hs
    rw [if_pos hky, hk] at hs
    linarith

theorem summable_geometric_moment (q : ℕ) :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ q * (1 / 2 : ℝ) ^ n) := by
  have hr : ‖(1 / 2 : ℝ)‖ < 1 := by norm_num
  have hs := summable_pow_mul_geometric_of_norm_lt_one q hr
  have hg := summable_geometric_of_norm_lt_one hr
  apply Summable.of_nonneg_of_le (fun n => by positivity) _
    ((hs.add hg).mul_left ((2 : ℝ) ^ (q - 1)))
  intro n
  have hb := add_pow_le (by positivity : (0 : ℝ) ≤ n) (by norm_num : (0 : ℝ) ≤ 1) q
  have hb' := mul_le_mul_of_nonneg_right hb (by positivity : 0 ≤ (1 / 2 : ℝ) ^ n)
  convert hb' using 1 <;> push_cast <;> ring

def geometricMomentConstant (q : ℕ) : ℝ :=
  1 + ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ q * (1 / 2 : ℝ) ^ n

/-- A genuine integral estimate for the capped random variable, with the
finite-size error retained. No integrability premise on the uncapped height
is required. -/
theorem integral_capped_nat_pow_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℕ) (hY : Measurable Y) (epsilon : ℝ) (he : 0 ≤ epsilon)
    (m q : ℕ)
    (htail : ∀ n, n < m → P.real {ω | n < Y ω} ≤ (1 / 2 : ℝ) ^ n + 2 * epsilon) :
    (∫ ω, ((min (Y ω) m : ℕ) : ℝ) ^ q ∂P) ≤
      geometricMomentConstant q + 2 * epsilon * (m : ℝ) * ((m + 1 : ℕ) : ℝ) ^ q := by
  classical
  have hset (n : ℕ) : MeasurableSet {ω | n < Y ω} :=
    measurableSet_lt measurable_const hY
  let T : ℕ → Ω → ℝ := fun n =>
    Set.indicator {ω | n < Y ω} (fun _ => ((n + 1 : ℕ) : ℝ) ^ q)
  have hi (n : ℕ) : Integrable (T n) P :=
    (integrable_const _).indicator (hset n)
  have hcap : Integrable (fun ω => ((min (Y ω) m : ℕ) : ℝ) ^ q) P := by
    apply (integrable_const ((m : ℝ) ^ q)).mono'
      (((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
        (hY.min measurable_const)).pow_const q).aestronglyMeasurable
    filter_upwards [] with ω
    change ‖((min (Y ω) m : ℕ) : ℝ) ^ q‖ ≤ (m : ℝ) ^ q
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast min_le_right (Y ω) m) q
  calc
    _ ≤ ∫ ω, 1 + ∑ n ∈ Finset.range m, T n ω ∂P :=
      integral_mono hcap ((integrable_const 1).add (integrable_finset_sum _ (fun n _ => hi n)))
        (fun ω => by
          have heq : (∑ n ∈ Finset.range m, T n ω) =
              ∑ n ∈ Finset.range m, if n < Y ω then ((n + 1 : ℕ) : ℝ) ^ q else 0 := by
            apply Finset.sum_congr rfl
            intro n hn
            by_cases h : n < Y ω <;> simp [T, Set.indicator, h]
          rw [heq]
          exact capped_nat_pow_le (Y ω) m q)
    _ = 1 + ∑ n ∈ Finset.range m, ((n + 1 : ℕ) : ℝ) ^ q * P.real {ω | n < Y ω} := by
      rw [integral_add (integrable_const 1) (integrable_finset_sum _ (fun n _ => hi n)),
        integral_finset_sum _ (fun n _ => hi n)]
      simp only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro n hn
      change (∫ ω, (Set.indicator {ω | n < Y ω}
        (fun _ => ((n + 1 : ℕ) : ℝ) ^ q)) ω ∂P) = _
      rw [integral_indicator (hset n), setIntegral_const]
      simp [Measure.real, smul_eq_mul, mul_comm]
    _ ≤ 1 + ∑ n ∈ Finset.range m,
        ((n + 1 : ℕ) : ℝ) ^ q * ((1 / 2 : ℝ) ^ n + 2 * epsilon) := by
      exact add_le_add_left (Finset.sum_le_sum (fun n hn =>
        mul_le_mul_of_nonneg_left (htail n (Finset.mem_range.mp hn)) (by positivity))) 1
    _ ≤ geometricMomentConstant q + 2 * epsilon * (m : ℝ) * ((m + 1 : ℕ) : ℝ) ^ q := by
      simp only [mul_add, Finset.sum_add_distrib]
      have hg := (summable_geometric_moment q).sum_le_tsum (Finset.range m)
        (fun n _ => by positivity)
      have heach (n : ℕ) (hn : n ∈ Finset.range m) :
          ((n + 1 : ℕ) : ℝ) ^ q * (2 * epsilon) ≤
            ((m + 1 : ℕ) : ℝ) ^ q * (2 * epsilon) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply pow_le_pow_left₀ (by positivity) _ q
        exact_mod_cast (show n + 1 ≤ m + 1 by have := Finset.mem_range.mp hn; omega)
      have herr := Finset.sum_le_sum heach
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at herr
      dsimp [geometricMomentConstant]
      nlinarith

/-- Discretizing a real height gives the capped estimate used before a
subsequential limit. The additive error is multiplied only by a finite cap. -/
theorem integral_capped_height_pow_le_of_recursion
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H : Ω → ℝ) (hH : Measurable H) (hH0 : ∀ ω, 0 ≤ H ω)
    (A epsilon : ℝ) (hA : 0 < A) (he : 0 ≤ epsilon)
    (m q : ℕ)
    (hstep : ∀ n : ℕ, n < m → P.real {ω | A * ((n + 1 : ℕ) : ℝ) < H ω} ≤
      P.real {ω | A * (n : ℝ) < H ω} / 2 + epsilon) :
    (∫ ω, min (H ω) (A * (m : ℝ)) ^ q ∂P) ≤
      A ^ q * (geometricMomentConstant q +
        2 * epsilon * (m : ℝ) * ((m + 1 : ℕ) : ℝ) ^ q) := by
  let Y : Ω → ℕ := fun ω => Nat.ceil (H ω / A)
  have hY : Measurable Y := Nat.ceil_mono.measurable.comp (hH.div_const A)
  have hset (n : ℕ) : {ω | n < Y ω} = {ω | A * (n : ℝ) < H ω} := by
    ext ω
    simp only [Y, Nat.lt_ceil]
    exact lt_div_iff₀' hA
  have hz : P.real {ω | 0 < Y ω} ≤ 1 := by
    simpa only [measureReal_univ_eq_one] using
      (measureReal_mono (μ := P) (Set.subset_univ {ω | 0 < Y ω}))
  have ht (n : ℕ) (hn : n < m) :
      P.real {ω | n < Y ω} ≤ (1 / 2 : ℝ) ^ n + 2 * epsilon := by
    exact geometric_tail_of_recursion_upto (fun k => P.real {ω | k < Y ω}) epsilon he hz m
      (fun k hk => by simpa only [hset] using hstep k hk) n hn.le
  have hI := integral_capped_nat_pow_le P Y hY epsilon he m q ht
  have hi : Integrable (fun ω => min (H ω) (A * (m : ℝ)) ^ q) P := by
    apply (integrable_const ((A * (m : ℝ)) ^ q)).mono'
      ((hH.min measurable_const).pow_const q).aestronglyMeasurable
    filter_upwards [] with ω
    change ‖min (H ω) (A * (m : ℝ)) ^ q‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (le_min (hH0 ω) (by positivity)) _)]
    exact pow_le_pow_left₀ (le_min (hH0 ω) (by positivity)) (min_le_right _ _) q
  have hn : Integrable (fun ω => ((min (Y ω) m : ℕ) : ℝ) ^ q) P := by
    apply (integrable_const ((m : ℝ) ^ q)).mono'
      (((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
        (hY.min measurable_const)).pow_const q).aestronglyMeasurable
    filter_upwards [] with ω
    change ‖((min (Y ω) m : ℕ) : ℝ) ^ q‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast min_le_right (Y ω) m) q
  calc
    _ ≤ ∫ ω, A ^ q * ((min (Y ω) m : ℕ) : ℝ) ^ q ∂P := by
      apply integral_mono hi (hn.const_mul _)
      intro ω
      have hb : min (H ω) (A * (m : ℝ)) ≤ A * ((min (Y ω) m : ℕ) : ℝ) := by
        by_cases hy : Y ω ≤ m
        · rw [Nat.min_eq_left hy]
          exact (min_le_left _ _).trans (by
            simpa only [mul_comm] using (div_le_iff₀ hA).mp (Nat.le_ceil (H ω / A)))
        · rw [Nat.min_eq_right (le_of_not_ge hy)]
          exact min_le_right _ _
      simpa only [mul_pow] using pow_le_pow_left₀
        (le_min (hH0 ω) (by positivity)) hb q
    _ = A ^ q * ∫ ω, ((min (Y ω) m : ℕ) : ℝ) ^ q ∂P := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hI (pow_nonneg hA.le _)

end GeneralizedBulk.Analysis
