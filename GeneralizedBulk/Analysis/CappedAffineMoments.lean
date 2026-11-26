import GeneralizedBulk.Analysis.ReversibleTail
import GeneralizedBulk.Analysis.CappedMomentTransfer

/-! Capped scalar moments from the reversible good-excess moment estimate. -/
noncomputable section
open MeasureTheory
namespace GeneralizedBulk.Analysis

theorem integrable_nonnegative_cap_pow {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ) (hf : Measurable f)
    (hnonneg : ∀ x, 0 ≤ f x) (K : ℝ) (hK : 0 ≤ K) (q : ℕ) :
    Integrable (fun x => min (f x) K ^ q) P := by
  apply (integrable_const (K ^ q)).mono' (((hf.min measurable_const).pow_const q).aestronglyMeasurable)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (le_min (hnonneg x) hK) q)]
  exact pow_le_pow_left₀ (le_min (hnonneg x) hK) (min_le_right _ _) q

/-- The finite affine scalar normalization changes the cap and constants,
while keeping the genuine finite good-excess moment on the right. -/
theorem integral_good_capped_affine_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (good : Set Ω) (hgood : MeasurableSet good) (T f : Ω → ℝ)
    (hT : Measurable T) (hf : Measurable f) (hfnonneg : ∀ x, 0 ≤ f x)
    (a b B L : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hbound : ∀ x ∈ good, f x ≤ a + b * T x) (q : ℕ) :
    (∫ x, good.indicator (fun x => min (f x) (a + b * (B + L)) ^ q) x ∂P) ≤
      (2 : ℝ) ^ (q - 1) * ((a + b * B) ^ q + b ^ q *
        (∫ x, min (goodExcess good T B x) L ^ q ∂P)) := by
  let H := goodExcess good T B
  have hH : Measurable H := measurable_goodExcess good T B hgood hT
  have hHnonneg (x) : 0 ≤ H x := goodExcess_nonneg good T B x
  have hpoint (x : Ω) : good.indicator (fun x => min (f x) (a + b * (B + L)) ^ q) x ≤
      (2 : ℝ) ^ (q - 1) * ((a + b * B) ^ q + b ^ q * min (H x) L ^ q) := by
    by_cases hx : x ∈ good
    · rw [Set.indicator_of_mem hx]
      have hTx : T x ≤ B + H x := by
        dsimp [H,goodExcess]
        rw [if_pos hx]
        have hm := le_max_right (0 : ℝ) (T x - B)
        linarith
      have hfx : f x ≤ a + b * (B + H x) :=
        (hbound x hx).trans (add_le_add_left (mul_le_mul_of_nonneg_left hTx hb) a)
      have hclip : min (f x) (a + b * (B + L)) ≤ a + b * B + b * min (H x) L := by
        by_cases hh : H x ≤ L
        · rw [min_eq_left hh]
          exact (min_le_left _ _).trans (by nlinarith only [hfx])
        · rw [min_eq_right (le_of_not_ge hh)]
          convert min_le_right (f x) (a + b * (B + L)) using 1 <;> ring
      have hp := pow_le_pow_left₀ (le_min (hfnonneg x) (by positivity)) hclip q
      have hsum := add_pow_le (show 0 ≤ a + b * B by positivity)
        (mul_nonneg hb (le_min (hHnonneg x) hL)) q
      rw [mul_pow] at hsum
      exact hp.trans hsum
    · rw [Set.indicator_of_not_mem hx]
      have hh : 0 ≤ min (H x) L := le_min (hHnonneg x) hL
      positivity
  have hiF := (integrable_nonnegative_cap_pow P f hf hfnonneg
    (a + b * (B + L)) (by positivity) q).indicator hgood
  have hiH := integrable_nonnegative_cap_pow P H hH hHnonneg L hL q
  have hiR := ((integrable_const ((a + b * B) ^ q)).add (hiH.const_mul (b ^ q))).const_mul
    ((2 : ℝ) ^ (q - 1))
  have hi := integral_mono hiF hiR hpoint
  simp only [Pi.add_apply] at hi
  rw [integral_const_mul, integral_add (integrable_const _) (hiH.const_mul _),
    integral_const_mul, integral_const, measureReal_univ_eq_one, one_smul] at hi
  exact hi

end GeneralizedBulk.Analysis
