import GeneralizedBulk.Analysis.CappedTail

/-!
# Tail recursion from a reversible concentration obstruction

The recursion is derived by partitioning the forward large-height event.
Rejected proposals are kept as an additive error, as is escape from the
common graph event. Consequently neither error is integrated above a cap.
-/
noncomputable section
open MeasureTheory
open scoped Classical
namespace GeneralizedBulk.Analysis

def goodTail {S : Type*} (good : Set S) (T : S → ℝ) (t : ℝ) : Set S :=
  {s | s ∈ good ∧ t < T s}

/-- A reversible obstruction forces a forward or reversed concentration
failure. The four terms are retained separately before applying estimates. -/
theorem goodTail_le_rejection_failure_reverse
    {S : Type*} [MeasurableSpace S] (P : Measure S) [IsProbabilityMeasure P]
    (tau : S → S) (htau : MeasurePreserving tau P P)
    (good accepted failure : Set S) (hgood : MeasurableSet good)
    (hfailure : MeasurableSet failure) (T : S → ℝ) (hT : Measurable T)
    (A T0 t : ℝ) (ht : T0 ≤ t)
    (hheight : ∀ s, T s - A ≤ T (tau s))
    (hobstruction : ∀ s ∈ accepted, T0 ≤ T s → s ∈ failure ∨ tau s ∈ failure) :
    P.real (goodTail good T t) ≤ P.real acceptedᶜ +
      P.real (goodTail good T t ∩ failure) + P.real goodᶜ +
        P.real (goodTail good T (t - A) ∩ failure) := by
  have hsubset : goodTail good T t ⊆
      ((acceptedᶜ ∪ (goodTail good T t ∩ failure)) ∪ tau ⁻¹' goodᶜ) ∪
        tau ⁻¹' (goodTail good T (t - A) ∩ failure) := by
    intro s hs
    by_cases ha : s ∈ accepted
    · by_cases hf : s ∈ failure
      · exact Or.inl (Or.inl (Or.inr ⟨hs,hf⟩))
      · by_cases hg : tau s ∈ good
        · have hr := (hobstruction s ha (ht.trans hs.2.le)).resolve_left hf
          exact Or.inr ⟨⟨hg, by linarith [hheight s, hs.2]⟩, hr⟩
        · exact Or.inl (Or.inr hg)
    · exact Or.inl (Or.inl (Or.inl ha))
  have htail : MeasurableSet (goodTail good T (t - A) ∩ failure) :=
    (hgood.inter (measurableSet_lt measurable_const hT)).inter hfailure
  calc
    _ ≤ P.real (((acceptedᶜ ∪ (goodTail good T t ∩ failure)) ∪ tau ⁻¹' goodᶜ) ∪
        tau ⁻¹' (goodTail good T (t - A) ∩ failure)) := measureReal_mono hsubset
    _ ≤ ((P.real acceptedᶜ + P.real (goodTail good T t ∩ failure)) +
      P.real (tau ⁻¹' goodᶜ)) + P.real (tau ⁻¹' (goodTail good T (t - A) ∩ failure)) := by
      exact (measureReal_union_le _ _).trans (add_le_add_right
        ((measureReal_union_le _ _).trans (add_le_add_right (measureReal_union_le _ _) _)) _)
    _ = _ := by
      rw [htau.measureReal_preimage hgood.compl.nullMeasurableSet,
        htau.measureReal_preimage htail.nullMeasurableSet]

/-- Conditional second-moment failure bounds, applied in both directions,
give the genuine scalar tail recursion. Rejection is an additive error. -/
theorem goodTail_recursion
    {S : Type*} [MeasurableSpace S] (P : Measure S) [IsProbabilityMeasure P]
    (tau : S → S) (htau : MeasurePreserving tau P P)
    (good accepted failure : Set S) (hgood : MeasurableSet good)
    (hfailure : MeasurableSet failure) (T : S → ℝ) (hT : Measurable T)
    (A T0 C t : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (ht : 0 < t)
    (hthreshold : T0 + A ≤ t) (hshift : 2 * A ≤ t)
    (hheight : ∀ s, T s - A ≤ T (tau s))
    (hobstruction : ∀ s ∈ accepted, T0 ≤ T s → s ∈ failure ∨ tau s ∈ failure)
    (hfail : ∀ u : ℝ, T0 ≤ u →
      P.real (goodTail good T u ∩ failure) ≤ (C / u) * P.real (goodTail good T u)) :
    P.real (goodTail good T t) ≤
      (3 * C / t) * P.real (goodTail good T (t - A)) + P.real acceptedᶜ + P.real goodᶜ := by
  have hta : 0 < t - A := by linarith
  have hmono : P.real (goodTail good T t) ≤ P.real (goodTail good T (t - A)) :=
    measureReal_mono (fun s hs => ⟨hs.1, by linarith [hs.2]⟩)
  have hfwd := (hfail t (by linarith)).trans
    (mul_le_mul_of_nonneg_left hmono (div_nonneg hC ht.le))
  have hrev := hfail (t - A) (by linarith)
  have hratio : C / (t - A) ≤ 2 * C / t := by
    rw [div_le_div_iff₀ hta ht]
    nlinarith
  have hrev' := hrev.trans (mul_le_mul_of_nonneg_right hratio measureReal_nonneg)
  have hp := goodTail_le_rejection_failure_reverse P tau htau good accepted failure hgood hfailure T hT
    A T0 t (by linarith) hheight hobstruction
  calc
    _ ≤ P.real acceptedᶜ + (C / t) * P.real (goodTail good T (t - A)) + P.real goodᶜ +
        (2 * C / t) * P.real (goodTail good T (t - A)) := by linarith only [hp, hfwd, hrev']
    _ = _ := by ring

/-- A step exceeding both the rank shift and the eventual contraction
threshold turns the reversible recursion into the geometric recursion used
for capped moments. -/
theorem goodTail_discrete_recursion
    {S : Type*} [MeasurableSpace S] (P : Measure S) [IsProbabilityMeasure P]
    (tau : S → S) (htau : MeasurePreserving tau P P)
    (good accepted failure : Set S) (hgood : MeasurableSet good)
    (hfailure : MeasurableSet failure) (T : S → ℝ) (hT : Measurable T)
    (A T0 C B step : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hB : 0 < B) (hBthreshold : T0 + A ≤ B) (hBshift : 2 * A ≤ B)
    (hBcontract : 6 * C ≤ B) (hstep : A ≤ step) (hstep0 : 0 ≤ step)
    (hheight : ∀ s, T s - A ≤ T (tau s))
    (hobstruction : ∀ s ∈ accepted, T0 ≤ T s → s ∈ failure ∨ tau s ∈ failure)
    (hfail : ∀ u : ℝ, T0 ≤ u →
      P.real (goodTail good T u ∩ failure) ≤ (C / u) * P.real (goodTail good T u))
    (n : ℕ) :
    P.real (goodTail good T (B + step * (n + 1 : ℕ))) ≤
      P.real (goodTail good T (B + step * (n : ℝ))) / 2 + P.real acceptedᶜ + P.real goodᶜ := by
  let t := B + step * (n + 1 : ℕ)
  have hBt : B ≤ t := le_add_of_nonneg_right (mul_nonneg hstep0 (Nat.cast_nonneg _))
  have ht : 0 < t := hB.trans_le hBt
  have hp := goodTail_recursion P tau htau good accepted failure hgood hfailure T hT
    A T0 C t hA hC ht (hBthreshold.trans hBt) (hBshift.trans hBt) hheight hobstruction hfail
  have hmono : P.real (goodTail good T (t - A)) ≤ P.real (goodTail good T (B + step * (n : ℝ))) := by
    exact measureReal_mono (by
      intro s hs
      refine ⟨hs.1, ?_⟩
      have hh := hs.2
      dsimp [t] at hh
      push_cast at hh
      nlinarith)
  have hratio : 3 * C / t ≤ 1 / 2 := by
    rw [div_le_iff₀ ht]
    have hlow : 6 * C ≤ t := hBcontract.trans hBt
    calc
      3 * C = (6 * C) / 2 := by ring
      _ ≤ t / 2 := div_le_div_of_nonneg_right hlow (by norm_num)
      _ = (1 / 2) * t := by ring
  have hmul := mul_le_mul hratio hmono measureReal_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
  calc
    _ ≤ (3 * C / t) * P.real (goodTail good T (t - A)) + P.real acceptedᶜ + P.real goodᶜ := hp
    _ ≤ _ := by nlinarith

/-- The scalar height above a fixed threshold, restricted to the common
model event. It is nonnegative and has exactly the shifted good-event tails. -/
def goodExcess {S : Type*} (good : Set S) (T : S → ℝ) (B : ℝ) (s : S) : ℝ :=
  if s ∈ good then max 0 (T s - B) else 0

theorem measurable_goodExcess {S : Type*} [MeasurableSpace S]
    (good : Set S) (T : S → ℝ) (B : ℝ) (hgood : MeasurableSet good) (hT : Measurable T) :
    Measurable (goodExcess good T B) :=
  Measurable.ite hgood (measurable_const.max (hT.sub_const B)) measurable_const

theorem goodExcess_nonneg {S : Type*} (good : Set S) (T : S → ℝ) (B : ℝ) (s : S) :
    0 ≤ goodExcess good T B s := by
  dsimp [goodExcess]
  split_ifs
  · exact le_max_left _ _
  · exact le_refl _

theorem goodExcess_tail_eq {S : Type*} (good : Set S) (T : S → ℝ) (B r : ℝ) (hr : 0 ≤ r) :
    {s | r < goodExcess good T B s} = goodTail good T (B + r) := by
  ext s
  by_cases hs : s ∈ good
  · simp only [goodExcess, hs, ↓reduceIte, lt_max_iff, goodTail, Set.mem_setOf_eq,
      true_and]
    constructor
    · rintro (hzero | hT)
      · exact False.elim ((not_lt_of_ge hr) hzero)
      · linarith
    · intro h
      exact Or.inr (by linarith)
  · simp only [goodExcess, hs, ↓reduceIte, goodTail, Set.mem_setOf_eq, false_and,
      iff_false, not_lt]
    exact hr

/-- The complete reversible argument yields every capped moment of the good
scalar excess. Both finite-size errors remain multiplied by the finite cap;
no uncapped moment of the finite model is presumed. -/
theorem integral_capped_goodExcess_pow_le
    {S : Type*} [MeasurableSpace S] (P : Measure S) [IsProbabilityMeasure P]
    (tau : S → S) (htau : MeasurePreserving tau P P)
    (good accepted failure : Set S) (hgood : MeasurableSet good)
    (hfailure : MeasurableSet failure) (T : S → ℝ) (hT : Measurable T)
    (A T0 C B step : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hB : 0 < B) (hBthreshold : T0 + A ≤ B) (hBshift : 2 * A ≤ B)
    (hBcontract : 6 * C ≤ B) (hstep : A ≤ step) (hstep0 : 0 < step)
    (hheight : ∀ s, T s - A ≤ T (tau s))
    (hobstruction : ∀ s ∈ accepted, T0 ≤ T s → s ∈ failure ∨ tau s ∈ failure)
    (hfail : ∀ u : ℝ, T0 ≤ u →
      P.real (goodTail good T u ∩ failure) ≤ (C / u) * P.real (goodTail good T u))
    (m q : ℕ) :
    (∫ s, min (goodExcess good T B s) (step * (m : ℝ)) ^ q ∂P) ≤
      step ^ q * (geometricMomentConstant q +
        2 * (P.real acceptedᶜ + P.real goodᶜ) * (m : ℝ) * ((m + 1 : ℕ) : ℝ) ^ q) := by
  apply integral_capped_height_pow_le_of_recursion P (goodExcess good T B)
    (measurable_goodExcess good T B hgood hT) (goodExcess_nonneg good T B) step
    (P.real acceptedᶜ + P.real goodᶜ) hstep0 (add_nonneg measureReal_nonneg measureReal_nonneg) m q
  intro n hn
  rw [goodExcess_tail_eq good T B _ (by positivity), goodExcess_tail_eq good T B _ (by positivity)]
  have hp := goodTail_discrete_recursion P tau htau good accepted failure hgood hfailure T hT
    A T0 C B step hA hC hB hBthreshold hBshift hBcontract hstep hstep0.le hheight hobstruction hfail n
  simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hp

end GeneralizedBulk.Analysis
