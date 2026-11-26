import GeneralizedBulk.Analysis.AnchoredCompactness

/-!
# Actual anchored subsequences from capped good-event moments

Only one capped anchor moment is needed for tightness. Rare exceptional
events and the cap are kept through the finite estimates; no uncapped
finite-model moment or state-law tightness is assumed.
-/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped Topology ENNReal BigOperators Classical
namespace GeneralizedBulk.Analysis

/-- Every finite real random variable has vanishing tails under a finite measure. -/
theorem real_tail_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (f : Ω → ℝ) (hf : Measurable f) :
    Tendsto (fun m : ℕ => P {x | (m : ℝ) < f x}) atTop (𝓝 0) := by
  let sets := fun m : ℕ => {x | (m : ℝ) < f x}
  have hmono : Antitone sets := by
    intro m n hmn x hx
    exact lt_of_le_of_lt (show (m : ℝ) ≤ (n : ℝ) by exact_mod_cast hmn) hx
  have heq : (⋂ m, sets m) = ∅ := by
    apply Set.eq_empty_iff_forall_not_mem.mpr
    intro x hx
    obtain ⟨m,hm⟩ := exists_nat_gt (f x)
    have hh := Set.mem_iInter.mp hx m
    exact (not_lt_of_gt hm) hh
  have h := tendsto_measure_iInter_atTop (μ := P)
    (fun m => (measurableSet_lt measurable_const hf).nullMeasurableSet)
    hmono ⟨0,measure_ne_top _ _⟩
  rw [heq, measure_empty] at h
  exact h

/-- Eventual uniform tails extend over the finite initial part of a sequence. -/
theorem uniform_real_tails_of_eventual
    {Ω : Type*} [MeasurableSpace Ω] (P : ℕ → Measure Ω)
    [∀ n, IsFiniteMeasure (P n)] (f : ℕ → Ω → ℝ) (hf : ∀ n, Measurable (f n))
    (hasymptotic : ∀ epsilon : ℝ≥0∞, 0 < epsilon → ∃ B : ℝ,
      ∀ᶠ n in atTop, P n {x | B < f n x} ≤ epsilon) :
    ∀ epsilon : ℝ≥0∞, 0 < epsilon → ∃ B : ℝ,
      ∀ n, P n {x | B < f n x} ≤ epsilon := by
  intro epsilon hepsilon
  obtain ⟨B0,hB0⟩ := hasymptotic epsilon hepsilon
  obtain ⟨N,hN⟩ := eventually_atTop.mp hB0
  have hearly (i : Fin N) : ∃ b : ℕ, P i {x | (b : ℝ) < f i x} ≤ epsilon := by
    have h := (tendsto_order.mp (real_tail_tendsto_zero (P i) (f i) (hf i))).2 epsilon hepsilon
    obtain ⟨b,hb⟩ := eventually_atTop.mp h
    exact ⟨b,(hb b le_rfl).le⟩
  choose b hb using hearly
  let B1 : ℝ := ∑ i : Fin N, (b i : ℝ)
  refine ⟨max B0 B1, fun n => ?_⟩
  by_cases hn : N ≤ n
  · have hsub : {x | max B0 B1 < f n x} ⊆ {x | B0 < f n x} :=
      fun x hx => lt_of_le_of_lt (le_max_left B0 B1) hx
    exact (measure_mono hsub).trans (hN n hn)
  · let i : Fin N := ⟨n,lt_of_not_ge hn⟩
    have hi : (b i : ℝ) ≤ max B0 B1 := by
      apply le_trans _ (le_max_right _ _)
      exact Finset.single_le_sum (fun j _ => Nat.cast_nonneg (b j)) (Finset.mem_univ i)
    exact (measure_mono (fun x hx => lt_of_le_of_lt hi hx)).trans (hb i)

/-- A good-event capped first moment controls actual tails, while the rare
bad event is retained additively and disappears only in the limit. -/
theorem uniform_real_tails_of_good_capped_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : ℕ → Measure Ω)
    [∀ n, IsProbabilityMeasure (P n)] (f : ℕ → Ω → ℝ) (hf : ∀ n, Measurable (f n))
    (hnonneg : ∀ n x, 0 ≤ f n x)
    (good : ℕ → Set Ω) (hgood : ∀ n, MeasurableSet (good n))
    (hbad : Tendsto (fun n => (P n).real (good n)ᶜ) atTop (𝓝 0))
    (cap : ℕ → ℝ) (hcap : Tendsto cap atTop atTop)
    (C : ℝ) (hC : 0 ≤ C)
    (hmoment : ∀ᶠ n in atTop, (∫ x, (good n).indicator
      (fun x => min (f n x) (cap n)) x ∂P n) ≤ C) :
    ∀ epsilon : ℝ≥0∞, 0 < epsilon → ∃ B : ℝ,
      ∀ n, P n {x | B < f n x} ≤ epsilon := by
  apply uniform_real_tails_of_eventual P f hf
  intro epsilon hepsilon
  by_cases htop : epsilon = ∞
  · exact ⟨0,Eventually.of_forall (fun n => by simp [htop])⟩
  have hδ : 0 < epsilon.toReal := ENNReal.toReal_pos hepsilon.ne' htop
  obtain ⟨R,hR⟩ := exists_nat_gt (max 0 (2 * C / epsilon.toReal))
  have hRpos : 0 < (R : ℝ) := (le_max_left _ _).trans_lt hR
  have hCR : C / (R : ℝ) ≤ epsilon.toReal / 2 := by
    have hh := (div_lt_iff₀ hδ).mp ((le_max_right _ _).trans_lt hR)
    rw [div_le_div_iff₀ hRpos (by norm_num : (0 : ℝ) < 2)]
    linarith
  refine ⟨R,?_⟩
  filter_upwards [hmoment, hcap.eventually (eventually_ge_atTop (R : ℝ)),
    (tendsto_order.mp hbad).2 (epsilon.toReal / 2) (half_pos hδ)] with n hn hlarge hrare
  let Y := (good n).indicator (fun x => min (f n x) (cap n))
  have hYnonneg (x) : 0 ≤ Y x := by
    apply Set.indicator_nonneg
    intro a ha
    exact le_min (hnonneg n a) (hRpos.le.trans hlarge)
  have hi : Integrable Y (P n) :=
    (integrable_nonnegative_cap (P n) (f n) (hf n) (hnonneg n) (cap n)
      (hRpos.le.trans hlarge)).indicator (hgood n)
  have hMarkov := mul_meas_ge_le_integral_of_nonneg (μ := P n)
    (Eventually.of_forall hYnonneg) hi (R : ℝ)
  have htail : (P n).real {x | (R : ℝ) ≤ Y x} ≤ C / (R : ℝ) := by
    rw [le_div_iff₀ hRpos]
    change (R : ℝ) * (P n).real {x | (R : ℝ) ≤ Y x} ≤ _ at hMarkov
    nlinarith only [hMarkov, hn]
  have hsub : {x | (R : ℝ) < f n x} ⊆ (good n)ᶜ ∪ {x | (R : ℝ) ≤ Y x} := by
    intro x hx
    by_cases hxgood : x ∈ good n
    · right
      dsimp [Y]
      rw [Set.indicator_of_mem hxgood]
      exact le_min hx.le hlarge
    · exact Or.inl hxgood
  have hreal : (P n).real {x | (R : ℝ) < f n x} ≤ epsilon.toReal := by
    calc
      _ ≤ (P n).real ((good n)ᶜ ∪ {x | (R : ℝ) ≤ Y x}) := measureReal_mono hsub
      _ ≤ (P n).real (good n)ᶜ + (P n).real {x | (R : ℝ) ≤ Y x} := measureReal_union_le _ _
      _ ≤ epsilon.toReal := by linarith [htail, hCR]
  calc
    _ = ENNReal.ofReal ((P n).real {x | (R : ℝ) < f n x}) :=
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal epsilon.toReal := ENNReal.ofReal_le_ofReal hreal
    _ = epsilon := ENNReal.ofReal_toReal htop

/-- Capped first anchor moments on high-probability graph events produce a
joint counting/analytic-state subsequence, with no tightness premise. -/
theorem anchored_subsequence_of_good_capped_anchor_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : ℕ → Measure Ω)
    [∀ n, IsProbabilityMeasure (P n)]
    (X : ℕ → Ω → AnchoredCountingState) (hX : ∀ n, Measurable (X n))
    (good : ℕ → Set Ω) (hgood : ∀ n, MeasurableSet (good n))
    (hbad : Tendsto (fun n => (P n).real (good n)ᶜ) atTop (𝓝 0))
    (cap : ℕ → ℝ) (hcap : Tendsto cap atTop atTop)
    (C : ℝ) (hC : 0 ≤ C)
    (hmoment : ∀ᶠ n in atTop, (∫ x, (good n).indicator
      (fun x => min ‖(X n x).val.2‖ (cap n)) x ∂P n) ≤ C) :
    ∃ (ν : ProbabilityMeasure AnchoredCountingState) (r : ℕ → ℕ), StrictMono r ∧
      External.WeakLawConverges (fun n => Measure.map (X (r n)) (P (r n))) ν := by
  let laws : ℕ → ProbabilityMeasure AnchoredCountingState := fun n =>
    ProbabilityMeasure.map (⟨P n,inferInstance⟩ : ProbabilityMeasure Ω) (hX n).aemeasurable
  have ht := uniform_real_tails_of_good_capped_moment P
    (fun n x => ‖(X n x).val.2‖)
    (fun n => (measurable_snd.comp ((hX n).subtype_val)).norm)
    (fun n x => norm_nonneg _) good hgood hbad cap hcap C hC hmoment
  have htail : ∀ epsilon : ℝ≥0∞, 0 < epsilon → ∃ B : ℝ,
      ∀ n, (laws n : Measure AnchoredCountingState) {s | B < ‖s.val.2‖} ≤ epsilon := by
    intro epsilon hepsilon
    obtain ⟨B,hB⟩ := ht epsilon hepsilon
    refine ⟨B,fun n => ?_⟩
    change (Measure.map (X n) (P n)) {s : AnchoredCountingState | B < ‖s.val.2‖} ≤ epsilon
    have hset : MeasurableSet {s : AnchoredCountingState | B < ‖s.val.2‖} :=
      measurableSet_lt measurable_const (measurable_snd.comp measurable_subtype_coe).norm
    rw [Measure.map_apply (hX n) hset]
    exact hB n
  obtain ⟨ν,r,hr,hlim⟩ := anchored_laws_subsequence_of_uniform_anchor_tails laws htail
  refine ⟨ν,r,hr,?_⟩
  intro F
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim F

end GeneralizedBulk.Analysis
