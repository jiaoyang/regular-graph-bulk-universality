import Mathlib

/-! Deterministic shrinking envelopes for convergence in probability on
possibly varying probability spaces. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology Classical

namespace GeneralizedBulk.Graph

/-- A fixed finite sum of errors tending to zero in probability also tends
to zero in probability, on sample spaces that may depend on the index. -/
theorem finite_sum_inProbability_zero
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (k : ℕ) (hk : 0 < k) (r : ∀ n, Ω n → Fin k → ℝ)
    (hprob : ∀ a (t : ℝ), 0 < t →
      Tendsto (fun n => (P n {ω | t ≤ r n ω a}).toReal) atTop (𝓝 0)) :
    ∀ t : ℝ, 0 < t → Tendsto
      (fun n => (P n {ω | t ≤ ∑ a, r n ω a}).toReal) atTop (𝓝 0) := by
  intro t ht
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hsum : Tendsto (fun n => ∑ a : Fin k,
      (P n {ω | t / k ≤ r n ω a}).toReal) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using
      tendsto_finset_sum (Finset.univ : Finset (Fin k))
        (fun a _ => hprob a (t / k) (div_pos ht hkR))
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) (fun n => ?_) hsum
  have hsub : {ω | t ≤ ∑ a, r n ω a} ⊆
      ⋃ a : Fin k, {ω | t / k ≤ r n ω a} := by
    intro ω hω
    apply Set.mem_iUnion.mpr
    by_contra hnone
    have hsmall : ∀ a : Fin k, r n ω a < t / k := by
      simpa only [not_exists, Set.mem_setOf_eq, not_le] using hnone
    have hlt := Finset.sum_lt_sum_of_nonempty
      (s := Finset.univ) (show (Finset.univ : Finset (Fin k)).Nonempty from
        ⟨⟨0, hk⟩, Finset.mem_univ _⟩) (fun a _ => hsmall a)
    have htot : (∑ _a : Fin k, t / (k : ℝ)) = t := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    rw [htot] at hlt
    exact (not_lt_of_ge hω) hlt
  exact (measureReal_mono hsub).trans (measureReal_iUnion_fintype_le _)

/-- A random error converging to zero in probability admits a positive,
antitone deterministic envelope tending to zero, outside which the
probability also tends to zero. The sample space may vary with the index. -/
theorem exists_shrinking_probability_width
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (r : ∀ n, Ω n → ℝ)
    (hprob : ∀ t : ℝ, 0 < t →
      Tendsto (fun n => (P n {ω | t ≤ r n ω}).toReal) atTop (𝓝 0)) :
    ∃ δ : ℕ → ℝ, (∀ n, 0 < δ n) ∧ Antitone δ ∧
      Tendsto δ atTop (𝓝 0) ∧
      Tendsto (fun n => (P n {ω | δ n < r n ω}).toReal) atTop (𝓝 0) := by
  let s : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
  have hs (m : ℕ) : 0 < s m := by dsimp [s]; positivity
  have htail (m : ℕ) : ∃ T : ℕ, ∀ n ≥ T,
      (P n {ω | s m ≤ r n ω}).toReal < s m := by
    exact eventually_atTop.mp ((hprob (s m) (hs m)).eventually (gt_mem_nhds (hs m)))
  choose T hT using htail
  let valid (n : ℕ) : Finset ℕ := (Finset.range (n + 1)).filter (fun m => T m ≤ n)
  let level (n : ℕ) : ℕ := (valid n).sup id
  have hlevel : Monotone level := by
    intro n n' hnn'
    apply Finset.sup_mono
    intro m hm
    simp only [valid, Finset.mem_filter, Finset.mem_range] at hm ⊢
    exact ⟨by omega, hm.2.trans hnn'⟩
  have hlevelTop : Tendsto level atTop atTop := by
    apply tendsto_atTop.2
    intro m
    filter_upwards [eventually_ge_atTop (max m (T m))] with n hn
    apply Finset.le_sup (f := id)
    simp only [valid, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, (le_max_right m (T m)).trans hn⟩
  have hactive : ∀ᶠ n in atTop, T (level n) ≤ n := by
    filter_upwards [eventually_ge_atTop (T 0)] with n hn
    have hnempty : (valid n).Nonempty := by
      refine ⟨0, ?_⟩
      simp [valid, hn]
    obtain ⟨m, hm, heq⟩ := Finset.sup_mem_of_nonempty (f := id) hnempty
    have hTm : T m ≤ n := (Finset.mem_filter.mp hm).2
    change m = level n at heq
    simpa only [← heq] using hTm
  refine ⟨fun n => s (level n), fun n => hs _, ?_, ?_, ?_⟩
  · intro n n' hnn'
    dsimp [s]
    apply one_div_le_one_div_of_le (by positivity)
    have hh : (level n : ℝ) ≤ level n' := by exact_mod_cast hlevel hnn'
    linarith
  · exact tendsto_one_div_add_atTop_nhds_zero_nat.comp hlevelTop
  · apply squeeze_zero' (Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))
      (hactive.mono (fun n hn => ?_))
      (tendsto_one_div_add_atTop_nhds_zero_nat.comp hlevelTop)
    exact (ENNReal.toReal_mono (measure_ne_top (P n) _)
      (measure_mono (fun ω hω => by
        change s (level n) < r n ω at hω
        exact hω.le))).trans (hT _ n hn).le

end GeneralizedBulk.Graph
