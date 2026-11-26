import GaussianWave.Foundation

/-!
# Uniformity and convergence in graph probability

These selection lemmas permit size-dependent finite graph spaces and empty
sets of admissible eigenvector selections. There is no hidden assumption that
an admissible tuple exists at every size.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace GaussianWave

/-- Convergence along every subsequence of good selections is uniform on the
good sets, even if some of those sets are empty. -/
theorem uniform_of_subsequence_selections {S : ℕ → Type*}
    (good : ∀ n, Set (S n)) (f : ∀ n, S n → ℝ) (c : ℝ)
    (hseq : ∀ r : ℕ → ℕ, StrictMono r → ∀ x : ∀ j, S (r j),
      (∀ j, x j ∈ good (r j)) →
        Tendsto (fun j => f (r j) (x j)) atTop (𝓝 c)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ x ∈ good n, |f n x - c| < ε := by
  classical
  intro ε hε
  by_contra hnot
  have hbad : ∃ᶠ n in atTop, ∃ x ∈ good n, ε ≤ |f n x - c| := by
    simpa only [not_eventually, not_forall, not_lt, exists_prop] using hnot
  obtain ⟨r, hr, hbad⟩ := extraction_of_frequently_atTop hbad
  let x : ∀ j, S (r j) := fun j => Classical.choose (hbad j)
  have hx (j : ℕ) : x j ∈ good (r j) := (Classical.choose_spec (hbad j)).1
  have hlarge (j : ℕ) : ε ≤ |f (r j) (x j) - c| := (Classical.choose_spec (hbad j)).2
  have hsmall : ∀ᶠ j in atTop, |f (r j) (x j) - c| < ε := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp (hseq r hr x hx)) ε hε
  obtain ⟨j, hj⟩ := hsmall.exists
  exact (not_lt_of_ge (hlarge j)) hj

/-- Tightness in probability of a real bound on varying graph spaces. -/
def TightInProbability {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) (M : ∀ n, Ω n → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ᶠ n in atTop,
    (P n {ω | C < M n ω}).toReal < ε

/-- The probabilistic final step of the note: a tight fourth-moment bound
and common high-probability BS events promote deterministic sequential
convergence to convergence in graph probability. -/
theorem inProbability_of_good_sequences_and_tight_bound
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (good : ∀ n, Set (Ω n))
    (_hgood : ∀ n, MeasurableSet (good n))
    (hbad : Tendsto (fun n => (P n (good n)ᶜ).toReal) atTop (𝓝 0))
    (M e : ∀ n, Ω n → ℝ) (htight : TightInProbability P M)
    (hseq : ∀ C : ℝ, ∀ r : ℕ → ℕ, StrictMono r → ∀ ω : ∀ j, Ω (r j),
      (∀ j, ω j ∈ good (r j) ∧ M (r j) (ω j) ≤ C) →
        Tendsto (fun j => e (r j) (ω j)) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => (P n {ω | ε ≤ |e n ω|}).toReal) atTop (𝓝 0) := by
  intro ε hε
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le ENNReal.toReal_nonneg)
  · intro b hb
    obtain ⟨C, hC⟩ := htight (b / 2) (by linarith)
    have hu := uniform_of_subsequence_selections
      (fun n => {ω | ω ∈ good n ∧ M n ω ≤ C}) e 0 (hseq C) ε hε
    have hg := (tendsto_order.mp hbad).2 (b / 2) (by linarith)
    filter_upwards [hu, hC, hg] with n hn hMn hgn
    have hsub : {ω | ε ≤ |e n ω|} ⊆ (good n)ᶜ ∪ {ω | C < M n ω} := by
      intro ω hω
      by_cases hgω : ω ∈ good n
      · right
        by_contra hnot
        have hs := hn ω ⟨hgω, le_of_not_gt hnot⟩
        simp only [sub_zero] at hs
        exact (not_lt_of_ge hω) hs
      · exact Or.inl hgω
    have hmeasure : P n {ω | ε ≤ |e n ω|} ≤
        P n (good n)ᶜ + P n {ω | C < M n ω} :=
      (measure_mono hsub).trans (measure_union_le _ _)
    have hreal := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩) hmeasure
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at hreal
    linarith

end GaussianWave

namespace GaussianWave

/-- A predicate version of the uniform selection argument, useful for
extended-real Wasserstein thresholds without taking `toReal` of infinity. -/
theorem eventually_no_bad_of_subsequence_selections {S : ℕ → Type*}
    (good bad : ∀ n, Set (S n))
    (hseq : ∀ r : ℕ → ℕ, StrictMono r → ∀ x : ∀ j, S (r j),
      (∀ j, x j ∈ good (r j)) → ∀ᶠ j in atTop, x j ∉ bad (r j)) :
    ∀ᶠ n in atTop, ∀ x ∈ good n, x ∉ bad n := by
  classical
  by_contra hnot
  have hbad : ∃ᶠ n in atTop, ∃ x ∈ good n, x ∈ bad n := by
    simpa only [not_eventually, not_forall, not_not, exists_prop] using hnot
  obtain ⟨r, hr, hb⟩ := extraction_of_frequently_atTop hbad
  let x : ∀ j, S (r j) := fun j => Classical.choose (hb j)
  have hx (j : ℕ) : x j ∈ good (r j) := (Classical.choose_spec (hb j)).1
  obtain ⟨j, hj⟩ := (hseq r hr x hx).exists
  exact hj (Classical.choose_spec (hb j)).2

/-- A general graph-event convergence principle, allowing graph spaces to
vary with N. In applications `bad` means that some admissible eigenvector
selection has Wasserstein error above a fixed positive threshold. -/
theorem probability_bad_tendsto_zero_of_good_subsequences
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (good bad : ∀ n, Set (Ω n))
    (hbad : Tendsto (fun n => (P n (good n)ᶜ).toReal) atTop (𝓝 0))
    (M : ∀ n, Ω n → ℝ) (htight : TightInProbability P M)
    (hseq : ∀ C : ℝ, ∀ r : ℕ → ℕ, StrictMono r → ∀ ω : ∀ j, Ω (r j),
      (∀ j, ω j ∈ good (r j) ∧ M (r j) (ω j) ≤ C) →
        ∀ᶠ j in atTop, ω j ∉ bad (r j)) :
    Tendsto (fun n => (P n (bad n)).toReal) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le ENNReal.toReal_nonneg)
  · intro b hb
    obtain ⟨C, hC⟩ := htight (b / 2) (by linarith)
    have hu := eventually_no_bad_of_subsequence_selections
      (fun n => {ω | ω ∈ good n ∧ M n ω ≤ C}) bad (hseq C)
    have hg := (tendsto_order.mp hbad).2 (b / 2) (by linarith)
    filter_upwards [hu, hC, hg] with n hn hMn hgn
    have hsub : bad n ⊆ (good n)ᶜ ∪ {ω | C < M n ω} := by
      intro ω hω
      by_cases hgω : ω ∈ good n
      · right
        by_contra hnot
        exact hn ω ⟨hgω, le_of_not_gt hnot⟩ hω
      · exact Or.inl hgω
    have hmeasure : P n (bad n) ≤ P n (good n)ᶜ + P n {ω | C < M n ω} :=
      (measure_mono hsub).trans (measure_union_le _ _)
    have hreal := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩) hmeasure
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at hreal
    linarith

end GaussianWave
