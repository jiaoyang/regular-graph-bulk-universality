import GeneralizedBulk.Gaussian.Presentation
import GeneralizedBulk.Counting.WindowOccurrences
import GeneralizedBulk.Counting.OccurrenceUniqueness
import GeneralizedBulk.Counting.FinitePresentationEquiv

/-! Actual finite window labels in every countable particle presentation. -/
noncomputable section
open MeasureTheory BourgadeHuang
open scoped ENNReal BigOperators
namespace GeneralizedBulk.Gaussian
open Counting
namespace ParticlePresentation
variable {I : Type*} [Countable I] {s : AnchoredCountingState}

abbrev WindowLabels (p : ParticlePresentation s I) (a b : ℝ) :=
  {i : I // p.location i ∈ Set.Icc a b}

theorem restrict_eq_sum_window (p : ParticlePresentation s I) (a b : ℝ) :
    s.val.1.measure.restrict (Set.Icc a b) =
      Measure.sum (fun i : p.WindowLabels a b => Measure.dirac (p.location i.val)) := by
  classical
  ext B hB
  rw [Measure.restrict_apply hB,p.measure_eq,Measure.sum_apply _ (hB.inter measurableSet_Icc),
    Measure.sum_apply _ hB]
  have hsupport : Function.support (fun i : I => Measure.dirac (p.location i) (B ∩ Set.Icc a b)) ⊆
      {i | p.location i ∈ Set.Icc a b} := by
    intro i hi
    by_cases hmem : p.location i ∈ Set.Icc a b
    · exact hmem
    · exact False.elim (hi (by
        simp [Measure.dirac_apply' _ (hB.inter measurableSet_Icc),Set.indicator_apply,hmem]))
  rw [← tsum_subtype_eq_of_support_subset hsupport]
  apply tsum_congr
  intro i
  simp [Measure.dirac_apply' _ (hB.inter measurableSet_Icc),Measure.dirac_apply' _ hB,
    Set.indicator_apply,i.property.1,i.property.2]

theorem finite_windowLabels (p : ParticlePresentation s I) (a b : ℝ) : Finite (p.WindowLabels a b) := by
  classical
  by_cases h : Finite (p.WindowLabels a b)
  · exact h
  · letI : Infinite (p.WindowLabels a b) := not_finite_iff_infinite.mp h
    have heq := congrArg (fun μ : Measure ℝ => μ Set.univ) (p.restrict_eq_sum_window a b)
    dsimp only at heq
    rw [Measure.restrict_apply_univ,Measure.sum_apply _ MeasurableSet.univ] at heq
    simp only [Measure.dirac_apply_of_mem (Set.mem_univ _)] at heq
    rw [ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero] at heq
    exact False.elim (isCompact_Icc.measure_ne_top heq)

/-- There is a literal injection selecting every window occurrence, and it
matches the canonical sorted window list exactly. No simplicity is required. -/
theorem exists_window_selection (p : ParticlePresentation s I) (a b : ℝ) :
    ∃ e : Fin (intervalCount s.val.1 a b) → I, Function.Injective e ∧
      (∀ k, p.location (e k) = windowOccurrence s.val.1 a b k.val) ∧
      Set.range e = {i | p.location i ∈ Set.Icc a b} := by
  classical
  letI : Finite (p.WindowLabels a b) := p.finite_windowLabels a b
  letI := Fintype.ofFinite (p.WindowLabels a b)
  have hfinite : s.val.1.measure.restrict (Set.Icc a b) =
      ∑ i : p.WindowLabels a b, Measure.dirac (p.location i.val) := by
    rw [p.restrict_eq_sum_window a b]
    ext B hB
    rw [Measure.sum_apply _ hB,Measure.finset_sum_apply,tsum_fintype]
  have hcanonical : s.val.1.measure.restrict (Set.Icc a b) =
      ∑ k : Fin (intervalCount s.val.1 a b), Measure.dirac (windowOccurrence s.val.1 a b k.val) := by
    have h := finiteCountingMeasure_eq_sum_occurrences (windowCountingMeasure s.val.1 a b)
    rw [finiteCount_window] at h
    exact h
  obtain ⟨q,hq⟩ := finite_dirac_presentations_equiv
    (fun i : p.WindowLabels a b => p.location i.val)
    (fun k : Fin (intervalCount s.val.1 a b) => windowOccurrence s.val.1 a b k.val)
    (hfinite.symm.trans hcanonical)
  refine ⟨fun k => (q.symm k).val,Subtype.val_injective.comp q.symm.injective,?_,?_⟩
  · intro k
    simpa only [q.apply_symm_apply] using (hq (q.symm k)).symm
  · ext i
    constructor
    · rintro ⟨k,rfl⟩
      exact (q.symm k).property
    · intro hi
      exact ⟨q ⟨i,hi⟩,by simp⟩

end ParticlePresentation
end GeneralizedBulk.Gaussian
