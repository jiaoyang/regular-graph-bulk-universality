import GeneralizedBulk.Analysis.AnchoredCompactness
import GeneralizedBulk.Analysis.WeakLawTightness
import GeneralizedBulk.Analysis.WeakRelations

/-! Genuine scalar-state weak convergence automatically supplies the
uniform anchored-law tightness used by finite marked-window extraction. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter Set
open scoped Topology
namespace GeneralizedBulk.Analysis

theorem isTightMeasureSet_anchored_of_weakLawConverges
    (μ : ℕ → Measure AnchoredCountingState) [∀ n,IsProbabilityMeasure (μ n)]
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hweak : External.WeakLawConverges μ ν) : IsTightMeasureSet (range μ) := by
  let anchor := fun s : AnchoredCountingState => s.val.2
  have hc : Continuous anchor := continuous_snd.comp continuous_subtype_val
  letI : ∀ n,IsProbabilityMeasure ((μ n).map anchor) := fun n => isProbabilityMeasure_map hc.measurable.aemeasurable
  letI : IsProbabilityMeasure (ν.map anchor) := isProbabilityMeasure_map hc.measurable.aemeasurable
  have ht := isTightMeasureSet_of_weakLawConverges (fun n => (μ n).map anchor) (ν.map anchor)
    (weakLaw_map μ ν hweak anchor hc)
  apply isTightMeasureSet_anchored_of_uniform_anchor_tails μ
  intro ε hε
  obtain ⟨K,hK,hcap⟩ := IsTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp ht ε hε
  obtain ⟨R,hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  refine ⟨R,fun n => ?_⟩
  have hsub : {z : ℂ | R < ‖z‖} ⊆ Kᶜ := by
    intro z hz hzK
    have hh : ‖z‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hR hzK
    exact (not_lt_of_ge hh) hz
  have hh := (measure_mono (μ := (μ n).map anchor) hsub).trans (hcap _ ⟨n,rfl⟩)
  rw [Measure.map_apply hc.measurable (isOpen_lt continuous_const continuous_norm).measurableSet] at hh
  exact hh

theorem uniform_anchor_real_tails_of_weakLawConverges
    (μ : ℕ → Measure AnchoredCountingState) [∀ n,IsProbabilityMeasure (μ n)]
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hweak : External.WeakLawConverges μ ν) :
    ∀ δ : ℝ,0 < δ → ∃ A : ℝ,0 < A ∧
      ∀ n,(μ n).real {s | A < ‖s.val.2‖} ≤ δ := by
  let anchor := fun s : AnchoredCountingState => s.val.2
  have hc : Continuous anchor := continuous_snd.comp continuous_subtype_val
  letI : ∀ n,IsProbabilityMeasure ((μ n).map anchor) := fun n => isProbabilityMeasure_map hc.measurable.aemeasurable
  letI : IsProbabilityMeasure (ν.map anchor) := isProbabilityMeasure_map hc.measurable.aemeasurable
  have ht := isTightMeasureSet_of_weakLawConverges (fun n => (μ n).map anchor) (ν.map anchor)
    (weakLaw_map μ ν hweak anchor hc)
  intro δ hδ
  obtain ⟨K,hK,hcap⟩ := IsTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp ht
    (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ)
  obtain ⟨R,hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  let A := max R 1
  have hA : 0 < A := lt_of_lt_of_le (by norm_num : (0 : ℝ)<1) (le_max_right _ _)
  refine ⟨A,hA,fun n => ?_⟩
  have hsub : {z : ℂ | A < ‖z‖} ⊆ Kᶜ := by
    intro z hz hzK
    have hh : ‖z‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hR hzK
    exact not_lt_of_ge (hh.trans (le_max_left _ _)) hz
  have hb := (measure_mono (μ := (μ n).map anchor) hsub).trans (hcap _ ⟨n,rfl⟩)
  rw [Measure.map_apply hc.measurable (isOpen_lt continuous_const continuous_norm).measurableSet] at hb
  simpa only [Measure.real,ENNReal.toReal_ofReal hδ.le] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hb

end GeneralizedBulk.Analysis
