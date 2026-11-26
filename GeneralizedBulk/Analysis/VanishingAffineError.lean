import GeneralizedBulk.Analysis.WeakLawTightness
import GeneralizedBulk.Analysis.WeakRelations

/-! A vanishing deterministic coefficient times a norm-tight scalar is a
vanishing probability error. Uniform prelimit scalar moments are unnecessary. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace GeneralizedBulk.Analysis

variable {Ω : ℕ → Type*} [∀ n,MeasurableSpace (Ω n)]
variable {V : Type*} [NormedAddCommGroup V]

theorem vanishing_affine_error_probability_of_uniform_norm_tails
    (P : ∀ n,Measure (Ω n)) [∀ n,IsProbabilityMeasure (P n)]
    (s : ∀ n,Ω n → V) (c : ℕ → ℝ) (e : ∀ n,Ω n → ℝ)
    (hc : ∀ᶠ n in atTop,0 ≤ c n) (hc0 : Tendsto c atTop (nhds 0))
    (hbound : ∀ᶠ n in atTop,∀ x,e n x ≤ c n*(1+‖s n x‖))
    (htail : ∀ δ : ℝ≥0∞,0 < δ → ∃ B : ℝ,∀ n,P n {x | B < ‖s n x‖} ≤ δ) :
    ∀ ε : ℝ,0 < ε → Tendsto (fun n => (P n).real {x | ε < e n x}) atTop (nhds 0) := by
  intro ε hε
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le measureReal_nonneg)
  · intro δ hδ
    obtain ⟨B,hB⟩ := htail (ENNReal.ofReal (δ/2)) (ENNReal.ofReal_pos.mpr (half_pos hδ))
    let R := max 0 B
    have hR : 0 < 1+R := by dsimp [R]; linarith [le_max_left (0 : ℝ) B]
    have hsmall : ∀ᶠ n in atTop,c n*(1+R) < ε := by
      have hh : Tendsto (fun n => c n*(1+R)) atTop (nhds 0) := by simpa only [zero_mul] using hc0.mul_const (1+R)
      exact hh.eventually (eventually_lt_nhds hε)
    filter_upwards [hc,hbound,hsmall] with n hc hb hs
    have hsub : {x | ε < e n x} ⊆ {x | B < ‖s n x‖} := by
      intro x hx
      by_contra hnot
      have hsn : ‖s n x‖ ≤ R := (le_of_not_gt hnot).trans (le_max_right _ _)
      have hh := (hb x).trans (mul_le_mul_of_nonneg_left (add_le_add_left hsn 1) hc)
      change ε < e n x at hx
      linarith
    have hp : (P n).real {x | B < ‖s n x‖} ≤ δ/2 := by
      simpa only [measureReal_def,ENNReal.toReal_ofReal (half_pos hδ).le] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top (hB n)
    exact (measureReal_mono hsub).trans hp |>.trans_lt (by linarith)

variable [ProperSpace V] [CompleteSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V]

theorem uniform_norm_tails_of_weakLaw_map
    (P : ∀ n,Measure (Ω n)) [∀ n,IsProbabilityMeasure (P n)]
    (s : ∀ n,Ω n → V) (hs : ∀ n,Measurable (s n))
    (ν : Measure V) [IsProbabilityMeasure ν]
    (hweak : External.WeakLawConverges (fun n => (P n).map (s n)) ν) :
    ∀ δ : ℝ≥0∞,0 < δ → ∃ B : ℝ,∀ n,P n {x | B < ‖s n x‖} ≤ δ := by
  letI : ∀ n,IsProbabilityMeasure ((P n).map (s n)) := fun n => isProbabilityMeasure_map (hs n).aemeasurable
  have ht := isTightMeasureSet_of_weakLawConverges _ ν hweak
  intro δ hδ
  obtain ⟨K,hK,hcapture⟩ := IsTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp ht δ hδ
  obtain ⟨B,hB⟩ := hK.isBounded.subset_closedBall (0 : V)
  refine ⟨B,fun n => ?_⟩
  have hsub : {x : V | B < ‖x‖} ⊆ Kᶜ := by
    intro x hx hxK
    have hh : ‖x‖ ≤ B := by simpa only [Metric.mem_closedBall,dist_zero_right] using hB hxK
    exact (not_lt_of_ge hh) hx
  have hh := (measure_mono (μ := (P n).map (s n)) hsub).trans (hcapture _ ⟨n,rfl⟩)
  rw [Measure.map_apply (hs n) (isOpen_lt continuous_const continuous_norm).measurableSet] at hh
  exact hh

theorem vanishing_affine_error_probability_of_weakLaw_map
    (P : ∀ n,Measure (Ω n)) [∀ n,IsProbabilityMeasure (P n)]
    (s : ∀ n,Ω n → V) (hs : ∀ n,Measurable (s n))
    (ν : Measure V) [IsProbabilityMeasure ν]
    (hweak : External.WeakLawConverges (fun n => (P n).map (s n)) ν)
    (c : ℕ → ℝ) (e : ∀ n,Ω n → ℝ)
    (hc : ∀ᶠ n in atTop,0 ≤ c n) (hc0 : Tendsto c atTop (nhds 0))
    (hbound : ∀ᶠ n in atTop,∀ x,e n x ≤ c n*(1+‖s n x‖)) :
    ∀ ε : ℝ,0 < ε → Tendsto (fun n => (P n).real {x | ε < e n x}) atTop (nhds 0) :=
  vanishing_affine_error_probability_of_uniform_norm_tails P s c e hc hc0 hbound
    (uniform_norm_tails_of_weakLaw_map P s hs ν hweak)

theorem vanishing_affine_error_probability_of_weakLaw_observation
    {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    (P : ∀ n,Measure (Ω n)) [∀ n,IsProbabilityMeasure (P n)]
    (X : ∀ n,Ω n → S) (hX : ∀ n,Measurable (X n))
    (ν : Measure S) [IsProbabilityMeasure ν]
    (hweak : External.WeakLawConverges (fun n => (P n).map (X n)) ν)
    (f : S → V) (hf : Continuous f) (c : ℕ → ℝ) (e : ∀ n,Ω n → ℝ)
    (hc : ∀ᶠ n in atTop,0 ≤ c n) (hc0 : Tendsto c atTop (nhds 0))
    (hbound : ∀ᶠ n in atTop,∀ x,e n x ≤ c n*(1+‖f (X n x)‖)) :
    ∀ ε : ℝ,0 < ε → Tendsto (fun n => (P n).real {x | ε < e n x}) atTop (nhds 0) := by
  letI : IsProbabilityMeasure (ν.map f) := isProbabilityMeasure_map hf.measurable.aemeasurable
  have hm := weakLaw_map (fun n => (P n).map (X n)) ν hweak f hf
  have hm' : External.WeakLawConverges (fun n => (P n).map (fun x => f (X n x))) (ν.map f) := by
    simpa only [Measure.map_map hf.measurable (hX _),Function.comp_def] using hm
  exact vanishing_affine_error_probability_of_weakLaw_map P (fun n x => f (X n x))
    (fun n => hf.measurable.comp (hX n)) (ν.map f) hm' c e hc hc0 hbound

end GeneralizedBulk.Analysis
