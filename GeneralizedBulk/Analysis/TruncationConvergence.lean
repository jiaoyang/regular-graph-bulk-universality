import GeneralizedBulk.ExternalInputs
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-! Genuine weak-law closure under finite truncation. Couplings with small
probability of a metric error control the actual Levy--Prokhorov distance. -/
noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
namespace GeneralizedBulk.Analysis
variable {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E]
  [MeasurableSpace E] [BorelSpace E]

theorem map_measure_le_thickening_add_of_coupling (P : Measure Ω)
    (X Y : Ω → E) (hX : Measurable X) (hY : Measurable Y)
    (δ : ℝ) (hδ : 0 < δ) (B : Set E) (hB : MeasurableSet B) :
    (P.map X) B ≤ (P.map Y) (thickening (2*δ) B) + P {x | δ < dist (X x) (Y x)} := by
  have hsub : X ⁻¹' B ⊆ Y ⁻¹' thickening (2*δ) B ∪ {x | δ < dist (X x) (Y x)} := by
    intro x hx
    by_cases h : δ < dist (X x) (Y x)
    · exact Or.inr h
    · apply Or.inl
      apply mem_thickening_iff.mpr
      refine ⟨X x,hx,?_⟩
      rw [dist_comm]
      exact (le_of_not_gt h).trans_lt (by linarith)
  rw [Measure.map_apply hX hB,Measure.map_apply hY isOpen_thickening.measurableSet]
  exact (measure_mono hsub).trans (measure_union_le _ _)

theorem levyProkhorovDist_map_le_of_error_probability (P : Measure Ω) [IsFiniteMeasure P]
    (X Y : Ω → E) (hX : Measurable X) (hY : Measurable Y)
    (δ : ℝ) (hδ : 0 < δ)
    (herror : P.real {x | δ < dist (X x) (Y x)} ≤ δ) :
    levyProkhorovDist (P.map X) (P.map Y) ≤ 2*δ := by
  have hb : P {x | δ < dist (X x) (Y x)} ≤ ENNReal.ofReal δ := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
    exact ENNReal.ofReal_le_ofReal herror
  have he : levyProkhorovEDist (P.map X) (P.map Y) ≤ ENNReal.ofReal (2*δ) := by
    apply sInf_le
    intro B hB
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*δ)]
    constructor
    · exact (map_measure_le_thickening_add_of_coupling P X Y hX hY δ hδ B hB).trans
        (add_le_add_left (hb.trans (ENNReal.ofReal_le_ofReal (by linarith))) _)
    · have hbs : P {x | δ < dist (Y x) (X x)} ≤ ENNReal.ofReal δ := by simpa only [dist_comm] using hb
      exact (map_measure_le_thickening_add_of_coupling P Y X hY hX δ hδ B hB).trans
        (add_le_add_left (hbs.trans (ENNReal.ofReal_le_ofReal (by linarith))) _)
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top he).trans_eq (ENNReal.toReal_ofReal (by positivity))

theorem tendsto_of_metric_truncations {M : Type*} [PseudoMetricSpace M]
    (X : ℕ → M) (XR : ℕ → ℕ → M) (YR : ℕ → M) (Y : M)
    (hfinite : ∀ R,Tendsto (XR R) atTop (𝓝 (YR R)))
    (hpre : ∀ ε : ℝ,0 < ε → ∃ R0,∀ R,R0 ≤ R → ∀ᶠ n in atTop,dist (X n) (XR R n) ≤ ε)
    (htarget : Tendsto YR atTop (𝓝 Y)) : Tendsto X atTop (𝓝 Y) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨R0,hR0⟩ := hpre (ε/3) (by linarith)
  have htarget' := (Metric.tendsto_nhds.mp htarget) (ε/3) (by linarith)
  obtain ⟨R1,hR1⟩ := eventually_atTop.mp htarget'
  let R := max R0 R1
  have hf := (Metric.tendsto_nhds.mp (hfinite R)) (ε/3) (by linarith)
  filter_upwards [hR0 R (le_max_left _ _),hf] with n hn hnf
  have ht := hR1 R (le_max_right _ _)
  exact (dist_triangle (X n) (XR R n) Y).trans_lt (by
    have hd := dist_triangle (XR R n) (YR R) Y
    linarith)

def levyProbability (P : Measure E) [IsProbabilityMeasure P] : LevyProkhorov (ProbabilityMeasure E) :=
  ⟨P,inferInstance⟩

theorem levyProbability_tendsto_of_probability (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → E) (Y : Ω → E) (hX : ∀ n,Measurable (X n)) (hY : Measurable Y)
    (hprob : ∀ ε δ : ℝ,0 < ε → 0 < δ →
      ∀ᶠ n in atTop,P.real {x | ε < dist (X n x) (Y x)} ≤ δ) :
    letI : ∀ n,IsProbabilityMeasure (P.map (X n)) := fun n => isProbabilityMeasure_map (hX n).aemeasurable
    letI : IsProbabilityMeasure (P.map Y) := isProbabilityMeasure_map hY.aemeasurable
    Tendsto (fun n => levyProbability (P.map (X n))) atTop (𝓝 (levyProbability (P.map Y))) := by
  letI : ∀ n,IsProbabilityMeasure (P.map (X n)) := fun n => isProbabilityMeasure_map (hX n).aemeasurable
  letI : IsProbabilityMeasure (P.map Y) := isProbabilityMeasure_map hY.aemeasurable
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hprob (ε/3) (ε/3) (by linarith) (by linarith)] with n hn
  have hh := levyProkhorovDist_map_le_of_error_probability P (X n) Y (hX n) hY (ε/3) (by linarith) hn
  exact hh.trans_lt (by linarith)

theorem weakLaw_of_probability_truncations
    {ΩN : ℕ → Type*} {T : Type*} [∀ n,MeasurableSpace (ΩN n)] [MeasurableSpace T] [TopologicalSpace.SeparableSpace E]
    (P : ∀ n,Measure (ΩN n)) [∀ n,IsProbabilityMeasure (P n)]
    (Q : Measure T) [IsProbabilityMeasure Q]
    (X : ∀ n,ΩN n → E) (XR : ℕ → ∀ n,ΩN n → E) (YR : ℕ → T → E) (Y : T → E)
    (hX : ∀ n,Measurable (X n)) (hXR : ∀ R n,Measurable (XR R n))
    (hYR : ∀ R,Measurable (YR R)) (hY : Measurable Y)
    (hfinite : ∀ R,External.WeakLawConverges (fun n => (P n).map (XR R n)) (Q.map (YR R)))
    (hpre : ∀ ε δ : ℝ,0 < ε → 0 < δ →
      ∃ R0,∀ R,R0 ≤ R → ∀ᶠ n in atTop,(P n).real {x | ε < dist (X n x) (XR R n x)} ≤ δ)
    (htarget : ∀ ε δ : ℝ,0 < ε → 0 < δ →
      ∀ᶠ R in atTop,Q.real {x | ε < dist (YR R x) (Y x)} ≤ δ) :
    External.WeakLawConverges (fun n => (P n).map (X n)) (Q.map Y) := by
  letI : ∀ n,IsProbabilityMeasure ((P n).map (X n)) := fun n => isProbabilityMeasure_map (hX n).aemeasurable
  letI : ∀ R n,IsProbabilityMeasure ((P n).map (XR R n)) := fun R n => isProbabilityMeasure_map (hXR R n).aemeasurable
  letI : ∀ R,IsProbabilityMeasure (Q.map (YR R)) := fun R => isProbabilityMeasure_map (hYR R).aemeasurable
  letI : IsProbabilityMeasure (Q.map Y) := isProbabilityMeasure_map hY.aemeasurable
  have hf (R : ℕ) : Tendsto (fun n => levyProbability ((P n).map (XR R n))) atTop
      (𝓝 (levyProbability (Q.map (YR R)))) := by
    let laws : ℕ → ProbabilityMeasure E := fun n => ⟨(P n).map (XR R n),inferInstance⟩
    let limit : ProbabilityMeasure E := ⟨Q.map (YR R),inferInstance⟩
    have hh : Tendsto laws atTop (𝓝 limit) := by
      apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
      intro F
      exact hfinite R F
    exact (homeomorph_probabilityMeasure_levyProkhorov (Ω := E)).continuous_toFun.continuousAt.tendsto.comp hh
  have hp : ∀ ε : ℝ,0 < ε → ∃ R0,∀ R,R0 ≤ R → ∀ᶠ n in atTop,
      dist (levyProbability ((P n).map (X n))) (levyProbability ((P n).map (XR R n))) ≤ ε := by
    intro ε hε
    obtain ⟨R0,hR0⟩ := hpre (ε/3) (ε/3) (by linarith) (by linarith)
    refine ⟨R0,fun R hR => ?_⟩
    filter_upwards [hR0 R hR] with n hn
    exact (levyProkhorovDist_map_le_of_error_probability (P n) (X n) (XR R n)
      (hX n) (hXR R n) (ε/3) (by linarith) hn).trans (by linarith)
  have ht := levyProbability_tendsto_of_probability Q YR Y hYR hY htarget
  have hall := tendsto_of_metric_truncations _ _ _ _ hf hp ht
  have hweak := (homeomorph_probabilityMeasure_levyProkhorov (Ω := E)).continuous_invFun.continuousAt.tendsto.comp hall
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak

theorem weakLaw_of_equal_on_large_events
    {ΩN : ℕ → Type*} [∀ n,MeasurableSpace (ΩN n)] [TopologicalSpace.SeparableSpace E]
    (P : ∀ n,Measure (ΩN n)) [∀ n,IsProbabilityMeasure (P n)]
    (X X' : ∀ n,ΩN n → E) (hX : ∀ n,Measurable (X n)) (hX' : ∀ n,Measurable (X' n))
    (good : ∀ n,Set (ΩN n)) (heq : ∀ n x,x ∈ good n → X n x=X' n x)
    (hbad : Tendsto (fun n => (P n).real (good n)ᶜ) atTop (𝓝 0))
    (ν : Measure E) [IsProbabilityMeasure ν]
    (hweak : External.WeakLawConverges (fun n => (P n).map (X' n)) ν) :
    External.WeakLawConverges (fun n => (P n).map (X n)) ν := by
  have hm := weakLaw_of_probability_truncations P ν X (fun _ => X') (fun _ => id) id
    hX (fun _ => hX') (fun _ => measurable_id) measurable_id
  simp only [Measure.map_id] at hm
  apply hm
  · intro R
    simpa only [Measure.map_id] using hweak
  · intro ε δ hε hδ
    refine ⟨0,fun R hR => ?_⟩
    filter_upwards [(tendsto_order.mp hbad).2 δ hδ] with n hn
    have hsub : {x | ε < dist (X n x) (X' n x)} ⊆ (good n)ᶜ := by
      intro x hx hgood
      change ε < dist (X n x) (X' n x) at hx
      rw [heq n x hgood,dist_self] at hx
      exact (not_lt_of_ge hε.le) hx
    exact (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)).trans hn.le
  · intro ε δ hε hδ
    apply Eventually.of_forall
    intro R
    have he : {x : E | ε < dist x x} = ∅ := by ext x; simp [not_lt.mpr hε.le]
    change ν.real {x : E | ε < dist x x} ≤ δ
    simpa only [he,measureReal_empty] using hδ.le

end GeneralizedBulk.Analysis
