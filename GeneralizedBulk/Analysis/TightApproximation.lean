import GeneralizedBulk.Analysis.TruncationConvergence
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! A tight random envelope suffices for vanishing approximation errors.
This is useful for resolvent derivatives when scalar anchors are tight but
uncapped prelimit moments have not yet been shown uniformly integrable. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace GeneralizedBulk.Analysis
variable {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

theorem probability_truncation_tails_of_tight_domination
    {ΩN : ℕ → Type*} [∀ n,MeasurableSpace (ΩN n)]
    (P : ∀ n,Measure (ΩN n)) [∀ n,IsProbabilityMeasure (P n)]
    (X : ∀ n,ΩN n → E) (XR : ℕ → ∀ n,ΩN n → E)
    (M : ∀ n,ΩN n → ℝ) (a : ℕ → ℝ) (ha0 : ∀ R,0 ≤ a R)
    (ha : Tendsto a atTop (𝓝 0))
    (htight : ∀ δ : ℝ,0 < δ → ∃ B : ℝ,0 < B ∧
      ∀ n,(P n).real {x | B < M n x} ≤ δ)
    (hbound : ∀ R n x,dist (X n x) (XR R n x) ≤ a R * M n x) :
    ∀ ε δ : ℝ,0 < ε → 0 < δ →
      ∃ R0,∀ R,R0 ≤ R → ∀ᶠ n in atTop,(P n).real {x | ε < dist (X n x) (XR R n x)} ≤ δ := by
  intro ε δ hε hδ
  obtain ⟨B,hB,hBt⟩ := htight δ hδ
  have hs := (tendsto_order.mp ha).2 (ε/B) (div_pos hε hB)
  obtain ⟨R0,hR0⟩ := eventually_atTop.mp hs
  refine ⟨R0,fun R hR => Eventually.of_forall (fun n => ?_)⟩
  have hsub : {x | ε < dist (X n x) (XR R n x)} ⊆ {x | B < M n x} := by
    intro x hx
    by_contra hn
    have hm : M n x ≤ B := le_of_not_gt hn
    have hab : a R * B < ε := (lt_div_iff₀ hB).mp (hR0 R hR)
    have hh := (hbound R n x).trans (mul_le_mul_of_nonneg_left hm (ha0 R))
    exact (not_lt_of_ge hh) (hab.trans hx)
  exact (measureReal_mono hsub).trans (hBt n)

theorem probability_tails_of_tendsto_ae
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (Y : ℕ → Ω → E) (Z : Ω → E) (hY : ∀ R,Measurable (Y R))
    (hae : ∀ᵐ x ∂Q,Tendsto (fun R => Y R x) atTop (𝓝 (Z x))) :
    ∀ ε δ : ℝ,0 < ε → 0 < δ →
      ∀ᶠ R in atTop,Q.real {x | ε < dist (Y R x) (Z x)} ≤ δ := by
  have hm := tendstoInMeasure_of_tendsto_ae (μ := Q) (f := Y) (g := Z)
    (fun R => (hY R).aestronglyMeasurable) hae
  intro ε δ hε hδ
  have ht := (tendsto_order.mp (hm ε hε)).2 (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ)
  filter_upwards [ht] with R hR
  have hb : Q {x | ε < dist (Y R x) (Z x)} ≤ ENNReal.ofReal δ :=
    (measure_mono (fun x hx => le_of_lt (show ε < dist (Y R x) (Z x) from hx))).trans hR.le
  simpa only [Measure.real,ENNReal.toReal_ofReal hδ.le] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hb

theorem weakLaw_of_tight_dominated_approximations
    {ΩN : ℕ → Type*} {T : Type*} [∀ n,MeasurableSpace (ΩN n)] [MeasurableSpace T]
    [TopologicalSpace.SeparableSpace E]
    (P : ∀ n,Measure (ΩN n)) [∀ n,IsProbabilityMeasure (P n)]
    (Q : Measure T) [IsProbabilityMeasure Q]
    (X : ∀ n,ΩN n → E) (XR : ℕ → ∀ n,ΩN n → E) (YR : ℕ → T → E) (Y : T → E)
    (hX : ∀ n,Measurable (X n)) (hXR : ∀ R n,Measurable (XR R n))
    (hYR : ∀ R,Measurable (YR R)) (hY : Measurable Y)
    (hfinite : ∀ R,External.WeakLawConverges (fun n => (P n).map (XR R n)) (Q.map (YR R)))
    (M : ∀ n,ΩN n → ℝ) (a : ℕ → ℝ) (ha0 : ∀ R,0 ≤ a R)
    (ha : Tendsto a atTop (𝓝 0))
    (htight : ∀ δ : ℝ,0 < δ → ∃ B : ℝ,0 < B ∧
      ∀ n,(P n).real {x | B < M n x} ≤ δ)
    (hbound : ∀ R n x,dist (X n x) (XR R n x) ≤ a R * M n x)
    (htarget : ∀ᵐ x ∂Q,Tendsto (fun R => YR R x) atTop (𝓝 (Y x))) :
    External.WeakLawConverges (fun n => (P n).map (X n)) (Q.map Y) :=
  weakLaw_of_probability_truncations P Q X XR YR Y hX hXR hYR hY hfinite
    (probability_truncation_tails_of_tight_domination P X XR M a ha0 ha htight hbound)
    (probability_tails_of_tendsto_ae Q YR Y hYR htarget)

end GeneralizedBulk.Analysis
