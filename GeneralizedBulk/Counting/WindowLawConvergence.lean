import GeneralizedBulk.Counting.WindowOccurrences
import GeneralizedBulk.Analysis.AEContinuousMapping
import BourgadeHuang.AnchoredSequenceCompactness

/-! Scalar-state weak convergence controls the actual finite sorted windows. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped Topology
namespace GeneralizedBulk.Counting

abbrev WindowData (m : ℕ) := AnchoredCountingState × (ℕ × (Fin m → ℝ))

def windowData (m : ℕ) (a b : ℝ) (s : AnchoredCountingState) : WindowData m :=
  (s,(intervalCount s.val.1 a b,fun j => windowOccurrence s.val.1 a b j.val))

theorem measurable_windowData (m : ℕ) (a b : ℝ) : Measurable (windowData m a b) := by
  have hscalar : Measurable (fun s : AnchoredCountingState => s.val.1) :=
    measurable_fst.comp measurable_subtype_coe
  exact measurable_id.prodMk (((measurable_intervalCount a b).comp hscalar).prodMk
    (measurable_pi_lambda _ (fun j => (measurable_windowOccurrence a b j.val).comp hscalar)))

theorem continuousAt_windowData (m : ℕ) (a b : ℝ) (s : AnchoredCountingState)
    (ha : s.val.1.measure {a} = 0) (hb : s.val.1.measure {b} = 0) :
    ContinuousAt (windowData m a b) s := by
  have hscalar : ContinuousAt (fun t : AnchoredCountingState => t.val.1) s :=
    (continuous_fst.comp continuous_subtype_val).continuousAt
  have hc : ContinuousAt (fun t : AnchoredCountingState => intervalCount t.val.1 a b) s :=
    (continuousAt_intervalCount s.val.1 a b ha hb).comp
      (f := fun t : AnchoredCountingState => t.val.1) (x := s) hscalar
  have hp : ContinuousAt (fun t : AnchoredCountingState =>
      fun j : Fin m => windowOccurrence t.val.1 a b j.val) s := by
    apply continuousAt_pi.mpr
    intro j
    exact (continuousAt_windowOccurrence s.val.1 a b j.val ha hb).comp
      (f := fun t : AnchoredCountingState => t.val.1) (x := s) hscalar
  exact continuousAt_id.prodMk (hc.prodMk hp)

/-- Genuine scalar/counting weak convergence automatically includes sorted
finite windows whenever the deterministic boundary is almost surely atom free. -/
theorem weakLaw_windowData_of_weak
    (μ : ℕ → Measure AnchoredCountingState) [∀ n, IsProbabilityMeasure (μ n)]
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hweak : External.WeakLawConverges μ ν) (m : ℕ) (a b : ℝ)
    (hboundary : ∀ᵐ s ∂ν, s.val.1.measure {a} = 0 ∧ s.val.1.measure {b} = 0) :
    External.WeakLawConverges (fun n => Measure.map (windowData m a b) (μ n))
      (Measure.map (windowData m a b) ν) := by
  letI : PolishSpace AnchoredCountingState := isClosed_validAnchoredCountingState.polishSpace
  letI : MetricSpace AnchoredCountingState := TopologicalSpace.metrizableSpaceMetric AnchoredCountingState
  apply Analysis.weakLaw_map_of_ae_continuous μ ν hweak (windowData m a b) (measurable_windowData m a b)
  filter_upwards [hboundary] with s hs
  exact continuousAt_windowData m a b s hs.1 hs.2

end GeneralizedBulk.Counting
