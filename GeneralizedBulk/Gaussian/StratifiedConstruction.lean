import GeneralizedBulk.Counting.MassStrata
import GeneralizedBulk.Analysis.CountableStrata
import GeneralizedBulk.Gaussian.HeightVariance

/-!
# Actual Gaussian marking before infinite-particle normalization

Finite counting-mass strata use Fin m independent marks and the infinite
stratum uses Nat. Their actual conditioned scalar laws are mixed with their
original masses. The resulting scalar marginal is exactly the starting law.
-/
noncomputable section
open MeasureTheory BourgadeHuang
open scoped Topology ENNReal
namespace GeneralizedBulk.Gaussian
open Counting Analysis

abbrev MassActive (ν : Measure AnchoredCountingState) := ActiveStratum ν massClass
abbrev MassMarkSpace (ν : Measure AnchoredCountingState) (i : MassActive ν) := MassLabels i.val → (Fin 4 → ℝ)
abbrev MassMarkedSample (ν : Measure AnchoredCountingState) :=
  StratumSample ν massClass (MassMarkSpace ν)

def massStratumLaw (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (i : MassActive ν) : ProbabilityMeasure (MassState i.val) :=
  stratumProbability ν massClass measurable_massClass i

theorem massStratum_anchor_integrable (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hm : Integrable (fun s : AnchoredCountingState => ‖s.val.2‖) ν) (i : MassActive ν) :
    Integrable (fun s : MassState i.val => ‖(stratumPresentation i.val s).scalar.val.2‖)
      (massStratumLaw ν i : Measure (MassState i.val)) := by
  have h := integrable_conditionalSubtypeLaw ν (stratumSet massClass i.val)
    (measurable_massClass (measurableSet_singleton i.val)) i.property
    (fun s : AnchoredCountingState => ‖s.val.2‖) hm
  simpa only [stratumPresentation_scalar] using h

/-- The actual mixed probability law of scalar state and independent Gaussian
marks, with finite mass allowed at this stage. -/
def massMarkedLaw (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (parameters : Parameters) : Measure (MassMarkedSample ν) :=
  stratumMarkedLaw ν massClass measurable_massClass (MassMarkSpace ν)
    (fun i => iidLaw (markLaw parameters.p) (MassLabels i.val))

instance massMarkedLaw_isProbability (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (parameters : Parameters) : IsProbabilityMeasure (massMarkedLaw ν parameters) := by
  unfold massMarkedLaw
  infer_instance

def massScalarState (ν : Measure AnchoredCountingState) : MassMarkedSample ν → AnchoredCountingState :=
  stratumSampleValue ν massClass (MassMarkSpace ν)

theorem measurable_massScalarState (ν : Measure AnchoredCountingState) : Measurable (massScalarState ν) :=
  measurable_stratumSampleValue ν massClass (MassMarkSpace ν)

theorem massMarkedLaw_scalar_marginal (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (parameters : Parameters) : Measure.map (massScalarState ν) (massMarkedLaw ν parameters) = ν :=
  stratumMarkedLaw_value_marginal ν massClass measurable_massClass (MassMarkSpace ν)
    (fun i => iidLaw (markLaw parameters.p) (MassLabels i.val))

theorem massScalarState_identDistrib (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (parameters : Parameters) : ProbabilityTheory.IdentDistrib (massScalarState ν) id
      (massMarkedLaw ν parameters) ν := by
  refine ⟨(measurable_massScalarState ν).aemeasurable,measurable_id.aemeasurable,?_⟩
  simpa only [Measure.map_id] using massMarkedLaw_scalar_marginal ν parameters

/-- The actual analytic Gaussian series is constructed on every stratum;
there is no infinite-particle premise in this definition. -/
def massCenteredField (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hm : Integrable (fun s : AnchoredCountingState => ‖s.val.2‖) ν)
    (parameters : Parameters) (v : ℂ × Bool) (z : MassMarkedSample ν) : EndpointMatrix :=
  constructedField (massStratumLaw ν z.1 : Measure (MassState z.1.val))
    (stratumPresentation z.1.val) (measurable_stratumPresentation z.1.val)
    (massStratum_anchor_integrable ν hm z.1) parameters v z.2

/-- The mixed analytic field is a genuinely measurable random matrix. -/
theorem measurable_massCenteredField (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hm : Integrable (fun s : AnchoredCountingState => ‖s.val.2‖) ν)
    (parameters : Parameters) (v : ℂ × Bool) :
    Measurable (massCenteredField ν hm parameters v) := by
  apply measurable_sigma_of_sections
  intro i
  exact measurable_constructedField (massStratumLaw ν i : Measure (MassState i.val))
    (stratumPresentation i.val) (measurable_stratumPresentation i.val)
    (massStratum_anchor_integrable ν hm i) parameters v

def massMarkedMatrix (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hm : Integrable (fun s : AnchoredCountingState => ‖s.val.2‖) ν)
    (parameters : Parameters) (w : ℂ) (z : MassMarkedSample ν) : EndpointMatrix :=
  Marked.mean parameters id w (massScalarState ν z) + massCenteredField ν hm parameters (w,false) z

/-- On every stratum the mixed raw matrix is exactly the already constructed
Gaussian marked matrix of that stratum's canonical presentation. -/
theorem massMarkedMatrix_mk (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hm : Integrable (fun s : AnchoredCountingState => ‖s.val.2‖) ν)
    (parameters : Parameters) (w : ℂ) (i : MassActive ν)
    (z : MassState i.val × MassMarkSpace ν i) :
    massMarkedMatrix ν hm parameters w ⟨i,z⟩ =
      Marked.markedMatrix parameters (fun s => (stratumPresentation i.val s).scalar)
        (constructedZ (massStratumLaw ν i : Measure (MassState i.val))
          (stratumPresentation i.val) (measurable_stratumPresentation i.val)
          (massStratum_anchor_integrable ν hm i) parameters) w z.1 z.2 := by
  simp only [massMarkedMatrix,massCenteredField,Marked.markedMatrix]
  simp [Marked.mean,stratumPresentation_scalar,constructedZ,constructedField,massScalarState,
    stratumSampleValue]

end GeneralizedBulk.Gaussian
