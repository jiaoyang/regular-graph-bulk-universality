import GeneralizedBulk.Graph.ResolventJets
import GeneralizedBulk.Gaussian.StratifiedJets

/-! Actual graph raw derivative laws converge to the constructed mixed
Gaussian derivatives whenever their value laws do. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped Topology
namespace GeneralizedBulk.External.RegularSpectralData
open Graph GeneralizedBulk.Analysis GeneralizedBulk.Gaussian
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

theorem weakLaw_rawValueJet_mass
    {I : Type*} [Fintype I] (P : Measure Ω) [IsProbabilityMeasure P] (hd : 0 < d)
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hm : Integrable (fun s : AnchoredCountingState => ‖s.val.2‖) ν)
    (parameters : Parameters) (E center : ℝ) (w : I → GraphNonreal)
    (hvalues : ∀ R : ℕ,External.WeakLawConverges
      (fun n => (P.prod (uniformOrientedProposals (N n) d)).map (fun z =>
        finitePairedValues (fun i => (w i).val) (1/((R : ℝ)+1))
          (D.rawCoordinateExtension n E parameters.scale center z)))
      ((massMarkedLaw ν parameters).map (fun z =>
        finitePairedValues (fun i => (w i).val) (1/((R : ℝ)+1))
          (massRawCoordinate ν hm parameters z))))
    (htight : ∀ δ : ℝ,0 < δ → ∃ A : ℝ,0 < A ∧ ∀ n,
      P.real {ω | A < ‖(D.microscopicCountingState n ω E parameters.scale center).val.2‖} ≤ δ) :
    External.WeakLawConverges
      (fun n => (P.prod (uniformOrientedProposals (N n) d)).map (fun z =>
        finiteValueJet (fun i => (w i).val) (D.rawCoordinateExtension n E parameters.scale center z)
          (D.rawCoordinateDerivative n E parameters.scale z)))
      ((massMarkedLaw ν parameters).map (fun z =>
        finiteValueJet (fun i => (w i).val) (massRawCoordinate ν hm parameters z)
          (massRawCoordinateDerivative ν hm parameters z))) := by
  apply D.weakLaw_rawValueJet_of_value_laws P hd (massMarkedLaw ν parameters)
    E parameters.scale center w (massRawCoordinate ν hm parameters)
    (massRawCoordinateDerivative ν hm parameters)
    (measurable_massRawCoordinate ν hm parameters)
    (measurable_massRawCoordinateDerivative ν hm parameters) hvalues htight
  filter_upwards [hasDerivAt_massRawCoordinate_ae ν hm parameters] with z hz
  intro i j
  exact hz (w i).val (w i).property j

end GeneralizedBulk.External.RegularSpectralData
