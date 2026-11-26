import GeneralizedBulk.Gaussian.StratifiedJets
import GeneralizedBulk.Exterior.StratifiedExterior
import GeneralizedBulk.Exterior.FiniteJetCoordinates

/-! The finite constructed raw jet maps to the exact mixed exterior values. -/
noncomputable section
open MeasureTheory BourgadeHuang
namespace GeneralizedBulk.Gaussian
open Graph Exterior Analysis Counting
variable (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
variable (hm : Integrable (fun s : AnchoredCountingState => ‖s.val.2‖) ν)

@[simp] theorem finiteRawJetMatrix_massRawCoordinate_value
    {I : Type*} [Fintype I] (parameters : Parameters) (w : I → GraphNonreal)
    (z : MassMarkedSample ν) (i : I) :
    finiteRawJetMatrix (finiteValueJet (fun i => (w i).val)
      (massRawCoordinate ν hm parameters z) (massRawCoordinateDerivative ν hm parameters z)) i false =
      massMarkedMatrix ν hm parameters (w i).val z := by
  ext a b
  simp [finiteRawJetMatrix,finiteValueJet,massRawCoordinate,(w i).property]

@[simp] theorem finiteRawJetMatrix_massRawCoordinate_derivative
    {I : Type*} [Fintype I] (parameters : Parameters) (w : I → GraphNonreal)
    (z : MassMarkedSample ν) (i : I) :
    finiteRawJetMatrix (finiteValueJet (fun i => (w i).val)
      (massRawCoordinate ν hm parameters z) (massRawCoordinateDerivative ν hm parameters z)) i true =
      massMarkedDerivative ν hm parameters (w i).val z := by
  ext a b
  simp [finiteRawJetMatrix,finiteValueJet,massRawCoordinateDerivative,(w i).property]

theorem finiteJetExterior_massRawCoordinate
    {I : Type*} [Fintype I] (parameters : Parameters) (w : I → GraphNonreal)
    (z : MassMarkedSample ν) :
    finiteJetExterior (finiteValueJet (fun i => (w i).val)
      (massRawCoordinate ν hm parameters z) (massRawCoordinateDerivative ν hm parameters z)) =
      fun i => ((massExterior ν hm parameters z).1 (w i),(massExterior ν hm parameters z).2 (w i)) := by
  have hM (i : I) : finiteRawJetMatrix (finiteValueJet (fun i => (w i).val)
      (massRawCoordinate ν hm parameters z) (massRawCoordinateDerivative ν hm parameters z)) i false =
      massMarkedMatrix ν hm parameters (w i).val z := by
    ext a b
    simp [finiteRawJetMatrix,finiteValueJet,massRawCoordinate,(w i).property]
  have hL (i : I) : finiteRawJetMatrix (finiteValueJet (fun i => (w i).val)
      (massRawCoordinate ν hm parameters z) (massRawCoordinateDerivative ν hm parameters z)) i true =
      massMarkedDerivative ν hm parameters (w i).val z := by
    ext a b
    simp [finiteRawJetMatrix,finiteValueJet,massRawCoordinateDerivative,(w i).property]
  funext i
  change (rawExteriorScalar _ _ _,rawExterior _) = _
  rw [hM,hL]
  rcases z with ⟨a,z⟩
  simp only [finiteJetExterior,finiteRawJetMatrix,finiteValueJet,massRawCoordinate,
    massRawCoordinateDerivative,(w i).property,↓reduceIte,
    massExterior,gaussianExterior,gaussianExteriorJet,valueOfJet,jetOfRaw,
    constructedScalar,constructedMatrix,constructedDerivative,
    massMarkedMatrix,massMarkedDerivative,massCenteredField,massScalarState,stratumSampleValue,
    stratumPresentation_scalar,Bool.false_eq_true,↓reduceIte]
  rfl

theorem finiteJetExterior_massRawCoordinate_law
    {I : Type*} [Fintype I] (parameters : Parameters) (w : I → GraphNonreal) :
    Measure.map finiteJetExterior
      (Measure.map (fun z => finiteValueJet (fun i => (w i).val)
        (massRawCoordinate ν hm parameters z) (massRawCoordinateDerivative ν hm parameters z))
        (massMarkedLaw ν parameters)) =
      Measure.map (fun z => fun i => ((massExterior ν hm parameters z).1 (w i),
        (massExterior ν hm parameters z).2 (w i))) (massMarkedLaw ν parameters) := by
  rw [Measure.map_map measurable_finiteJetExterior
    (measurable_finiteValueJet (fun i => (w i).val) _ _
      (measurable_massRawCoordinate ν hm parameters)
      (measurable_massRawCoordinateDerivative ν hm parameters))]
  congr 1
  exact funext (finiteJetExterior_massRawCoordinate ν hm parameters w)

end GeneralizedBulk.Gaussian
