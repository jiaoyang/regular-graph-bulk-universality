import GeneralizedBulk.Graph.StratifiedJetConvergence
import GeneralizedBulk.Graph.RawFieldMeanConvergence

/-! The finite paired value laws used for spectral differentiation are
continuous marginals of the already constructed state/raw-field laws. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped Topology
namespace GeneralizedBulk.Gaussian
open Graph Analysis Exterior

def pairedSpectral {I : Type*} (w : I → GraphNonreal) (R : ℕ) : (I × Bool) → GraphNonreal :=
  fun t => if t.2 then horizontalShift (w t.1) R else w t.1

theorem pairedSpectral_val {I : Type*} (w : I → GraphNonreal) (R : ℕ) (t : I × Bool) :
    (pairedSpectral w R t).val = (w t.1).val + if t.2 then ((1/((R : ℝ)+1) : ℝ) : ℂ) else 0 := by
  rcases t with ⟨i,b⟩
  cases b <;> simp [pairedSpectral,horizontalShift,horizontalStep]

def stateRawCoordinates {V : Type*} (w : V → GraphNonreal) (z : WindowFieldState V) :
    V → RawComplexCoordinate → ℂ :=
  fun v => rawComplexCoordinate (anchoredNevanlinna z.1 (w v).val,z.2 v)

theorem continuous_stateRawCoordinates {V : Type*} (w : V → GraphNonreal) :
    Continuous (stateRawCoordinates w) := by
  apply continuous_pi
  intro v
  apply continuous_pi
  intro j
  cases j with
  | inl u => exact (continuous_anchoredNevanlinna (w v).property).comp continuous_fst
  | inr ij =>
    exact (continuous_apply ij.2).comp ((continuous_apply ij.1).comp
      ((continuous_apply v).comp continuous_snd))

end GeneralizedBulk.Gaussian
namespace GeneralizedBulk.External.RegularSpectralData
open Graph GeneralizedBulk.Gaussian GeneralizedBulk.Analysis
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

theorem paired_raw_values_converge_of_rawState
    {I : Type*} [Fintype I] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hm : Integrable (fun s : AnchoredCountingState => ‖s.val.2‖) ν)
    (parameters : Parameters) (E center : ℝ) (w : I → GraphNonreal) (R : ℕ)
    (hraw : External.WeakLawConverges
      (fun n => (P.prod (uniformOrientedProposals (N n) d)).map
        (D.microscopicRawState n E center parameters (pairedSpectral w R)))
      ((massMarkedLaw ν parameters).map (massRawState ν hm parameters (pairedSpectral w R)))) :
    External.WeakLawConverges
      (fun n => (P.prod (uniformOrientedProposals (N n) d)).map (fun z =>
        finitePairedValues (fun i => (w i).val) (1/((R : ℝ)+1))
          (D.rawCoordinateExtension n E parameters.scale center z)))
      ((massMarkedLaw ν parameters).map (fun z =>
        finitePairedValues (fun i => (w i).val) (1/((R : ℝ)+1))
          (massRawCoordinate ν hm parameters z))) := by
  have hw := weakLaw_map _ _ hraw (stateRawCoordinates (pairedSpectral w R))
    (continuous_stateRawCoordinates _)
  have hsource (n : ℕ) : stateRawCoordinates (pairedSpectral w R) ∘
      D.microscopicRawState n E center parameters (pairedSpectral w R) =
      fun z => finitePairedValues (fun i => (w i).val) (1/((R : ℝ)+1))
        (D.rawCoordinateExtension n E parameters.scale center z) := by
    funext z t j
    simp only [Function.comp_apply,finitePairedValues,← pairedSpectral_val w R t]
    cases j with
    | inl u =>
      cases u
      change anchoredNevanlinna (D.microscopicCountingState n z.1 E parameters.scale center)
        (pairedSpectral w R t).val = _
      rw [D.microscopicCountingState_scalar n z.1 E parameters.scale center parameters.scale_pos]
      exact (D.rawCoordinateExtension_scalar n z.1 z.2 E parameters.scale center parameters.scale_pos _).symm
    | inr ij =>
      exact (D.rawCoordinateExtension_matrix n z.1 z.2 E parameters.scale center parameters.scale_pos _ ij.1 ij.2).symm
  have htarget : stateRawCoordinates (pairedSpectral w R) ∘
      massRawState ν hm parameters (pairedSpectral w R) =
      fun z => finitePairedValues (fun i => (w i).val) (1/((R : ℝ)+1))
        (massRawCoordinate ν hm parameters z) := by
    funext z t j
    simp only [Function.comp_apply,finitePairedValues,← pairedSpectral_val w R t]
    cases j <;> simp only [stateRawCoordinates,massRawState,rawComplexCoordinate,
      massRawCoordinate,(pairedSpectral w R t).property,↓reduceIte] <;> rfl
  simpa only [Measure.map_map (continuous_stateRawCoordinates _).measurable
      (D.measurable_microscopicRawState _ E center parameters _),
    Measure.map_map (continuous_stateRawCoordinates _).measurable
      (measurable_massRawState ν hm parameters _),hsource,htarget] using hw

end GeneralizedBulk.External.RegularSpectralData
