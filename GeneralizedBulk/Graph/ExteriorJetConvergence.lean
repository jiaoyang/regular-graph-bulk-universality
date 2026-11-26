import GeneralizedBulk.Graph.FiniteJetExterior
import GeneralizedBulk.Gaussian.StratifiedJetExterior
import GeneralizedBulk.Gaussian.InfiniteInvertibility
import GeneralizedBulk.Exterior.JetLawConvergence
import GeneralizedBulk.Exterior.FiniteValueLaw

/-! The actual finite raw jets converge to the literal exterior finite laws.
Inversion is justified by proved infinite-model positivity after normalization. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped Topology ENNReal
namespace GeneralizedBulk.External.RegularSpectralData
open Graph GeneralizedBulk.Gaussian GeneralizedBulk.Exterior GeneralizedBulk.Analysis
variable {d : ℕ} {N : ℕ → ℕ} {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
variable (D : RegularSpectralData d N Ω)

set_option maxHeartbeats 2000000 in
theorem microscopicExterior_finite_converges_of_rawJets
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hUniform : ∀ n,Measure.map (D.spectralRegularGraph n) P=regularGraphLaw (N n) d)
    (hd : 0 < d) (r : ℕ → ℕ)
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hm : Integrable (fun s : AnchoredCountingState => ‖s.val.2‖) ν)
    (parameters : Parameters) (E center : ℝ) (w : I → GraphNonreal)
    (hlinear : ∀ᵐ s ∂ν,anchoredLinearCoefficient s=0)
    (hmass : ∀ᵐ s ∂ν,s.val.1.measure Set.univ=∞)
    (hjet : WeakLawConverges
      (fun n => (P.prod (uniformOrientedProposals (N (r n)) d)).map (fun z =>
        finiteValueJet (fun i => (w i).val) (D.rawCoordinateExtension (r n) E parameters.scale center z)
          (D.rawCoordinateDerivative (r n) E parameters.scale z)))
      ((massMarkedLaw ν parameters).map (fun z =>
        finiteValueJet (fun i => (w i).val) (massRawCoordinate ν hm parameters z)
          (massRawCoordinateDerivative ν hm parameters z)))) :
    WeakLawConverges
      (fun n => (edgePairLaw (N (r n)) d).map (fun s =>
        finiteValueEvaluation w (microscopicEdgePairExterior (D.size_pos (r n)) E parameters.scale
          center parameters.scale_pos s)))
      ((massMarkedLaw ν parameters).map (fun z => finiteValueEvaluation w (massExterior ν hm parameters z))) := by
  let SN := fun n z => finiteValueJet (fun i => (w i).val)
    (D.rawCoordinateExtension (r n) E parameters.scale center z)
    (D.rawCoordinateDerivative (r n) E parameters.scale z)
  let T := fun z => finiteValueJet (fun i => (w i).val)
    (massRawCoordinate ν hm parameters z) (massRawCoordinateDerivative ν hm parameters z)
  let μ := fun n => (P.prod (uniformOrientedProposals (N (r n)) d)).map (SN n)
  let ξ := (massMarkedLaw ν parameters).map T
  letI : ∀ n,IsProbabilityMeasure (uniformOrientedProposals (N (r n)) d) :=
    fun n => uniformOrientedProposals_isProbability _ _ (D.size_pos (r n)) hd
  have hSN (n : ℕ) : Measurable (SN n) := measurable_finiteValueJet _ _ _
    (D.measurable_rawCoordinateExtension (r n) E parameters.scale center)
    (D.measurable_rawCoordinateDerivative (r n) E parameters.scale)
  have hT : Measurable T := measurable_finiteValueJet _ _ _
    (measurable_massRawCoordinate ν hm parameters) (measurable_massRawCoordinateDerivative ν hm parameters)
  letI : ∀ n,IsProbabilityMeasure (μ n) := fun n => isProbabilityMeasure_map (hSN n).aemeasurable
  letI : IsProbabilityMeasure ξ := isProbabilityMeasure_map hT.aemeasurable
  have hpred : MeasurableSet {v : FiniteRawJet I | ∀ i,IsUnit (finiteRawJetMatrix v i false)} := by
    have heq : {v : FiniteRawJet I | ∀ i,IsUnit (finiteRawJetMatrix v i false)} =
        ⋂ i,{v : FiniteRawJet I | (finiteRawJetMatrix v i false).det ≠ 0} := by
      ext v
      simp only [Set.mem_setOf_eq,Set.mem_iInter,Matrix.isUnit_iff_isUnit_det,isUnit_iff_ne_zero]
    rw [heq]
    exact MeasurableSet.iInter (fun i =>
      (isOpen_ne_fun (continuous_finiteRawJetMatrix i false).matrix_det continuous_const).measurableSet)
  have hu : ∀ᵐ v ∂ξ,∀ i,IsUnit (finiteRawJetMatrix v i false) := by
    apply (ae_map_iff hT.aemeasurable hpred).mpr
    filter_upwards [massMarkedMatrix_ae_isUnit ν hm parameters hlinear hmass] with z hz
    intro i
    have heq : finiteRawJetMatrix (T z) i false=massMarkedMatrix ν hm parameters (w i).val z := by
      ext a b
      simp only [finiteRawJetMatrix,T,finiteValueJet,Bool.false_eq_true,↓reduceIte,
        massRawCoordinate,(w i).property]
    rw [heq]
    exact hz (w i)
  have hmap := weakLaw_finiteJetExterior μ ξ hjet hu
  have hsource (n : ℕ) : (μ n).map finiteJetExterior =
      (edgePairLaw (N (r n)) d).map (fun s => finiteValueEvaluation w
        (microscopicEdgePairExterior (D.size_pos (r n)) E parameters.scale center parameters.scale_pos s)) := by
    rw [show μ n=(P.prod (uniformOrientedProposals (N (r n)) d)).map (SN n) from rfl,
      Measure.map_map measurable_finiteJetExterior (hSN n)]
    have heq : finiteJetExterior ∘ SN n = fun z => finiteValueEvaluation w
        (microscopicEdgePairExterior (D.size_pos (r n)) E parameters.scale center parameters.scale_pos
          (D.spectralPairSample (r n) z)) := by
      funext z
      exact D.finiteJetExterior_rawCoordinateExtension (r n) E parameters.scale center parameters.scale_pos w z
    rw [heq]
    exact D.spectralPairSample_map_observable (V := I → RawValue) P hUniform (r n) hd
      (fun s => finiteValueEvaluation w (microscopicEdgePairExterior (D.size_pos (r n))
        E parameters.scale center parameters.scale_pos s))
  have htarget : ξ.map finiteJetExterior=(massMarkedLaw ν parameters).map
      (fun z => finiteValueEvaluation w (massExterior ν hm parameters z)) := by
    rw [show ξ=(massMarkedLaw ν parameters).map T from rfl,
      Measure.map_map measurable_finiteJetExterior hT]
    congr 1
    funext z
    exact finiteJetExterior_massRawCoordinate ν hm parameters w z
  simpa only [hsource,htarget] using hmap

/- The actual finite switch symmetry, its vanishing rejection probability,
and the proved exterior mapping theorem give the literal complete exterior
law symmetry used by the loop characterization. -/
set_option maxHeartbeats 2500000 in
theorem massExterior_switching_of_rawJet_limits
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hUniform : ∀ n,Measure.map (D.spectralRegularGraph n) P=regularGraphLaw (N n) d)
    (hd : 0 < d) (r : ℕ → ℕ) (hr : StrictMono r)
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hm : Integrable (fun s : AnchoredCountingState => ‖s.val.2‖) ν)
    (parameters : Parameters) (E center : ℝ)
    (hlinear : ∀ᵐ s ∂ν,anchoredLinearCoefficient s=0)
    (hmass : ∀ᵐ s ∂ν,s.val.1.measure Set.univ=∞)
    (hjet : ∀ S : Finset GraphNonreal,WeakLawConverges
      (fun n => (P.prod (uniformOrientedProposals (N (r n)) d)).map (fun z =>
        finiteValueJet (fun i : S => i.val.val) (D.rawCoordinateExtension (r n) E parameters.scale center z)
          (D.rawCoordinateDerivative (r n) E parameters.scale z)))
      ((massMarkedLaw ν parameters).map (fun z =>
        finiteValueJet (fun i : S => i.val.val) (massRawCoordinate ν hm parameters z)
          (massRawCoordinateDerivative ν hm parameters z)))) :
    Measure.map (action GeneralizedSwitching.endpointPermutation)
      (Measure.map (massExterior ν hm parameters) (massMarkedLaw ν parameters)) =
      Measure.map (massExterior ν hm parameters) (massMarkedLaw ν parameters) := by
  letI : Nonempty Ω := ProbabilityMeasure.nonempty (⟨P,inferInstance⟩ : ProbabilityMeasure Ω)
  letI : ∀ n,Nonempty (RegularGraph (N (r n)) d) :=
    fun n => ⟨D.spectralRegularGraph (r n) (Classical.arbitrary Ω)⟩
  letI : IsProbabilityMeasure (Measure.map (massExterior ν hm parameters) (massMarkedLaw ν parameters)) :=
    isProbabilityMeasure_map (measurable_massExterior ν hm parameters).aemeasurable
  apply microscopicExterior_limit_switch_invariant (fun n => N (r n))
    (fun n => D.size_pos (r n)) (D.size_tendsto.comp hr.tendsto_atTop) d hd
    E parameters.scale center parameters.scale_pos
    (Measure.map (massExterior ν hm parameters) (massMarkedLaw ν parameters))
  intro S
  have hw := D.microscopicExterior_finite_converges_of_rawJets P hUniform hd r ν hm parameters
    E center (fun i : S => i.val) hlinear hmass (hjet S)
  have hsource (n : ℕ) : Measure.map (exteriorProjection S)
      (Measure.map (microscopicEdgePairExterior (d := d) (D.size_pos (r n)) E parameters.scale center parameters.scale_pos)
        (edgePairLaw (N (r n)) d)) =
      (edgePairLaw (N (r n)) d).map (fun s => finiteValueEvaluation (fun i : S => i.val)
        (microscopicEdgePairExterior (D.size_pos (r n)) E parameters.scale center parameters.scale_pos s)) := by
    rw [Measure.map_map (measurable_exteriorProjection S) (measurable_of_finite _)]
    rfl
  have htarget : Measure.map (exteriorProjection S)
      (Measure.map (massExterior ν hm parameters) (massMarkedLaw ν parameters)) =
      (massMarkedLaw ν parameters).map (fun z =>
        finiteValueEvaluation (fun i : S => i.val) (massExterior ν hm parameters z)) := by
    rw [Measure.map_map (measurable_exteriorProjection S) (measurable_massExterior ν hm parameters)]
    rfl
  simpa only [hsource,htarget] using hw

end GeneralizedBulk.External.RegularSpectralData
