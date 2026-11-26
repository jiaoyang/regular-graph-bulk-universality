import GeneralizedBulk.Graph.ResolventJets
import GeneralizedBulk.Graph.SpectralPairSampling
import GeneralizedBulk.Exterior.FiniteJetCoordinates

/-! The actual finite raw jet transform is exactly the microscopic graph
exterior already known to have approximate switching invariance. -/
noncomputable section
open MeasureTheory BourgadeHuang
namespace GeneralizedBulk.External.RegularSpectralData
open Graph Exterior Analysis
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

theorem finiteJetExterior_rawCoordinateExtension
    {I : Type*} [Fintype I] (n : ℕ) (E sigma center : ℝ) (hsigma : 0 < sigma)
    (w : I → GraphNonreal) (z : Ω × ProposalSample (N n) d) :
    finiteJetExterior (finiteValueJet (fun i => (w i).val)
      (D.rawCoordinateExtension n E sigma center z) (D.rawCoordinateDerivative n E sigma z)) =
      fun i => ((microscopicEdgePairExterior (D.size_pos n) E sigma center hsigma
        (D.spectralPairSample n z)).1 (w i),
        (microscopicEdgePairExterior (D.size_pos n) E sigma center hsigma
          (D.spectralPairSample n z)).2 (w i)) := by
  funext a
  let G := D.simpleGraph n z.1
  let e := D.proposalEndpoints n z.1 z.2
  let u := microscopicParameter (N n) (D.size_pos n) E sigma hsigma (w a)
  have hM : finiteRawJetMatrix (finiteValueJet (fun i => (w i).val)
      (D.rawCoordinateExtension n E sigma center z) (D.rawCoordinateDerivative n E sigma z)) a false =
      graphBoundary G e u.val := by
    ext i j
    change D.rawCoordinateExtension n E sigma center z (w a).val (Sum.inr (i,j)) = _
    rw [D.rawCoordinateExtension_matrix n z.1 z.2 E sigma center hsigma (w a) i j]
    simp only [graphBoundary,G,e,D.graphResolvent_simpleGraph]
    rfl
  have hL : finiteRawJetMatrix (finiteValueJet (fun i => (w i).val)
      (D.rawCoordinateExtension n E sigma center z) (D.rawCoordinateDerivative n E sigma z)) a true =
      (microscopicStep (N n) sigma : ℂ) • graphBoundaryDerivative G e u.val := by
    ext i j
    change D.rawCoordinateDerivative n E sigma z (w a).val (Sum.inr (i,j)) = _
    rw [D.rawCoordinateDerivative_matrix n z.1 z.2 E sigma center hsigma (w a) i j]
    simp only [graphBoundaryDerivative,G,e,D.graphResolvent_simpleGraph,Matrix.smul_apply,smul_eq_mul]
    rfl
  have hs : D.rawCoordinateExtension n E sigma center z (w a).val (Sum.inl ()) =
      (((N n : ℂ)⁻¹*Matrix.trace (graphResolvent G u.val)-(center : ℂ))/(sigma : ℂ)) := by
    rw [D.rawCoordinateExtension_scalar n z.1 z.2 E sigma center hsigma (w a)]
    simp only [microscopicScalar,scalarResolvent,G,D.graphResolvent_simpleGraph]
    rfl
  have he : edgePairExterior (D.spectralPairSample n z) = graphExterior G e := by
    unfold edgePairExterior
    rw [show (D.spectralPairSample n z).val=(G,e) from D.proposalFiberEquiv_val n z.1 z.2]
  change (rawExteriorScalar _ _ _,rawExterior _) = _
  rw [hM,hL]
  simp only [finiteValueJet,Bool.false_eq_true,↓reduceIte]
  rw [hs]
  simp only [microscopicEdgePairExterior,he]
  apply Prod.ext
  · exact (microscopicExterior_scalar_formula G e (N n) (D.size_pos n) E sigma center hsigma (w a)).symm
  · rfl

theorem finiteJetExterior_rawCoordinateExtension_law
    {I : Type*} [Fintype I] (P : Measure Ω) [IsProbabilityMeasure P]
    (hUniform : ∀ n,Measure.map (D.spectralRegularGraph n) P=regularGraphLaw (N n) d)
    (hd : 0 < d) (n : ℕ) (E sigma center : ℝ) (hsigma : 0 < sigma)
    (w : I → GraphNonreal) :
    Measure.map finiteJetExterior
      (Measure.map (fun z => finiteValueJet (fun i => (w i).val)
        (D.rawCoordinateExtension n E sigma center z) (D.rawCoordinateDerivative n E sigma z))
        (P.prod (uniformOrientedProposals (N n) d))) =
      Measure.map (fun s : EdgePairState (N n) d => fun i =>
        ((microscopicEdgePairExterior (D.size_pos n) E sigma center hsigma s).1 (w i),
          (microscopicEdgePairExterior (D.size_pos n) E sigma center hsigma s).2 (w i)))
        (edgePairLaw (N n) d) := by
  rw [Measure.map_map measurable_finiteJetExterior
    (measurable_finiteValueJet (fun i => (w i).val) _ _
      (D.measurable_rawCoordinateExtension n E sigma center)
      (D.measurable_rawCoordinateDerivative n E sigma))]
  have he : finiteJetExterior ∘ (fun z => finiteValueJet (fun i => (w i).val)
      (D.rawCoordinateExtension n E sigma center z) (D.rawCoordinateDerivative n E sigma z)) =
      fun z => fun i => ((microscopicEdgePairExterior (D.size_pos n) E sigma center hsigma
        (D.spectralPairSample n z)).1 (w i),
        (microscopicEdgePairExterior (D.size_pos n) E sigma center hsigma
          (D.spectralPairSample n z)).2 (w i)) :=
    funext (fun z => D.finiteJetExterior_rawCoordinateExtension n E sigma center hsigma w z)
  rw [he]
  exact D.spectralPairSample_map_observable P hUniform n hd
    (fun s : EdgePairState (N n) d => fun i =>
      ((microscopicEdgePairExterior (D.size_pos n) E sigma center hsigma s).1 (w i),
        (microscopicEdgePairExterior (D.size_pos n) E sigma center hsigma s).2 (w i)))

end GeneralizedBulk.External.RegularSpectralData
