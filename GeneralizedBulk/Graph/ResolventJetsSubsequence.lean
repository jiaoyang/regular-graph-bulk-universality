import GeneralizedBulk.External.RegularSpectralReindex
import GeneralizedBulk.Graph.StratifiedJetConvergence
import GeneralizedBulk.Graph.PairedRawValues
import GeneralizedBulk.Analysis.VanishingAffineError

/-! The actual derivative-jet theorem along arbitrary strict scalar subsequences. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped Topology
namespace GeneralizedBulk.External.RegularSpectralData
open Graph GeneralizedBulk.Gaussian GeneralizedBulk.Analysis
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

@[simp] theorem reindex_microscopicCountingState (r : ℕ → ℕ) (hr : StrictMono r)
    (n : ℕ) (ω : Ω) (E sigma center : ℝ) :
    (D.reindex r hr).microscopicCountingState n ω E sigma center =
      D.microscopicCountingState (r n) ω E sigma center := rfl

@[simp] theorem reindex_microscopicRawState {I : Type*} [Fintype I]
    (r : ℕ → ℕ) (hr : StrictMono r) (n : ℕ) (E center : ℝ) (parameters : Parameters)
    (w : I → GraphNonreal) :
    (D.reindex r hr).microscopicRawState n E center parameters w =
      D.microscopicRawState (r n) E center parameters w := rfl

@[simp] theorem reindex_rawCoordinateExtension (r : ℕ → ℕ) (hr : StrictMono r)
    (n : ℕ) (E sigma center : ℝ) :
    (D.reindex r hr).rawCoordinateExtension n E sigma center =
      D.rawCoordinateExtension (r n) E sigma center := rfl

@[simp] theorem reindex_rawCoordinateDerivative (r : ℕ → ℕ) (hr : StrictMono r)
    (n : ℕ) (E sigma : ℝ) :
    (D.reindex r hr).rawCoordinateDerivative n E sigma =
      D.rawCoordinateDerivative (r n) E sigma := rfl

theorem paired_raw_values_converge_of_rawState_subsequence
    {I : Type*} [Fintype I] (r : ℕ → ℕ) (hr : StrictMono r)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hm : Integrable (fun s : AnchoredCountingState => ‖s.val.2‖) ν)
    (parameters : Parameters) (E center : ℝ) (w : I → GraphNonreal) (R : ℕ)
    (hraw : External.WeakLawConverges
      (fun n => (P.prod (uniformOrientedProposals (N (r n)) d)).map
        (D.microscopicRawState (r n) E center parameters (pairedSpectral w R)))
      ((massMarkedLaw ν parameters).map (massRawState ν hm parameters (pairedSpectral w R)))) :
    External.WeakLawConverges
      (fun n => (P.prod (uniformOrientedProposals (N (r n)) d)).map (fun z =>
        finitePairedValues (fun i => (w i).val) (1/((R : ℝ)+1))
          (D.rawCoordinateExtension (r n) E parameters.scale center z)))
      ((massMarkedLaw ν parameters).map (fun z =>
        finitePairedValues (fun i => (w i).val) (1/((R : ℝ)+1))
          (massRawCoordinate ν hm parameters z))) := by
  exact (D.reindex r hr).paired_raw_values_converge_of_rawState P ν hm parameters E center w R hraw

theorem weakLaw_rawValueJet_mass_subsequence
    {I : Type*} [Fintype I] (r : ℕ → ℕ) (hr : StrictMono r)
    (P : Measure Ω) [IsProbabilityMeasure P] (hd : 0 < d)
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hm : Integrable (fun s : AnchoredCountingState => ‖s.val.2‖) ν)
    (parameters : Parameters) (E center : ℝ) (w : I → GraphNonreal)
    (hvalues : ∀ R : ℕ,External.WeakLawConverges
      (fun n => (P.prod (uniformOrientedProposals (N (r n)) d)).map (fun z =>
        finitePairedValues (fun i => (w i).val) (1/((R : ℝ)+1))
          (D.rawCoordinateExtension (r n) E parameters.scale center z)))
      ((massMarkedLaw ν parameters).map (fun z =>
        finitePairedValues (fun i => (w i).val) (1/((R : ℝ)+1))
          (massRawCoordinate ν hm parameters z))))
    (htight : ∀ δ : ℝ,0 < δ → ∃ A : ℝ,0 < A ∧ ∀ n,
      P.real {ω | A < ‖(D.microscopicCountingState (r n) ω E parameters.scale center).val.2‖} ≤ δ) :
    External.WeakLawConverges
      (fun n => (P.prod (uniformOrientedProposals (N (r n)) d)).map (fun z =>
        finiteValueJet (fun i => (w i).val) (D.rawCoordinateExtension (r n) E parameters.scale center z)
          (D.rawCoordinateDerivative (r n) E parameters.scale z)))
      ((massMarkedLaw ν parameters).map (fun z =>
        finiteValueJet (fun i => (w i).val) (massRawCoordinate ν hm parameters z)
          (massRawCoordinateDerivative ν hm parameters z))) := by
  exact (D.reindex r hr).weakLaw_rawValueJet_mass P hd ν hm parameters E center w hvalues htight

/-- Weak scalar convergence itself supplies the uniform finite-anchor tails
needed to pass from paired values to actual spectral derivatives. -/
theorem microscopic_anchor_uniform_tails_of_scalar_weak
    (P : Measure Ω) [IsProbabilityMeasure P] (r : ℕ → ℕ)
    (E sigma center : ℝ) (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hscalar : External.WeakLawConverges
      (fun n => P.map (fun ω => D.microscopicCountingState (r n) ω E sigma center)) ν) :
    ∀ δ : ℝ,0 < δ → ∃ A : ℝ,0 < A ∧ ∀ n,
      P.real {ω | A < ‖(D.microscopicCountingState (r n) ω E sigma center).val.2‖} ≤ δ := by
  let anchor := fun s : AnchoredCountingState => s.val.2
  have hc : Continuous anchor := continuous_snd.comp continuous_subtype_val
  letI : IsProbabilityMeasure (ν.map anchor) := isProbabilityMeasure_map hc.measurable.aemeasurable
  have hw := weakLaw_map _ _ hscalar anchor hc
  have hweak : External.WeakLawConverges
      (fun n => P.map (fun ω => (D.microscopicCountingState (r n) ω E sigma center).val.2)) (ν.map anchor) := by
    simpa only [Measure.map_map hc.measurable (D.measurable_microscopicCountingState _ E sigma center)] using hw
  have ht := uniform_norm_tails_of_weakLaw_map (fun _ : ℕ => P)
    (fun n ω => (D.microscopicCountingState (r n) ω E sigma center).val.2)
    (fun n => hc.measurable.comp (D.measurable_microscopicCountingState (r n) E sigma center))
    (ν.map anchor) hweak
  intro δ hδ
  obtain ⟨A,hA⟩ := ht (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ)
  refine ⟨max A 1,lt_of_lt_of_le (by norm_num) (le_max_right A 1),fun n => ?_⟩
  have hsub : {ω | max A 1 < ‖(D.microscopicCountingState (r n) ω E sigma center).val.2‖} ⊆
      {ω | A < ‖(D.microscopicCountingState (r n) ω E sigma center).val.2‖} :=
    fun ω hω => (le_max_left A 1).trans_lt hω
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top ((measure_mono hsub).trans (hA n))
  simpa only [ENNReal.toReal_ofReal hδ.le] using hh

end GeneralizedBulk.External.RegularSpectralData
