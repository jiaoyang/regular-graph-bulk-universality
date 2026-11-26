import GeneralizedBulk.Graph.SpectralPairSampling
import GeneralizedBulk.Graph.RawFieldMeanConvergence

/-! Exact transport of the constructed scalar/raw-matrix limit to the finite
uniform graph laws used by the genuine switching couplings. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped Topology
namespace GeneralizedBulk.Gaussian
open Graph
variable {V : Type*} [Fintype V]

def stateRawValues (w : V → GraphNonreal) (z : WindowFieldState V) : RawField V :=
  fun v => (anchoredNevanlinna z.1 (w v).val,z.2 v)

theorem continuous_stateRawValues (w : V → GraphNonreal) : Continuous (stateRawValues w) := by
  apply continuous_pi
  intro v
  exact ((continuous_anchoredNevanlinna (w v).property).comp continuous_fst).prodMk
    ((continuous_apply v).comp continuous_snd)

end GeneralizedBulk.Gaussian
namespace GeneralizedBulk.External.RegularSpectralData
open Graph GeneralizedBulk.Gaussian GeneralizedBulk.Analysis
variable {d : ℕ} {N : ℕ → ℕ} {Ω V : Type*} [MeasurableSpace Ω] [Fintype V]
variable (D : RegularSpectralData d N Ω)

/-- The actual raw field limit retains the full scalar state until the exact
uniform graph/proposal sampling transport has been performed. -/
theorem microscopicRawFieldLaw_converges_of_rawState
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hUniform : ∀ n,Measure.map (D.spectralRegularGraph n) P=regularGraphLaw (N n) d)
    (hd : 0 < d) (E center : ℝ) (parameters : Parameters) (r : ℕ → ℕ)
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hm : Integrable (fun s : AnchoredCountingState => ‖s.val.2‖) ν)
    (w : V → GraphNonreal)
    (hraw : External.WeakLawConverges
      (fun n => Measure.map (D.microscopicRawState (r n) E center parameters w)
        (P.prod (uniformOrientedProposals (N (r n)) d)))
      (Measure.map (massRawState ν hm parameters w) (massMarkedLaw ν parameters))) :
    External.WeakLawConverges
      (fun n => microscopicRawFieldLaw (d := d) (D.size_pos (r n)) E parameters.scale center parameters.scale_pos w)
      (Measure.map (fun z => fun v =>
        ((anchoredNevanlinna (massScalarState ν z) (w v).val,
          massMarkedMatrix ν hm parameters (w v).val z) : RawValue)) (massMarkedLaw ν parameters)) := by
  have hw := weakLaw_map _ _ hraw (stateRawValues w) (continuous_stateRawValues w)
  have hsource (n) : Measure.map (stateRawValues w)
      (Measure.map (D.microscopicRawState (r n) E center parameters w)
        (P.prod (uniformOrientedProposals (N (r n)) d))) =
      microscopicRawFieldLaw (d := d) (D.size_pos (r n)) E parameters.scale center parameters.scale_pos w := by
    rw [Measure.map_map (continuous_stateRawValues w).measurable
      (D.measurable_microscopicRawState (r n) E center parameters w)]
    exact (D.microscopicRawFieldLaw_eq_spectral P hUniform (r n) hd E parameters.scale center parameters.scale_pos w).symm
  have htarget : Measure.map (stateRawValues w)
      (Measure.map (massRawState ν hm parameters w) (massMarkedLaw ν parameters)) =
      Measure.map (fun z => fun v =>
        ((anchoredNevanlinna (massScalarState ν z) (w v).val,
          massMarkedMatrix ν hm parameters (w v).val z) : RawValue)) (massMarkedLaw ν parameters) := by
    rw [Measure.map_map (continuous_stateRawValues w).measurable (measurable_massRawState ν hm parameters w)]
    rfl
  simpa only [hsource,htarget] using hw

/-- A single spectral value is a continuous marginal of the actual common
raw field, so the height-normalization coupling theorem applies directly. -/
theorem microscopicRawLaw_converges_of_rawState
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hUniform : ∀ n,Measure.map (D.spectralRegularGraph n) P=regularGraphLaw (N n) d)
    (hd : 0 < d) (E center : ℝ) (parameters : Parameters) (r : ℕ → ℕ)
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hm : Integrable (fun s : AnchoredCountingState => ‖s.val.2‖) ν)
    (w : GraphNonreal)
    (hraw : External.WeakLawConverges
      (fun n => Measure.map (D.microscopicRawState (r n) E center parameters (fun _ : Unit => w))
        (P.prod (uniformOrientedProposals (N (r n)) d)))
      (Measure.map (massRawState ν hm parameters (fun _ : Unit => w)) (massMarkedLaw ν parameters))) :
    External.WeakLawConverges
      (fun n => microscopicRawLaw (d := d) (D.size_pos (r n)) E parameters.scale center parameters.scale_pos w)
      (Measure.map (fun z =>
        ((anchoredNevanlinna (massScalarState ν z) w.val,
          massMarkedMatrix ν hm parameters w.val z) : RawValue)) (massMarkedLaw ν parameters)) := by
  have hw := D.microscopicRawFieldLaw_converges_of_rawState P hUniform hd E center parameters r ν hm (fun _ : Unit => w) hraw
  have he := weakLaw_map _ _ hw (fun z : RawField Unit => z ()) (continuous_apply ())
  have hsource (n) : Measure.map (fun z : RawField Unit => z ())
      (microscopicRawFieldLaw (d := d) (D.size_pos (r n)) E parameters.scale center parameters.scale_pos (fun _ : Unit => w)) =
      microscopicRawLaw (d := d) (D.size_pos (r n)) E parameters.scale center parameters.scale_pos w := by
    rw [microscopicRawFieldLaw,Measure.map_map (continuous_apply ()).measurable (measurable_of_finite _)]
    rfl
  have htarget : Measure.map (fun z : RawField Unit => z ())
      (Measure.map (fun z => fun _ : Unit =>
        ((anchoredNevanlinna (massScalarState ν z) w.val,massMarkedMatrix ν hm parameters w.val z) : RawValue))
        (massMarkedLaw ν parameters)) =
      Measure.map (fun z =>
        ((anchoredNevanlinna (massScalarState ν z) w.val,massMarkedMatrix ν hm parameters w.val z) : RawValue))
        (massMarkedLaw ν parameters) := by
    have hm' : Measurable (fun z : MassMarkedSample ν => fun _ : Unit =>
        ((anchoredNevanlinna (massScalarState ν z) w.val,massMarkedMatrix ν hm parameters w.val z) : RawValue)) :=
      (continuous_stateRawValues (fun _ : Unit => w)).measurable.comp
        (measurable_massRawState ν hm parameters (fun _ : Unit => w))
    rw [Measure.map_map (continuous_apply ()).measurable hm']
    rfl
  simpa only [hsource,htarget] using he

end GeneralizedBulk.External.RegularSpectralData
