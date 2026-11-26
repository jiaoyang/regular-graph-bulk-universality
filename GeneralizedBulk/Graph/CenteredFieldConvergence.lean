import GeneralizedBulk.Graph.CenteredField
import GeneralizedBulk.Gaussian.FieldCoordinates
import GeneralizedBulk.Gaussian.StratifiedWindowProbability
import GeneralizedBulk.Analysis.CoordinateTruncation

/-! Genuine full-field weak convergence from the proved finite-window laws
and literal finite-graph entrywise approximation errors. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped Topology
namespace GeneralizedBulk.External.RegularSpectralData
open Graph GeneralizedBulk.Gaussian GeneralizedBulk.Analysis
variable {d : ℕ} {N : ℕ → ℕ} {Ω V : Type*} [MeasurableSpace Ω] [Fintype V]
variable (D : RegularSpectralData d N Ω)

set_option maxHeartbeats 1500000 in
theorem microscopicCenteredState_converges_of_window_tails
    (r : ℕ → ℕ) (P : Measure Ω) [IsProbabilityMeasure P] (hd : 0 < d)
    (E center : ℝ) (parameters : Parameters) (w : V → GraphNonreal)
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hm : Integrable (fun s : AnchoredCountingState => ‖s.val.2‖) ν)
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop)
    (hfinite : ∀ k,External.WeakLawConverges
      (fun n => Measure.map (D.microscopicWindowState (r n) E center parameters (R k) w)
        (P.prod (uniformOrientedProposals (N (r n)) d)))
      (Measure.map (massWindowState ν parameters (R k) (fun v => ((w v).val,false)))
        (massMarkedLaw ν parameters)))
    (hpre : ∀ v i j,∀ ε δ : ℝ,0 < ε → 0 < δ →
      ∃ k0,∀ k,k0 ≤ k → ∀ᶠ n in atTop,
        (P.prod (uniformOrientedProposals (N (r n)) d)).real {z | ε <
          ‖D.microscopicCenteredMatrix (r n) E parameters (w v) z i j -
            D.microscopicWindowMatrix (r n) E parameters (R k) (w v) z i j‖} ≤ δ) :
    External.WeakLawConverges
      (fun n => Measure.map (D.microscopicCenteredState (r n) E center parameters w)
        (P.prod (uniformOrientedProposals (N (r n)) d)))
      (Measure.map (massCenteredState ν hm parameters (fun v => ((w v).val,false)))
        (massMarkedLaw ν parameters)) := by
  letI : PolishSpace AnchoredCountingState := isClosed_validAnchoredCountingState.polishSpace
  letI : MetricSpace AnchoredCountingState := TopologicalSpace.metrizableSpaceMetric AnchoredCountingState
  let Pn := fun n => P.prod (uniformOrientedProposals (N (r n)) d)
  letI : ∀ n,IsProbabilityMeasure (uniformOrientedProposals (N (r n)) d) :=
    fun n => uniformOrientedProposals_isProbability (N (r n)) d (D.size_pos (r n)) hd
  letI : ∀ n,IsProbabilityMeasure (Pn n) := fun n => inferInstance
  let F := windowStateCoordinates V
  have hF : Measurable (F : WindowFieldState V → AnchoredCountingState × (FieldCoordinate V → ℂ)) :=
    F.continuous_toFun.measurable
  have hFinv : Measurable (F.symm : AnchoredCountingState × (FieldCoordinate V → ℂ) → WindowFieldState V) :=
    F.symm.continuous_toFun.measurable
  let X := fun n => F ∘ D.microscopicCenteredState (r n) E center parameters w
  let XR := fun k n => F ∘ D.microscopicWindowState (r n) E center parameters (R k) w
  let YR := fun k => F ∘ massWindowState ν parameters (R k) (fun v => ((w v).val,false))
  let Y := F ∘ massCenteredState ν hm parameters (fun v => ((w v).val,false))
  have hX (n) : Measurable (X n) := hF.comp
    (D.measurable_microscopicCenteredState (r n) E center parameters w)
  have hXR (k n) : Measurable (XR k n) := hF.comp
    (D.measurable_microscopicWindowState (r n) E center parameters (R k) w)
  have hYR (k) : Measurable (YR k) := hF.comp
    (measurable_massWindowState ν parameters (R k) (fun v => ((w v).val,false)))
  have hY : Measurable Y := hF.comp
    (measurable_massCenteredState ν hm parameters (fun v => ((w v).val,false)))
  have hfinite' (k) : External.WeakLawConverges
      (fun n => (Pn n).map (XR k n)) ((massMarkedLaw ν parameters).map (YR k)) := by
    have hw := weakLaw_map _ _ (hfinite k) F F.continuous_toFun
    simpa only [Measure.map_map (g := (F : WindowFieldState V → AnchoredCountingState × (FieldCoordinate V → ℂ))) hF
      (D.measurable_microscopicWindowState _ E center parameters (R k) w),
      Measure.map_map (g := (F : WindowFieldState V → AnchoredCountingState × (FieldCoordinate V → ℂ))) hF
        (measurable_massWindowState ν parameters (R k) (fun v => ((w v).val,false)))] using hw
  have hpre' : ∀ i : FieldCoordinate V,∀ ε δ : ℝ,0 < ε → 0 < δ →
      ∃ k0,∀ k,k0 ≤ k → ∀ᶠ n in atTop,
        (Pn n).real {x | ε < dist ((X n x).2 i) ((XR k n x).2 i)} ≤ δ := by
    rintro ⟨v,i,j⟩ ε δ hε hδ
    simpa only [dist_eq_norm] using hpre v i j ε δ hε hδ
  have htarget' : ∀ i : FieldCoordinate V,∀ ε δ : ℝ,0 < ε → 0 < δ →
      ∀ᶠ k in atTop,(massMarkedLaw ν parameters).real
        {x | ε < dist ((YR k x).2 i) ((Y x).2 i)} ≤ δ := by
    rintro ⟨v,i,j⟩ ε δ hε hδ
    simpa only [dist_eq_norm] using massWindow_entry_probability_tendsto_zero ν hm parameters R hR
      ((w v).val,false) i j ε δ hε hδ
  have hw := weakLaw_of_state_coordinate_truncations Pn (massMarkedLaw ν parameters)
    X XR YR Y hX hXR hYR hY (fun _ _ _ => rfl) (fun _ _ => rfl) hfinite' hpre' htarget'
  have hback := weakLaw_map _ _ hw F.symm F.symm.continuous_toFun
  have hleft (n) : Measure.map F.symm ((Pn n).map (X n)) =
      Measure.map (D.microscopicCenteredState (r n) E center parameters w) (Pn n) := by
    rw [Measure.map_map (g := (F.symm : AnchoredCountingState × (FieldCoordinate V → ℂ) → WindowFieldState V)) hFinv (hX n)]
    congr 1
  have hright : Measure.map F.symm ((massMarkedLaw ν parameters).map Y) =
      Measure.map (massCenteredState ν hm parameters (fun v => ((w v).val,false))) (massMarkedLaw ν parameters) := by
    rw [Measure.map_map (g := (F.symm : AnchoredCountingState × (FieldCoordinate V → ℂ) → WindowFieldState V)) hFinv hY]
    congr 1
  simpa only [hleft,hright] using hback

end GeneralizedBulk.External.RegularSpectralData
