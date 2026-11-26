import GeneralizedBulk.Graph.CenteredField
import GeneralizedBulk.Graph.FiniteMeanProbability
import GeneralizedBulk.Gaussian.FieldCoordinates
import GeneralizedBulk.Analysis.CoordinateTruncation

/-! Re-addition of the calibrated mean yields the actual raw physical
resolvent law. Its finite constant-mode correction vanishes in probability
from scalar weak convergence, without prelimit scalar moment assumptions. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped Topology
namespace GeneralizedBulk.Gaussian
open Graph
variable {V : Type*} [Fintype V]

def readdMeanState (parameters : Parameters) (w : V → GraphNonreal)
    (z : WindowFieldState V) : WindowFieldState V :=
  (z.1,fun v => Marked.mean parameters id (w v).val z.1+z.2 v)

theorem continuous_readdMeanState (parameters : Parameters) (w : V → GraphNonreal) :
    Continuous (readdMeanState parameters w) := by
  apply continuous_fst.prodMk
  apply continuous_pi
  intro v
  have hc : Continuous (fun s : AnchoredCountingState => Marked.mean parameters id (w v).val s) :=
    (continuous_calibratedMean parameters).comp (continuous_anchoredNevanlinna (w v).property)
  exact (hc.comp continuous_fst).add ((continuous_apply v).comp continuous_snd)

variable (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
variable (hm : Integrable (fun s : AnchoredCountingState => ‖s.val.2‖) ν)

def massRawState (parameters : Parameters) (w : V → GraphNonreal) (z : MassMarkedSample ν) : WindowFieldState V :=
  (massScalarState ν z,fun v => massMarkedMatrix ν hm parameters (w v).val z)

theorem measurable_massRawState (parameters : Parameters) (w : V → GraphNonreal) :
    Measurable (massRawState ν hm parameters w) :=
  (continuous_readdMeanState parameters w).measurable.comp
    (measurable_massCenteredState ν hm parameters (fun v => ((w v).val,false)))

end GeneralizedBulk.Gaussian

namespace GeneralizedBulk.External.RegularSpectralData
open Graph GeneralizedBulk.Gaussian GeneralizedBulk.Analysis GeneralizedSwitching Exterior
variable {d : ℕ} {N : ℕ → ℕ} {Ω V : Type*} [MeasurableSpace Ω] [Fintype V]
variable (D : RegularSpectralData d N Ω)

def microscopicRawMatrix (n : ℕ) (E : ℝ) (parameters : Parameters)
    (w : GraphNonreal) (z : Ω × ProposalSample (N n) d) : EndpointMatrix :=
  fun i j => D.resolvent n z.1
    (microscopicParameter (N n) (D.size_pos n) E parameters.scale parameters.scale_pos w).val
      (D.proposalEndpoints n z.1 z.2 i) (D.proposalEndpoints n z.1 z.2 j)

theorem measurable_microscopicRawMatrix (n : ℕ) (E : ℝ) (parameters : Parameters) (w : GraphNonreal) :
    Measurable (D.microscopicRawMatrix n E parameters w) := by
  change @Measurable _ (Fin 4 → Fin 4 → ℂ) _ (borel _) _
  rw [← @BorelSpace.measurable_eq (Fin 4 → Fin 4 → ℂ) _ MeasurableSpace.pi (by infer_instance)]
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  apply measurable_from_prod_countable
  intro t
  exact D.measurable_resolventProposalEntry n _
    (microscopicParameter (N n) (D.size_pos n) E parameters.scale parameters.scale_pos w).property i j t

def microscopicRawState (n : ℕ) (E center : ℝ) (parameters : Parameters)
    (w : V → GraphNonreal) (z : Ω × ProposalSample (N n) d) : WindowFieldState V :=
  (D.microscopicCountingState n z.1 E parameters.scale center,fun v => D.microscopicRawMatrix n E parameters (w v) z)

theorem measurable_microscopicRawState (n : ℕ) (E center : ℝ) (parameters : Parameters) (w : V → GraphNonreal) :
    Measurable (D.microscopicRawState n E center parameters w) :=
  ((D.measurable_microscopicCountingState n E parameters.scale center).comp measurable_fst).prodMk
    (measurable_pi_lambda _ (fun v => D.measurable_microscopicRawMatrix n E parameters (w v)))

set_option maxHeartbeats 3000000 in
theorem microscopicRawState_converges_of_centered
    (P : Measure Ω) [IsProbabilityMeasure P]
    (E : ℝ) (hd : 3 ≤ (d : ℝ)) (hbulk : E^2 < 4*((d : ℝ)-1))
    (r : ℕ → ℕ) (hr : StrictMono r) (w : V → GraphNonreal)
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hm : Integrable (fun s : AnchoredCountingState => ‖s.val.2‖) ν)
    (hcentered : let parameters := Parameters.regular d E hd hbulk
      WeakLawConverges
        (fun n => Measure.map (D.microscopicCenteredState (r n) E parameters.center parameters w)
          (P.prod (uniformOrientedProposals (N (r n)) d)))
        (Measure.map (massCenteredState ν hm parameters (fun v => ((w v).val,false)))
          (massMarkedLaw ν parameters))) :
    let parameters := Parameters.regular d E hd hbulk
    WeakLawConverges
      (fun n => Measure.map (D.microscopicRawState (r n) E parameters.center parameters w)
        (P.prod (uniformOrientedProposals (N (r n)) d)))
      (Measure.map (massRawState ν hm parameters w) (massMarkedLaw ν parameters)) := by
  intro parameters
  letI : PolishSpace AnchoredCountingState := isClosed_validAnchoredCountingState.polishSpace
  letI : MetricSpace AnchoredCountingState := TopologicalSpace.metrizableSpaceMetric AnchoredCountingState
  have hdpos : 0 < d := by exact_mod_cast (show (0 : ℝ) < d by linarith)
  let Pn := fun n => P.prod (uniformOrientedProposals (N (r n)) d)
  letI : ∀ n,IsProbabilityMeasure (uniformOrientedProposals (N (r n)) d) :=
    fun n => uniformOrientedProposals_isProbability _ _ (D.size_pos _) hdpos
  letI : ∀ n,IsProbabilityMeasure (Pn n) := fun n => inferInstance
  have hcentered' : WeakLawConverges
      (fun n => (Pn n).map (D.microscopicCenteredState (r n) E parameters.center parameters w))
      ((massMarkedLaw ν parameters).map (massCenteredState ν hm parameters (fun v => ((w v).val,false)))) := hcentered
  have hfstN (n) : Measure.map Prod.fst
      (Measure.map (D.microscopicCenteredState (r n) E parameters.center parameters w) (Pn n)) =
        P.map (fun ω => D.microscopicCountingState (r n) ω E parameters.scale parameters.center) := by
    rw [Measure.map_map measurable_fst (D.measurable_microscopicCenteredState _ E parameters.center parameters w)]
    exact product_scalar_map P _ _ (D.measurable_microscopicCountingState _ E parameters.scale parameters.center)
  have hfstTarget : Measure.map Prod.fst
      (Measure.map (massCenteredState ν hm parameters (fun v => ((w v).val,false))) (massMarkedLaw ν parameters))=ν := by
    rw [Measure.map_map measurable_fst (measurable_massCenteredState ν hm parameters (fun v => ((w v).val,false)))]
    exact massMarkedLaw_scalar_marginal ν parameters
  have hscalar : WeakLawConverges
      (fun n => P.map (fun ω => D.microscopicCountingState (r n) ω E parameters.scale parameters.center)) ν := by
    have hh := weakLaw_map _ _ hcentered' Prod.fst continuous_fst
    simpa only [hfstN,hfstTarget] using hh
  let C := fun n => readdMeanState parameters w ∘ D.microscopicCenteredState (r n) E parameters.center parameters w
  have hC (n) : Measurable (C n) := (continuous_readdMeanState parameters w).measurable.comp
    (D.measurable_microscopicCenteredState _ E parameters.center parameters w)
  have hcalibrated : WeakLawConverges (fun n => (Pn n).map (C n))
      ((massMarkedLaw ν parameters).map (massRawState ν hm parameters w)) := by
    have hh := weakLaw_map _ _ hcentered' (readdMeanState parameters w) (continuous_readdMeanState parameters w)
    simpa only [Measure.map_map (continuous_readdMeanState parameters w).measurable
      (D.measurable_microscopicCenteredState _ E parameters.center parameters w),
      Measure.map_map (continuous_readdMeanState parameters w).measurable
        (measurable_massCenteredState ν hm parameters (fun v => ((w v).val,false)))] using hh
  let F := windowStateCoordinates V
  have hF : Measurable (F : WindowFieldState V → AnchoredCountingState × (FieldCoordinate V → ℂ)) := F.continuous_toFun.measurable
  have hFinv : Measurable (F.symm : AnchoredCountingState × (FieldCoordinate V → ℂ) → WindowFieldState V) := F.symm.continuous_toFun.measurable
  let X := fun n => F ∘ D.microscopicRawState (r n) E parameters.center parameters w
  let XR := fun (_k : ℕ) n => F ∘ C n
  let Y := F ∘ massRawState ν hm parameters w
  have hX (n) : Measurable (X n) := F.continuous_toFun.measurable.comp
    (D.measurable_microscopicRawState _ E parameters.center parameters w)
  have hXR (k n) : Measurable (XR k n) := F.continuous_toFun.measurable.comp (hC n)
  have hY : Measurable Y := F.continuous_toFun.measurable.comp (measurable_massRawState ν hm parameters w)
  have hfinite (k) : WeakLawConverges (fun n => (Pn n).map (XR k n)) ((massMarkedLaw ν parameters).map Y) := by
    have hh := weakLaw_map _ _ hcalibrated F F.continuous_toFun
    simpa only [Measure.map_map (g := (F : WindowFieldState V → AnchoredCountingState × (FieldCoordinate V → ℂ))) hF (hC _),
      Measure.map_map (g := (F : WindowFieldState V → AnchoredCountingState × (FieldCoordinate V → ℂ))) hF (measurable_massRawState ν hm parameters w)] using hh
  have hpre : ∀ i : FieldCoordinate V,∀ ε δ : ℝ,0 < ε → 0 < δ →
      ∃ k0,∀ k,k0 ≤ k → ∀ᶠ n in atTop,(Pn n).real
        {z | ε < dist ((X n z).2 i) ((XR k n z).2 i)} ≤ δ := by
    rintro ⟨v,i,j⟩ ε δ hε hδ
    have hp := D.microscopic_proposalMean_calibration_probability P E hd hbulk r hr ν hscalar (w v) ε hε
    refine ⟨0,fun k _ => ?_⟩
    filter_upwards [(tendsto_order.mp hp).2 δ hδ] with n hn
    let error := fun ω => entryEnvelope (D.proposalMean (r n) ω
      (microscopicParameter (N (r n)) (D.size_pos (r n)) E parameters.scale parameters.scale_pos (w v)).val-
      Marked.mean parameters (fun ω => D.microscopicCountingState (r n) ω E parameters.scale parameters.center) (w v).val ω)
    have hbound (z : Ω × ProposalSample (N (r n)) d) : dist ((X n z).2 (v,i,j)) ((XR k n z).2 (v,i,j)) ≤ error z.1 := by
      rw [dist_eq_norm]
      change ‖D.microscopicRawMatrix (r n) E parameters (w v) z i j-(C n z).2 v i j‖ ≤ error z.1
      have heq : D.microscopicRawMatrix (r n) E parameters (w v) z i j-(C n z).2 v i j =
          (D.proposalMean (r n) z.1
            (microscopicParameter (N (r n)) (D.size_pos (r n)) E parameters.scale parameters.scale_pos (w v)).val-
            Marked.mean parameters (fun ω => D.microscopicCountingState (r n) ω E parameters.scale parameters.center) (w v).val z.1) i j := by
        dsimp [microscopicRawMatrix,C,readdMeanState,microscopicCenteredState,microscopicCenteredMatrix,Matrix.sub_apply,Matrix.add_apply,Marked.mean]
        ring
      rw [heq]
      exact entryEnvelope_bound _ i j
    have hsub : {z | ε < dist ((X n z).2 (v,i,j)) ((XR k n z).2 (v,i,j))} ⊆ {ω | ε < error ω} ×ˢ Set.univ :=
      fun z hz => ⟨hz.trans_le (hbound z),Set.mem_univ _⟩
    have hevent : (Pn n).real ({ω | ε < error ω} ×ˢ Set.univ)=P.real {ω | ε < error ω} := by
      rw [measureReal_def,Measure.prod_prod]
      simp only [measure_univ,mul_one,measureReal_def]
    exact (measureReal_mono hsub).trans (hevent ▸ hn.le)
  have htarget : ∀ i : FieldCoordinate V,∀ ε δ : ℝ,0 < ε → 0 < δ →
      ∀ᶠ k : ℕ in atTop,(massMarkedLaw ν parameters).real {z | ε < dist ((Y z).2 i) ((Y z).2 i)} ≤ δ := by
    intro i ε δ hε hδ
    exact Eventually.of_forall (fun _ => by simp only [dist_self,show ¬ ε < 0 by linarith,Set.setOf_false,measureReal_empty]; exact hδ.le)
  have hw := weakLaw_of_state_coordinate_truncations Pn (massMarkedLaw ν parameters)
    X XR (fun _ => Y) Y hX hXR (fun _ => hY) hY (fun _ _ _ => rfl) (fun _ _ => rfl) hfinite hpre htarget
  have hback := weakLaw_map _ _ hw F.symm F.symm.continuous_toFun
  have hleft (n) : Measure.map F.symm ((Pn n).map (X n))=
      (Pn n).map (D.microscopicRawState (r n) E parameters.center parameters w) := by
    rw [Measure.map_map (g := (F.symm : AnchoredCountingState × (FieldCoordinate V → ℂ) → WindowFieldState V)) hFinv (hX n)]
    congr 1
  have hright : Measure.map F.symm ((massMarkedLaw ν parameters).map Y)=
      (massMarkedLaw ν parameters).map (massRawState ν hm parameters w) := by
    rw [Measure.map_map (g := (F.symm : AnchoredCountingState × (FieldCoordinate V → ℂ) → WindowFieldState V)) hFinv hY]
    congr 1
  simpa only [hleft,hright] using hback

end GeneralizedBulk.External.RegularSpectralData
