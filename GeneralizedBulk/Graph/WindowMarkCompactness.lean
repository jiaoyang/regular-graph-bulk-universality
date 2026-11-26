import GeneralizedBulk.Graph.ProposalSecondMoment
import GeneralizedBulk.Analysis.JointMarkSecondSubsequence
import GeneralizedBulk.Analysis.AEContinuousMapping
import GeneralizedBulk.Analysis.AnchoredCompactness

/-! Actual finite window/endpoint-mark laws have joint weak subsequences.
Marks use their exact global second moments, so no fourth-moment certificate
or bad-event control is needed for this compactness step. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter Set
open scoped Topology ENNReal
namespace GeneralizedBulk.External.RegularSpectralData
open Graph GeneralizedBulk.Counting GeneralizedBulk.Analysis
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

set_option maxHeartbeats 2500000 in
theorem windowMark_subsequence_of_tight_scalar {m : ℕ} (hm : 0 < m)
    (P : Measure Ω) [IsProbabilityMeasure P] (hd : 0 < d)
    (E sigma center R : ℝ) (selection : ∀ n,Ω → Fin m → Fin (N n))
    (hselection : ∀ n i,Measurable (fun ω => selection n ω i))
    (r : ℕ → ℕ)
    (hTight : IsTightMeasureSet (range (fun n => P.map (fun ω => D.microscopicCountingState (r n) ω E sigma center))))
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hscalar : WeakLawConverges
      (fun n => P.map (fun ω => D.microscopicCountingState (r n) ω E sigma center)) ν)
    (hboundary : ∀ᵐ s ∂ν,s.val.1.measure {-R}=0 ∧ s.val.1.measure {R}=0) :
    ∃ t : ℕ → ℕ,StrictMono t ∧
      ∃ ρ : ProbabilityMeasure (WindowData m × ((Fin m × Fin 4) → ℝ)),
        WeakLawConverges
          (fun n => D.windowMarkLaw P (r (t n)) E sigma center R (selection (r (t n)))) ρ := by
  letI : PolishSpace AnchoredCountingState := isClosed_validAnchoredCountingState.polishSpace
  letI : MetricSpace AnchoredCountingState := TopologicalSpace.metrizableSpaceMetric AnchoredCountingState
  let PN := fun n => P.prod (uniformOrientedProposals (N (r n)) d)
  letI : ∀ n,IsProbabilityMeasure (uniformOrientedProposals (N (r n)) d) :=
    fun n => uniformOrientedProposals_isProbability _ _ (D.size_pos _) hd
  letI : ∀ n,IsProbabilityMeasure (PN n) := fun n => inferInstance
  let S := fun n (z : Ω × ProposalSample (N (r n)) d) => D.microscopicCountingState (r n) z.1 E sigma center
  let marks := fun n => D.selectedProposalMarks (r n) (selection (r n))
  have hS (n) : Measurable (S n) := (D.measurable_microscopicCountingState (r n) E sigma center).comp measurable_fst
  have hmarks (n) : Measurable (marks n) := D.measurable_selectedProposalMarks (r n) _ (hselection (r n))
  have hSmarg (n) : (PN n).map (S n)=P.map (fun ω => D.microscopicCountingState (r n) ω E sigma center) :=
    product_scalar_map P _ _ (D.measurable_microscopicCountingState (r n) E sigma center)
  have hst : IsTightMeasureSet (range (fun n => (PN n).map (S n))) := by simpa only [hSmarg] using hTight
  have hi (n) := D.selectedProposalMarks_second_integrable_bound (r n) hm hd P _ (hselection (r n))
  obtain ⟨ρ,t,ht,hweak⟩ := anchored_mark_map_subsequence_of_tight_scalar_second PN S marks hS hmarks hst
    (fun n => (hi n).1) (4*m : ℕ) (fun n => (hi n).2)
  let F := fun n (z : Ω × ProposalSample (N (r n)) d) => (S n z,marks n z)
  have hF (n) : Measurable (F n) := (hS n).prodMk (hmarks n)
  have hfst (n) : ((PN n).map (F n)).map Prod.fst=P.map (fun ω => D.microscopicCountingState (r n) ω E sigma center) := by
    rw [Measure.map_map measurable_fst (hF n)]
    exact hSmarg n
  have hmarg : WeakLawConverges (fun n => ((PN (t n)).map (F (t n))).map Prod.fst) ν := by
    intro G
    simpa only [hfst] using (hscalar G).comp ht.tendsto_atTop
  have hρfst : (ρ : Measure (AnchoredCountingState × ((Fin m × Fin 4) → ℝ))).map Prod.fst=ν :=
    weak_limit_marginal_eq _ (ρ : Measure (AnchoredCountingState × ((Fin m × Fin 4) → ℝ))) hweak Prod.fst continuous_fst ν hmarg
  let f : (AnchoredCountingState × ((Fin m × Fin 4) → ℝ)) → WindowData m × ((Fin m × Fin 4) → ℝ) :=
    fun z => (windowData m (-R) R z.1,z.2)
  have hf : Measurable f := ((measurable_windowData m (-R) R).comp measurable_fst).prodMk measurable_snd
  have hcont : ∀ᵐ z ∂(ρ : Measure (AnchoredCountingState × ((Fin m × Fin 4) → ℝ))),ContinuousAt f z := by
    have hb : ∀ᵐ z ∂(ρ : Measure (AnchoredCountingState × ((Fin m × Fin 4) → ℝ))),z.1.val.1.measure {-R}=0 ∧ z.1.val.1.measure {R}=0 :=
      ae_of_ae_map measurable_fst.aemeasurable (by rw [hρfst]; exact hboundary)
    filter_upwards [hb] with z hz
    exact ((continuousAt_windowData m (-R) R z.1 hz.1 hz.2).comp continuousAt_fst).prodMk continuousAt_snd
  letI : ∀ n,IsProbabilityMeasure ((PN (t n)).map (F (t n))) :=
    fun n => isProbabilityMeasure_map (hF (t n)).aemeasurable
  have hmap := weakLaw_map_of_ae_continuous (fun n => (PN (t n)).map (F (t n))) (ρ : Measure (AnchoredCountingState × ((Fin m × Fin 4) → ℝ))) hweak f hf hcont
  have heq (n) : Measure.map f ((PN (t n)).map (F (t n)))=
      D.windowMarkLaw P (r (t n)) E sigma center R (selection (r (t n))) := by
    rw [Measure.map_map hf (hF (t n))]
    rfl
  refine ⟨t,ht,⟨Measure.map f (ρ : Measure (AnchoredCountingState × ((Fin m × Fin 4) → ℝ))),isProbabilityMeasure_map hf.aemeasurable⟩,?_⟩
  intro G
  simpa only [heq] using hmap G

theorem isTight_microscopic_states_of_uniform_anchor_tails
    (P : Measure Ω) (E sigma center : ℝ) (r : ℕ → ℕ)
    (htail : ∀ epsilon : ℝ≥0∞,0 < epsilon → ∃ B : ℝ,∀ n,
      P {ω | B < ‖(D.microscopicCountingState n ω E sigma center).val.2‖} ≤ epsilon) :
    IsTightMeasureSet (range (fun n => P.map (fun ω => D.microscopicCountingState (r n) ω E sigma center))) := by
  apply isTightMeasureSet_anchored_of_uniform_anchor_tails
  intro epsilon hepsilon
  obtain ⟨B,hB⟩ := htail epsilon hepsilon
  refine ⟨B,fun n => ?_⟩
  have hset : MeasurableSet {s : AnchoredCountingState | B < ‖s.val.2‖} :=
    measurableSet_lt measurable_const (measurable_snd.comp measurable_subtype_coe).norm
  rw [Measure.map_apply (D.measurable_microscopicCountingState (r n) E sigma center) hset]
  exact hB (r n)

end GeneralizedBulk.External.RegularSpectralData
