import GeneralizedBulk.Graph.HYResolventChannel
import GeneralizedBulk.Graph.FiniteConditional
import GeneralizedBulk.Graph.MeasurableSpectralVariance
import GeneralizedBulk.Graph.RawPairCompactness
import GeneralizedBulk.Graph.MicroscopicScalarState

/-! Literal joint sampling transport from a possibly augmented spectral
probability space to the uniform graph/two-edge law. Eigenbasis choices need
not be functions of the underlying graph. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped BigOperators Classical
namespace GeneralizedBulk.External.RegularSpectralData
open Graph
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

def spectralPairSample (n : ℕ) (z : Ω × ProposalSample (N n) d) : EdgePairState (N n) d :=
  (D.proposalFiberEquiv n z.1 z.2).val

theorem measurable_spectralPairSample (n : ℕ) : Measurable (D.spectralPairSample n) := by
  apply measurable_from_prod_countable
  intro t
  have he : Measurable (fun ω => D.proposalEndpoints n ω t) :=
    measurable_pi_lambda _ (fun i => D.measurable_proposalEndpoints n t i)
  apply measurable_to_countable'
  intro s
  have heq : (fun ω => D.spectralPairSample n (ω,t)) ⁻¹' {s} =
      {ω | D.spectralRegularGraph n ω=edgePairGraph s} ∩
        {ω | D.proposalEndpoints n ω t=s.val.2} := by
    ext ω
    constructor
    · intro hh
      have hv : D.spectralPairSample n (ω,t)=s := hh
      constructor
      · rw [← hv]
        exact (D.proposalFiberEquiv n ω t).property.symm
      · have hval := congrArg Subtype.val hv
        rw [show (D.spectralPairSample n (ω,t)).val=
          (D.simpleGraph n ω,D.proposalEndpoints n ω t) from D.proposalFiberEquiv_val n ω t] at hval
        exact congrArg Prod.snd hval
    · rintro ⟨hg,ht⟩
      apply Subtype.ext
      rw [show (D.spectralPairSample n (ω,t)).val=
        (D.simpleGraph n ω,D.proposalEndpoints n ω t) from D.proposalFiberEquiv_val n ω t]
      exact Prod.ext (congrArg Subtype.val hg) ht
  rw [heq]
  exact ((D.measurable_spectralRegularGraph n) (measurableSet_singleton _)).inter
    (he (measurableSet_singleton _))

/-- Uniform physical endpoint sampling over the original spectral model is
exactly the finite uniform edge-pair law. This is independent of every
auxiliary eigensystem choice. -/
theorem spectralPairSample_map (P : Measure Ω) [IsProbabilityMeasure P]
    (hUniform : ∀ n,Measure.map (D.spectralRegularGraph n) P=regularGraphLaw (N n) d)
    (n : ℕ) (hd : 0 < d) :
    Measure.map (D.spectralPairSample n) (P.prod (uniformOrientedProposals (N n) d)) =
      edgePairLaw (N n) d := by
  letI : Nonempty Ω := ProbabilityMeasure.nonempty (⟨P,inferInstance⟩ : ProbabilityMeasure Ω)
  letI : Nonempty (RegularGraph (N n) d) := ⟨D.spectralRegularGraph n (Classical.arbitrary Ω)⟩
  letI : Nonempty (EdgePairState (N n) d) := edgePairState_nonempty (D.size_pos n) hd
  letI : Nonempty (Fin (N n) × Fin d) := ⟨⟨⟨0,D.size_pos n⟩,⟨0,hd⟩⟩⟩
  letI := uniformOrientedProposals_isProbability (N n) d (D.size_pos n) hd
  letI : IsProbabilityMeasure (edgePairLaw (N n) d) := finiteUniform_isProbability _
  have hintegral (g : EdgePairState (N n) d → ℝ) :
      (∫ z,g (D.spectralPairSample n z) ∂P.prod (uniformOrientedProposals (N n) d)) =
      ∫ s,g s ∂edgePairLaw (N n) d := by
    let F := fun G : RegularGraph (N n) d =>
      ∫ s : {s : EdgePairState (N n) d // edgePairGraph s=G},g s ∂finiteUniform {s // edgePairGraph s=G}
    have hgi : Integrable (fun z => g (D.spectralPairSample n z))
        (P.prod (uniformOrientedProposals (N n) d)) := by
      apply (integrable_const (∑ s,‖g s‖)).mono'
        ((measurable_of_finite g).comp (D.measurable_spectralPairSample n)).aestronglyMeasurable
      exact Eventually.of_forall (fun z => Finset.single_le_sum
        (fun s _ => norm_nonneg (g s)) (Finset.mem_univ (D.spectralPairSample n z)))
    rw [integral_prod _ hgi]
    have hinner (ω : Ω) : (∫ t,g (D.spectralPairSample n (ω,t)) ∂uniformOrientedProposals (N n) d) =
        F (D.spectralRegularGraph n ω) := by
      dsimp [F]
      rw [← finiteUniform_map_equiv (D.proposalFiberEquiv n ω),
        integral_map (measurable_of_finite _).aemeasurable (measurable_of_finite _).aestronglyMeasurable]
      rfl
    simp_rw [hinner]
    rw [← integral_map (D.measurable_spectralRegularGraph n).aemeasurable
      (measurable_of_finite F).aestronglyMeasurable,hUniform n]
    exact (integral_edgePairLaw_fibers g).symm
  ext A hA
  apply (ENNReal.toReal_eq_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp
  let g := A.indicator (fun _ => (1:ℝ))
  have heq (μ : Measure (EdgePairState (N n) d)) : (∫ s,g s ∂μ)=μ.real A := by
    rw [integral_indicator_const 1 hA]
    simp
  change (Measure.map (D.spectralPairSample n) (P.prod (uniformOrientedProposals (N n) d))).real A =
    (edgePairLaw (N n) d).real A
  rw [← heq,← heq,integral_map (D.measurable_spectralPairSample n).aemeasurable
    (measurable_of_finite g).aestronglyMeasurable]
  exact hintegral g

theorem spectralPairSample_map_observable {V : Type*} [MeasurableSpace V]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hUniform : ∀ n,Measure.map (D.spectralRegularGraph n) P=regularGraphLaw (N n) d)
    (n : ℕ) (hd : 0 < d) (f : EdgePairState (N n) d → V) :
    Measure.map (fun z => f (D.spectralPairSample n z))
      (P.prod (uniformOrientedProposals (N n) d)) =
      Measure.map f (edgePairLaw (N n) d) := by
  change Measure.map (f ∘ D.spectralPairSample n) _ = _
  rw [← Measure.map_map (measurable_of_finite f) (D.measurable_spectralPairSample n),
    D.spectralPairSample_map P hUniform n hd]

theorem spectralPairSample_rawValue (n : ℕ) (E sigma center : ℝ)
    (hsigma : 0 < sigma) (w : GraphNonreal) (z : Ω × ProposalSample (N n) d) :
    microscopicRawValue (d := d) (D.size_pos n) E sigma center hsigma w (D.spectralPairSample n z) =
      (anchoredNevanlinna (D.microscopicCountingState n z.1 E sigma center) w.val,
        fun i j => D.resolvent n z.1
          (microscopicParameter (N n) (D.size_pos n) E sigma hsigma w).val
          (D.proposalEndpoints n z.1 z.2 i) (D.proposalEndpoints n z.1 z.2 j)) := by
  unfold microscopicRawValue
  have hv : (D.spectralPairSample n z).val=(D.simpleGraph n z.1,D.proposalEndpoints n z.1 z.2) :=
    D.proposalFiberEquiv_val n z.1 z.2
  rw [hv]
  apply Prod.ext
  · rw [D.microscopicCountingState_scalar n z.1 E sigma center hsigma w]
    simp only [Graph.microscopicScalar,microscopicScalar,D.graphResolvent_simpleGraph n z.1]
    rfl
  · change (fun i j => graphResolvent (D.simpleGraph n z.1) _
      (D.proposalEndpoints n z.1 z.2 i) (D.proposalEndpoints n z.1 z.2 j)) = _
    rw [D.graphResolvent_simpleGraph n z.1]

theorem microscopicRawLaw_eq_spectral (P : Measure Ω) [IsProbabilityMeasure P]
    (hUniform : ∀ n,Measure.map (D.spectralRegularGraph n) P=regularGraphLaw (N n) d)
    (n : ℕ) (hd : 0 < d) (E sigma center : ℝ) (hsigma : 0 < sigma) (w : GraphNonreal) :
    microscopicRawLaw (d := d) (D.size_pos n) E sigma center hsigma w =
      Measure.map (fun z : Ω × ProposalSample (N n) d =>
        ((anchoredNevanlinna (D.microscopicCountingState n z.1 E sigma center) w.val,
          fun i j => D.resolvent n z.1
            (microscopicParameter (N n) (D.size_pos n) E sigma hsigma w).val
            (D.proposalEndpoints n z.1 z.2 i) (D.proposalEndpoints n z.1 z.2 j)) : RawValue))
        (P.prod (uniformOrientedProposals (N n) d)) := by
  have hh := D.spectralPairSample_map_observable P hUniform n hd
    (microscopicRawValue (d := d) (D.size_pos n) E sigma center hsigma w)
  simpa only [D.spectralPairSample_rawValue,microscopicRawLaw] using hh.symm

theorem microscopicRawFieldLaw_eq_spectral {I : Type*} (P : Measure Ω) [IsProbabilityMeasure P]
    (hUniform : ∀ n,Measure.map (D.spectralRegularGraph n) P=regularGraphLaw (N n) d)
    (n : ℕ) (hd : 0 < d) (E sigma center : ℝ) (hsigma : 0 < sigma) (w : I → GraphNonreal) :
    microscopicRawFieldLaw (d := d) (D.size_pos n) E sigma center hsigma w =
      Measure.map (fun z : Ω × ProposalSample (N n) d => fun a =>
        ((anchoredNevanlinna (D.microscopicCountingState n z.1 E sigma center) (w a).val,
          fun i j => D.resolvent n z.1
            (microscopicParameter (N n) (D.size_pos n) E sigma hsigma (w a)).val
            (D.proposalEndpoints n z.1 z.2 i) (D.proposalEndpoints n z.1 z.2 j)) : RawValue))
        (P.prod (uniformOrientedProposals (N n) d)) := by
  have hh := D.spectralPairSample_map_observable P hUniform n hd
    (microscopicRawField (d := d) (D.size_pos n) E sigma center hsigma w)
  refine hh.symm.trans ?_
  congr 1
  funext z a
  exact D.spectralPairSample_rawValue n E sigma center hsigma (w a) z

end GeneralizedBulk.External.RegularSpectralData
