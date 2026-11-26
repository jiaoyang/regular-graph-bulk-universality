import GeneralizedBulk.Graph.WindowField
import GeneralizedBulk.Graph.WindowBulkConvergence
import GeneralizedBulk.Graph.WindowZeroMarkConvergence
import GeneralizedBulk.Analysis.CountableRestrictionConvergence

/-! Actual finite-window matrix laws converge jointly with the full scalar
state, solely from the allowed BS/HY inputs and scalar weak convergence. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter Set
open scoped Topology
namespace GeneralizedBulk.External.RegularSpectralData
open Graph GeneralizedBulk.Counting GeneralizedBulk.Analysis GeneralizedBulk.Gaussian
open GeneralizedBulk.KestenMcKay GeneralizedBulk.Entropy.ChannelRates
variable {d : ℕ} {N : ℕ → ℕ} {Ω V : Type*} [MeasurableSpace Ω] [Fintype V]
variable (D : RegularSpectralData d N Ω)

set_option maxHeartbeats 2500000 in
theorem microscopicWindowState_converges_of_BS_HY [Nonempty Ω]
    (r : ℕ → ℕ) (hr : StrictMono r)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hUniform : ∀ n,Measure.map (D.spectralRegularGraph n) P=regularGraphLaw (N n) d)
    (K : Set ℝ) (BS : BSQualitativeInput D P K)
    (HC : HYCoarseInput D P (D.kestenMcKayQuantile (by exact_mod_cast BS.degree_ge_three)))
    (J : Set ℝ) (hJ : IsCompact J) (hJbulk : ∀ E ∈ J,E^2 < 4*((d : ℝ)-1))
    (c0 : ℝ) (hcchannel : c0 < channelNoiseExponent (channelTheta 1 d))
    (hcrigidity : c0 < HC.rigidity_exponent) (hcsmall : c0 ≤ 1/16)
    (HL : HYLocalStarInput D P J c0 (treeGreenStar d (by exact_mod_cast BS.degree_ge_three)))
    (E center R gap : ℝ) (parameters : Parameters) (hp : parameters.p=E/d)
    (hE : E ∈ K) (hgap : 0 < gap) (hwindow : Icc (E-gap) (E+gap) ⊆ J) (leaf : Fin d)
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hscalar : WeakLawConverges
      (fun n => P.map (fun ω => D.microscopicCountingState (r n) ω E parameters.scale center)) ν)
    (hboundary : ∀ᵐ s ∂ν,s.val.1.measure {-R}=0 ∧ s.val.1.measure {R}=0)
    (w : V → GraphNonreal) :
    WeakLawConverges
      (fun n => Measure.map (D.microscopicWindowState (r n) E center parameters R w)
        (P.prod (uniformOrientedProposals (N (r n)) d)))
      (Measure.map (massWindowState ν parameters R (fun v => ((w v).val,false)))
        (massMarkedLaw ν parameters)) := by
  have hd : 0 < d := by have hh := BS.degree_ge_three; omega
  let μ := fun n => Measure.map (D.microscopicWindowState (r n) E center parameters R w)
    (P.prod (uniformOrientedProposals (N (r n)) d))
  let ξ := Measure.map (massWindowState ν parameters R (fun v => ((w v).val,false))) (massMarkedLaw ν parameters)
  let count := fun z : WindowFieldState V => intervalCount z.1.val.1 (-R) R
  have hcount : Measurable count := (measurable_intervalCount (-R) R).comp
    ((measurable_fst.comp measurable_subtype_coe).comp measurable_fst)
  letI : ∀ n,IsProbabilityMeasure (uniformOrientedProposals (N (r n)) d) :=
    fun n => uniformOrientedProposals_isProbability (N (r n)) d (D.size_pos (r n)) hd
  letI : ∀ n,IsProbabilityMeasure (μ n) := fun n =>
    isProbabilityMeasure_map (D.measurable_microscopicWindowState (r n) E center parameters R w).aemeasurable
  letI : IsProbabilityMeasure ξ := isProbabilityMeasure_map
    (measurable_massWindowState ν parameters R (fun v => ((w v).val,false))).aemeasurable
  apply weakLaw_of_countable_restrictions μ ξ (fun _ => count) count (fun _ => hcount) hcount
  intro m
  let fallback := fun n (_ : Ω) => D.bulkPaddingIndex E m n
  let selection := fun n (ω : Ω) => D.paddedWindowSelection n ω E parameters.scale (-R) R (fallback n)
  have hmarked : WeakLawConverges
      (fun n => (D.windowMarkLaw P (r n) E parameters.scale center R (selection (r n))).restrict
        (Prod.fst ⁻¹' {x : WindowData m | x.2.1=m}))
      (((ν.map (windowData m (-R) R)).restrict {x : WindowData m | x.2.1=m}).prod
        (finiteMarkLaw parameters.p m)) := by
    cases m with
    | zero =>
      exact D.windowMarkLaw_zero_restrict_converges P hd E parameters.scale center R parameters.p r selection ν hscalar hboundary
    | succ m =>
      rw [hp]
      exact D.windowMarkLaw_restrict_converges_of_BS_HY (Nat.succ_pos m) r hr P hUniform K BS HC J hJ hJbulk
        c0 hcchannel hcrigidity hcsmall HL E parameters.scale center R gap parameters.scale_pos hE hgap hwindow leaf ν hscalar hboundary
  have hmapped := weakLaw_map _ _ hmarked
    (windowPolynomialState parameters (fun v => ((w v).val,false)))
    (continuous_windowPolynomialState parameters (fun v => ((w v).val,false)))
  have hsource (n : ℕ) : (μ n).restrict {x | count x=m} =
      Measure.map (windowPolynomialState parameters (fun v => ((w v).val,false)))
        ((D.windowMarkLaw P (r n) E parameters.scale center R (selection (r n))).restrict
          (Prod.fst ⁻¹' {x : WindowData m | x.2.1=m})) :=
    D.microscopicWindowState_restrict_law P (r n) E center parameters R w (fallback (r n))
      (fun i => D.measurable_bulkPaddingIndex E m (r n) i)
  have htarget : ξ.restrict {x | count x=m} =
      Measure.map (windowPolynomialState parameters (fun v => ((w v).val,false)))
        (((ν.map (windowData m (-R) R)).restrict {x : WindowData m | x.2.1=m}).prod
          (finiteMarkLaw parameters.p m)) :=
    massWindowState_restrict_law ν parameters R (fun v => ((w v).val,false)) m
  simpa only [hsource,htarget] using hmapped

end GeneralizedBulk.External.RegularSpectralData
