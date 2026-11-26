import BourgadeHuang.RationalBulk.RationalLawDetermination

/-! The law-determination step is independent of the bulk/edge loop potential.
The actual charged ratios, their holomorphy and rational diagonal replication
are shared. Equality on any open edge sector suffices. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter Set
namespace BourgadeHuang.RationalEdge
open RationalBulk

/-- Equality on one actual open neighborhood for each rational charge block
forces equality of the entire anchored probability laws. -/
theorem anchored_law_eq_of_rational_local_expectations
    {β : ℝ} {p q : ℕ} (hp : 0<p) (hrat : β*(q:ℝ)=2*(p:ℝ))
    (μ ν : ProbabilityMeasure AnchoredCountingState) {a b : ℝ}
    (ha : 0<a) (hb : 0<b)
    (hμ : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2))
      (μ : Measure AnchoredCountingState))
    (hν : Integrable (fun s : AnchoredCountingState => Real.exp (b*‖s.val.2‖^2))
      (ν : Measure AnchoredCountingState))
    (heq : ∀ (k : ℕ) (eta : Fin k → Bool),
      ∃ z ∈ denominatorDomain (k*p) (repeatedSigns q eta),
        expectedChargedObservable (μ : Measure AnchoredCountingState) (charges β (k*p) (k*q))
          (blockAnchors (repeatedSigns p eta) (repeatedSigns q eta)) =ᶠ[𝓝 z]
        expectedChargedObservable (ν : Measure AnchoredCountingState) (charges β (k*p) (k*q))
          (blockAnchors (repeatedSigns p eta) (repeatedSigns q eta))) : μ=ν := by
  apply anchored_law_eq_of_rational_expectations hp hrat μ ν ha hb hμ hν
  intro k eta
  obtain ⟨z,hz,he⟩ := heq k eta
  exact (analyticOn_expectedChargedObservable (μ : Measure AnchoredCountingState)
      ha hμ β (repeatedSigns p eta) (repeatedSigns q eta)).eqOn_of_preconnected_of_eventuallyEq
    (analyticOn_expectedChargedObservable (ν : Measure AnchoredCountingState)
      hb hν β (repeatedSigns p eta) (repeatedSigns q eta))
    (denominatorDomain_convex (repeatedSigns q eta)).isPreconnected hz he

/-- Equivalent open-set formulation, convenient for an edge CMS chamber. -/
theorem anchored_law_eq_of_rational_open_expectations
    {β : ℝ} {p q : ℕ} (hp : 0<p) (hrat : β*(q:ℝ)=2*(p:ℝ))
    (μ ν : ProbabilityMeasure AnchoredCountingState) {a b : ℝ}
    (ha : 0<a) (hb : 0<b)
    (hμ : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2))
      (μ : Measure AnchoredCountingState))
    (hν : Integrable (fun s : AnchoredCountingState => Real.exp (b*‖s.val.2‖^2))
      (ν : Measure AnchoredCountingState))
    (heq : ∀ (k : ℕ) (eta : Fin k → Bool),
      ∃ U : Set (CMS.Point (k*p+k*q)), IsOpen U ∧ U.Nonempty ∧
        U ⊆ denominatorDomain (k*p) (repeatedSigns q eta) ∧
        EqOn
          (expectedChargedObservable (μ : Measure AnchoredCountingState) (charges β (k*p) (k*q))
            (blockAnchors (repeatedSigns p eta) (repeatedSigns q eta)))
          (expectedChargedObservable (ν : Measure AnchoredCountingState) (charges β (k*p) (k*q))
            (blockAnchors (repeatedSigns p eta) (repeatedSigns q eta))) U) : μ=ν := by
  apply anchored_law_eq_of_rational_local_expectations hp hrat μ ν ha hb hμ hν
  intro k eta
  obtain ⟨U,hU,⟨z,hz⟩,hsub,he⟩ := heq k eta
  exact ⟨z,hsub hz,Filter.mem_of_superset (hU.mem_nhds hz) (fun _ hw => he hw)⟩

/-- At its actual integration bases, every charged ratio equals one. -/
theorem expectedChargedObservable_at_bases {d : ℕ}
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (c b : Fin d → ℂ) (hb : ∀ j, (b j).im ≠ 0) :
    expectedChargedObservable ν c b b = 1 := by
  have he s : chargedObservable c b s b = 1 := by
    rw [chargedObservable_eq_exp c b b (fun j => sameOpenHalfPlane_self_of_offReal (hb j))]
    simp
  simp [expectedChargedObservable, he]

/-- The scalar in any local proportionality of genuine charged expectations
is fixed by their common diagonal value one. -/
theorem charged_proportionality_scalar_eq_one {n m : ℕ}
    (μ ν : ProbabilityMeasure AnchoredCountingState) {a b : ℝ}
    (ha : 0<a) (hb : 0<b)
    (hμ : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2))
      (μ : Measure AnchoredCountingState))
    (hν : Integrable (fun s : AnchoredCountingState => Real.exp (b*‖s.val.2‖^2))
      (ν : Measure AnchoredCountingState))
    (β : ℝ) (theta : Fin n → Bool) (eta : Fin m → Bool) (c : ℂ)
    {z : CMS.Point (n+m)} (hz : z ∈ denominatorDomain n eta)
    (he : expectedChargedObservable (μ : Measure AnchoredCountingState) (charges β n m)
        (blockAnchors theta eta) =ᶠ[𝓝 z]
      fun w => c*expectedChargedObservable (ν : Measure AnchoredCountingState) (charges β n m)
        (blockAnchors theta eta) w) : c=1 := by
  have hF := analyticOn_expectedChargedObservable (μ : Measure AnchoredCountingState)
    ha hμ β theta eta
  have hG := ((show AnalyticOnNhd ℂ (fun _ : CMS.Point (n+m) => c)
    (denominatorDomain n eta) from analyticOnNhd_const).mul
    (analyticOn_expectedChargedObservable (ν : Measure AnchoredCountingState) hb hν β theta eta))
  have hall := hF.eqOn_of_preconnected_of_eventuallyEq hG
    (denominatorDomain_convex eta).isPreconnected hz he
  have hbase : blockAnchors theta eta ∈ denominatorDomain n eta := by
    intro j
    cases hs : eta j <;> simp [blockAnchors,signAnchor,CMS.signValue,hs]
  have hbaseoff i : (blockAnchors theta eta i).im ≠ 0 := by
    rw [blockAnchors_eq_signAnchor]
    exact signAnchor_offReal _
  have h := hall hbase
  dsimp only at h
  rw [expectedChargedObservable_at_bases _ _ _ hbaseoff,
    expectedChargedObservable_at_bases _ _ _ hbaseoff,mul_one] at h
  exact h.symm

/-- It suffices to prove that the edge CMS observables span a one-dimensional
space locally: their genuine diagonal normalization removes the scalar. -/
theorem anchored_law_eq_of_rational_local_proportionality
    {β : ℝ} {p q : ℕ} (hp : 0<p) (hrat : β*(q:ℝ)=2*(p:ℝ))
    (μ ν : ProbabilityMeasure AnchoredCountingState) {a b : ℝ}
    (ha : 0<a) (hb : 0<b)
    (hμ : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2))
      (μ : Measure AnchoredCountingState))
    (hν : Integrable (fun s : AnchoredCountingState => Real.exp (b*‖s.val.2‖^2))
      (ν : Measure AnchoredCountingState))
    (heq : ∀ (k : ℕ) (eta : Fin k → Bool),
      ∃ (c : ℂ) (z : CMS.Point (k*p+k*q)), z ∈ denominatorDomain (k*p) (repeatedSigns q eta) ∧
        expectedChargedObservable (μ : Measure AnchoredCountingState) (charges β (k*p) (k*q))
          (blockAnchors (repeatedSigns p eta) (repeatedSigns q eta)) =ᶠ[𝓝 z]
        fun w => c*expectedChargedObservable (ν : Measure AnchoredCountingState) (charges β (k*p) (k*q))
          (blockAnchors (repeatedSigns p eta) (repeatedSigns q eta)) w) : μ=ν := by
  apply anchored_law_eq_of_rational_local_expectations hp hrat μ ν ha hb hμ hν
  intro k eta
  obtain ⟨c,z,hz,he⟩ := heq k eta
  have hc := charged_proportionality_scalar_eq_one μ ν ha hb hμ hν β
    (repeatedSigns p eta) (repeatedSigns q eta) c hz he
  subst c
  exact ⟨z,hz,by simpa only [one_mul] using he⟩

end BourgadeHuang.RationalEdge
