import BourgadeHuang.RationalEdge.ConvergenceReduction

/-!
# The hypotheses of Bourgade--Huang, Theorems 1.11 and 1.12

These lemmas translate the literal assumptions of the paper into the proved
edge compactness and hierarchy framework.  The final uniqueness premise in
`EdgeLoopEquations.law_eq_of_unique` is explicit: this reduction alone does
not prove Theorem 1.11 or identify a law with the Airy-beta process.
-/
noncomputable section
open scoped Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalEdge

/-- Assumption 1.10, with the weaker sufficient natural moments at the anchor.
The state includes all allowed Nevanlinna affine terms and integer pole
multiplicities; the loop equation includes coincident and mixed-half-plane
parameters. -/
structure EdgeLoopEquations {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (β : ℝ) (X : Ω → AnchoredCountingState) : Prop where
  measurable_state : Measurable X
  moments : ∀ q : ℕ, Integrable (fun ω => ‖(X ω).val.2‖ ^ q) μ
  equation : ∀ n : ℕ, ∀ w : ℂ, w.im ≠ 0 →
    ∀ aux : Fin n → ℂ, (∀ j, (aux j).im ≠ 0) →
      (∫ ω, loopIntegrand β (X ω) w aux ∂μ) = 0

/-- Finiteness of the expectations is proved, rather than left implicit in
the convention that the Bochner integral of a nonintegrable function is zero. -/
theorem EdgeLoopEquations.integrable_loop
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {β : ℝ} {X : Ω → AnchoredCountingState} (h : EdgeLoopEquations μ β X)
    {n : ℕ} {w : ℂ} {aux : Fin n → ℂ}
    (hw : w.im ≠ 0) (ha : ∀ j, (aux j).im ≠ 0) :
    Integrable (fun ω => loopIntegrand β (X ω) w aux) μ :=
  integrable_loop_comp μ X h.measurable_state h.moments β hw ha

theorem EdgeLoopEquations.vanishing_const
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {β : ℝ}
    {X : Ω → AnchoredCountingState} (h : EdgeLoopEquations μ β X) :
    VanishingHierarchy μ β (fun _ => X) := by
  intro n w hw aux ha
  simpa only [h.equation n w hw aux ha] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))

theorem weakLawConverges_const_probabilityLaw
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → AnchoredCountingState) (hX : Measurable X) :
    WeakLawConverges μ (fun _ => X)
      (probabilityLaw μ X hX : Measure AnchoredCountingState) := by
  intro F
  rw [integral_probabilityLaw]
  exact tendsto_const_nhds

theorem EdgeLoopEquations.exact_law
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {β : ℝ} {X : Ω → AnchoredCountingState} (h : EdgeLoopEquations μ β X) :
    ExactHierarchy
      (probabilityLaw μ X h.measurable_state : Measure AnchoredCountingState) β :=
  exactHierarchy_of_anchored_sequence_limit μ β (fun _ => X)
    (fun _ => h.measurable_state) (fun _ => h.moments) h.vanishing_const
    (probabilityLaw μ X h.measurable_state)
    (weakLawConverges_const_probabilityLaw μ X h.measurable_state)

theorem EdgeLoopEquations.exponentialSquare_law
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {β : ℝ} {X : Ω → AnchoredCountingState} (h : EdgeLoopEquations μ β X) :
    ∃ a : ℝ, 0 < a ∧ Integrable
      (fun s : AnchoredCountingState => Real.exp (a * ‖s.val.2‖ ^ 2))
      (probabilityLaw μ X h.measurable_state : Measure AnchoredCountingState) :=
  exponential_anchor_of_anchored_sequence_limit μ β (fun _ => X)
    (fun _ => h.measurable_state) (fun _ => h.moments) h.vanishing_const
    (probabilityLaw μ X h.measurable_state)
    (weakLawConverges_const_probabilityLaw μ X h.measurable_state)

/-- Exact edge characterization reduced to uniqueness among actual solutions
of the edge hierarchy. The uniqueness premise remains a separate obligation. -/
theorem EdgeLoopEquations.law_eq_of_unique
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {β : ℝ} {X : Ω → AnchoredCountingState} (h : EdgeLoopEquations μ β X)
    (ν : ProbabilityMeasure AnchoredCountingState)
    (hunique : ∀ ρ : ProbabilityMeasure AnchoredCountingState,
      ExactHierarchy (ρ : Measure AnchoredCountingState) β →
      (∃ a : ℝ, 0 < a ∧ Integrable
        (fun s : AnchoredCountingState => Real.exp (a * ‖s.val.2‖ ^ 2))
          (ρ : Measure AnchoredCountingState)) → ρ = ν) :
    probabilityLaw μ X h.measurable_state = ν ∧
      Measure.map (fun ω => (X ω).val.1) μ =
        (anchoredCountingLaw ν : Measure LocalCountingMeasure) := by
  have he := hunique (probabilityLaw μ X h.measurable_state)
    h.exact_law h.exponentialSquare_law
  refine ⟨he, ?_⟩
  rw [← he]
  change Measure.map (fun ω => (X ω).val.1) μ =
    Measure.map (fun s : AnchoredCountingState => s.val.1) (Measure.map X μ)
  exact (Measure.map_map (measurable_fst.comp measurable_subtype_coe)
    h.measurable_state).symm

/-- The real-order moment assumption in the paper supplies all moments needed
by the exact edge reduction. -/
theorem EdgeLoopEquations.of_paper
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (β : ℝ) (X : Ω → AnchoredCountingState) (hX : Measurable X)
    (hm : ∀ q : ℝ, 0 < q → ∀ w : ℂ, w.im ≠ 0 →
      Integrable (fun ω => ‖anchoredNevanlinna (X ω) w‖ ^ q) μ)
    (hh : ∀ n : ℕ, ∀ w : ℂ, w.im ≠ 0 →
      ∀ aux : Fin n → ℂ, (∀ j, (aux j).im ≠ 0) →
        (∫ ω, loopIntegrand β (X ω) w aux ∂μ) = 0) :
    EdgeLoopEquations μ β X := by
  refine ⟨hX, ?_, hh⟩
  intro q
  cases q with
  | zero => simpa using (integrable_const (1 : ℝ) : Integrable _ μ)
  | succ n =>
      simpa only [anchoredNevanlinna_I, Real.rpow_natCast] using
        hm (n + 1 : ℕ) (by positivity) Complex.I (by simp)

/-- The literal real-order event moments in Theorem 1.12 imply the natural
anchor moments in `EventWeightedHierarchy`. No moment outside the event is
required. -/
theorem event_anchor_moments_of_paper
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : ℕ → Ω → AnchoredCountingState) (A : ℕ → Set Ω)
    (hm : ∀ N, ∀ q : ℝ, 0 < q → ∀ w : ℂ, w.im ≠ 0 →
      Integrable (fun ω => ‖anchoredNevanlinna (X N ω) w‖ ^ q)
        (μ.restrict (A N))) :
    ∀ N q : ℕ, Integrable (fun ω => ‖(X N ω).val.2‖ ^ q) (μ.restrict (A N)) := by
  intro N q
  cases q with
  | zero => simpa using (integrable_const (1 : ℝ) : Integrable _ (μ.restrict (A N)))
  | succ n =>
      simpa only [anchoredNevanlinna_I, Real.rpow_natCast] using
        hm N (n + 1 : ℕ) (by positivity) Complex.I (by simp)

end BourgadeHuang.RationalEdge
