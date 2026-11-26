import BourgadeHuang.RationalBulk.GaussianBetaLimit

/-!
# Bourgade--Huang, Theorem 1.5

The exact bulk loop hierarchy characterizes Sine beta for every positive
rational beta.  This file discharges the exponential-square moment hypothesis
of the intermediate uniqueness theorem from the ordinary finite moments in
Assumption 1.4.  The argument applies the proved hierarchy moment estimates to
a constant sequence; it does not assume a local law, exponential integrability,
uniqueness, or convergence of that sequence as an additional input.

`bourgade_huang_theorem_1_5_paper` states the paper's finite real-order moments
at every off-real parameter.  The other endpoints use the weaker sufficient
assumption of all natural-order moments at the anchor `i`.
-/
noncomputable section
open scoped Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalBulk

/-- Assumption 1.4 on an arbitrary probability space.  The state contains a
locally finite integer counting measure and the full Nevanlinna anchor,
including the allowed nonnegative affine term.  All mixed half-plane and
coincident spectral parameters are included in the equation. -/
structure BulkLoopEquations {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (β : ℝ) (X : Ω → AnchoredCountingState) : Prop where
  measurable_state : Measurable X
  moments : ∀ q : ℕ, Integrable (fun ω => ‖(X ω).val.2‖ ^ q) μ
  equation : ∀ n : ℕ, ∀ w : ℂ, w.im ≠ 0 →
    ∀ aux : Fin n → ℂ, (∀ j, (aux j).im ≠ 0) →
      (∫ ω, loopIntegrand β (X ω) w aux ∂μ) = 0

/-- Every expectation in the hierarchy is an integral of an integrable
function; the equation cannot hold merely through the convention for an
undefined Bochner integral. -/
theorem BulkLoopEquations.integrable_loop
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {β : ℝ} {X : Ω → AnchoredCountingState} (h : BulkLoopEquations μ β X)
    {n : ℕ} {w : ℂ} {aux : Fin n → ℂ}
    (hw : w.im ≠ 0) (ha : ∀ j, (aux j).im ≠ 0) :
    Integrable (fun ω => loopIntegrand β (X ω) w aux) μ :=
  integrable_loop_comp μ X h.measurable_state h.moments β hw ha

theorem BulkLoopEquations.vanishing_const
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {β : ℝ}
    {X : Ω → AnchoredCountingState} (h : BulkLoopEquations μ β X) :
    VanishingHierarchy μ β (fun _ => X) := by
  intro n w hw aux ha
  simpa only [h.equation n w hw aux ha] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))

/-- A constant random variable sequence converges to its actual pushforward
law.  This elementary fact supplies the limit used for the moment estimates. -/
theorem weakLawConverges_const_probabilityLaw
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → AnchoredCountingState) (hX : Measurable X) :
    WeakLawConverges μ (fun _ => X)
      (probabilityLaw μ X hX : Measure AnchoredCountingState) := by
  intro F
  rw [integral_probabilityLaw]
  exact tendsto_const_nhds

theorem BulkLoopEquations.exact_law
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {β : ℝ} {X : Ω → AnchoredCountingState} (h : BulkLoopEquations μ β X) :
    ExactHierarchy
      (probabilityLaw μ X h.measurable_state : Measure AnchoredCountingState) β :=
  exactHierarchy_of_anchored_sequence_limit μ β (fun _ => X)
    (fun _ => h.measurable_state) (fun _ => h.moments) h.vanishing_const
    (probabilityLaw μ X h.measurable_state)
    (weakLawConverges_const_probabilityLaw μ X h.measurable_state)

/-- Exponential-square anchor integrability is a consequence of the exact
loop equations and finite moments, not an extra assumption in Theorem 1.5. -/
theorem BulkLoopEquations.exponentialSquare_law
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {β : ℝ} {X : Ω → AnchoredCountingState} (h : BulkLoopEquations μ β X) :
    ∃ a : ℝ, 0 < a ∧ Integrable
      (fun s : AnchoredCountingState => Real.exp (a * ‖s.val.2‖ ^ 2))
      (probabilityLaw μ X h.measurable_state : Measure AnchoredCountingState) :=
  exponential_anchor_of_anchored_sequence_limit μ β (fun _ => X)
    (fun _ => h.measurable_state) (fun _ => h.moments) h.vanishing_const
    (probabilityLaw μ X h.measurable_state)
    (weakLawConverges_const_probabilityLaw μ X h.measurable_state)

/-- The exact criterion identifies the full anchored state law as well as its
pole configuration. -/
theorem bourgade_huang_theorem_1_5_anchored
    (β : ℚ) (hβ : 0 < β)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → AnchoredCountingState) (h : BulkLoopEquations μ (β : ℝ) X) :
    probabilityLaw μ X h.measurable_state = sineBetaAnchoredLaw β hβ :=
  sineBetaAnchoredLaw_unique β hβ
    (probabilityLaw μ X h.measurable_state) h.exact_law h.exponentialSquare_law

/-- Bourgade--Huang Theorem 1.5: the poles of a particle-generated Nevanlinna
function satisfying the exact mixed bulk hierarchy have the Sine-beta law,
for every positive rational beta.  The conclusion is equality of probability
laws on the space of locally finite counting measures. -/
theorem bourgade_huang_theorem_1_5
    (β : ℚ) (hβ : 0 < β)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → AnchoredCountingState) (h : BulkLoopEquations μ (β : ℝ) X) :
    Measure.map (fun ω => (X ω).val.1) μ =
      (sineBetaLaw β hβ : Measure LocalCountingMeasure) := by
  have he := bourgade_huang_theorem_1_5_anchored β hβ μ X h
  unfold sineBetaLaw
  rw [← he]
  change Measure.map (fun ω => (X ω).val.1) μ =
    Measure.map (fun s : AnchoredCountingState => s.val.1) (Measure.map X μ)
  exact (Measure.map_map (measurable_fst.comp measurable_subtype_coe)
    h.measurable_state).symm

/-- Explicit hypotheses, with natural-order anchor moments.  Existence of all
the loop integrals follows from these moments and the proved Nevanlinna bounds. -/
theorem bourgade_huang_theorem_1_5_unbundled
    (β : ℚ) (hβ : 0 < β)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → AnchoredCountingState) (hX : Measurable X)
    (hm : ∀ q : ℕ, Integrable (fun ω => ‖(X ω).val.2‖ ^ q) μ)
    (hh : ∀ n : ℕ, ∀ w : ℂ, w.im ≠ 0 →
      ∀ aux : Fin n → ℂ, (∀ j, (aux j).im ≠ 0) →
        (∫ ω, loopIntegrand (β : ℝ) (X ω) w aux ∂μ) = 0) :
    Measure.map (fun ω => (X ω).val.1) μ =
      (sineBetaLaw β hβ : Measure LocalCountingMeasure) :=
  bourgade_huang_theorem_1_5 β hβ μ X ⟨hX, hm, hh⟩

/-- The paper's formulation: every positive real-order moment at every
off-real parameter is finite, and the literal equation (1.2) holds. -/
theorem bourgade_huang_theorem_1_5_paper
    (β : ℚ) (hβ : 0 < β)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → AnchoredCountingState) (hX : Measurable X)
    (hm : ∀ q : ℝ, 0 < q → ∀ w : ℂ, w.im ≠ 0 →
      Integrable (fun ω => ‖anchoredNevanlinna (X ω) w‖ ^ q) μ)
    (hh : ∀ n : ℕ, ∀ w : ℂ, w.im ≠ 0 →
      ∀ aux : Fin n → ℂ, (∀ j, (aux j).im ≠ 0) →
        (∫ ω, loopIntegrand (β : ℝ) (X ω) w aux ∂μ) = 0) :
    Measure.map (fun ω => (X ω).val.1) μ =
      (sineBetaLaw β hβ : Measure LocalCountingMeasure) := by
  apply bourgade_huang_theorem_1_5_unbundled β hβ μ X hX _ hh
  intro q
  cases q with
  | zero => simpa using (integrable_const (1 : ℝ) : Integrable _ μ)
  | succ n =>
      simpa only [anchoredNevanlinna_I, Real.rpow_natCast] using
        hm (n + 1 : ℕ) (by positivity) Complex.I (by simp)

end BourgadeHuang.RationalBulk
