import BourgadeHuang.RationalBulk.GaussianBetaLimit
import BourgadeHuang.RationalBulk.FullConvergenceReduction
import BourgadeHuang.RationalBulk.Compatibility

/-! Bourgade--Huang, Theorem 1.9, for every positive rational beta.
The event-restricted, moment-weighted approximate hierarchy is the only
probabilistic input. The target is the proved full Gaussian-beta bulk limit.
Tightness, exponential moments, the exact limiting hierarchy, rational CMS
uniqueness, and existence/identification of the target are all proved internally.
-/
noncomputable section
open scoped Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalBulk

/-- The complete criterion also gives convergence of the anchor together with
the counting configuration. No moment assumption outside the good events is used. -/
theorem bourgade_huang_theorem_1_9_anchored
    (β : ℚ) (hβ : 0 < β)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → AnchoredCountingState) (A : ℕ → Set Ω)
    (h : EventWeightedHierarchy μ (β : ℝ) X A) :
    WeakLawConverges μ X (sineBetaAnchoredLaw β hβ : Measure AnchoredCountingState) ∧
      VagueLawConverges μ (fun N ω => (X N ω).val.1)
        (sineBetaLaw β hβ : Measure LocalCountingMeasure) :=
  h.converges_of_unique (sineBetaAnchoredLaw β hβ) (sineBetaAnchoredLaw_unique β hβ)

/-- Bourgade--Huang Theorem 1.9: the full mixed bulk loop hierarchy, with
moment-weighted vanishing errors on events of probability tending to one,
implies vague convergence to Sine beta for every positive rational beta. -/
theorem bourgade_huang_theorem_1_9
    (β : ℚ) (hβ : 0 < β)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → AnchoredCountingState) (A : ℕ → Set Ω)
    (h : EventWeightedHierarchy μ (β : ℝ) X A) :
    VagueLawConverges μ (fun N ω => (X N ω).val.1)
      (sineBetaLaw β hβ : Measure LocalCountingMeasure) :=
  (bourgade_huang_theorem_1_9_anchored β hβ μ X A h).2

/-- An unbundled statement exposing every hypothesis. The anchor moment
assumption is weaker than assuming every off-real real-order moment in the
paper; the latter immediately supplies all these natural-order moments. -/
theorem bourgade_huang_theorem_1_9_unbundled
    (β : ℚ) (hβ : 0 < β)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → AnchoredCountingState) (A : ℕ → Set Ω)
    (hX : ∀ N, Measurable (X N)) (hA : ∀ N, MeasurableSet (A N))
    (hprob : Tendsto (fun N => μ.real (A N)ᶜ) atTop (𝓝 0))
    (hm : ∀ N q : ℕ, Integrable (fun ω => ‖(X N ω).val.2‖ ^ q) (μ.restrict (A N)))
    (herr : ∀ n : ℕ, ∀ K : Set ℂ, IsCompact K → (∀ z ∈ K, z.im ≠ 0) →
      ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ (∀ N, 0 ≤ ε N) ∧
        ∀ N (w : ℂ), w ∈ K → ∀ aux : Fin n → ℂ, (∀ j, aux j ∈ K) →
          ‖∫ ω, loopIntegrand (β : ℝ) (X N ω) w aux ∂(μ.restrict (A N))‖ ≤
            ε N * (1 + ∫ ω, coordinateMaximum (X N ω) w aux ^ (n+2)
              ∂(μ.restrict (A N)))) :
    VagueLawConverges μ (fun N ω => (X N ω).val.1)
      (sineBetaLaw β hβ : Measure LocalCountingMeasure) :=
  bourgade_huang_theorem_1_9 β hβ μ X A ⟨hX, hA, hprob, hm, herr⟩

/-- The paper's real-order event moments and uniform weighted error of (1.4).
The natural-order anchor moments required by the unbundled theorem follow by
evaluating the moment assumption at `i`. -/
theorem bourgade_huang_theorem_1_9_paper
    (β : ℚ) (hβ : 0 < β)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → AnchoredCountingState) (A : ℕ → Set Ω)
    (hX : ∀ N, Measurable (X N)) (hA : ∀ N, MeasurableSet (A N))
    (hprob : Tendsto (fun N => μ.real (A N)ᶜ) atTop (𝓝 0))
    (hm : ∀ N, ∀ q : ℝ, 0 < q → ∀ w : ℂ, w.im ≠ 0 →
      Integrable (fun ω => ‖anchoredNevanlinna (X N ω) w‖ ^ q) (μ.restrict (A N)))
    (herr : ∀ n : ℕ, ∀ K : Set ℂ, IsCompact K → (∀ z ∈ K, z.im ≠ 0) →
      ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ (∀ N, 0 ≤ ε N) ∧
        ∀ N (w : ℂ), w ∈ K → ∀ aux : Fin n → ℂ, (∀ j, aux j ∈ K) →
          ‖∫ ω, loopIntegrand (β : ℝ) (X N ω) w aux ∂(μ.restrict (A N))‖ ≤
            ε N * (1 + ∫ ω, coordinateMaximum (X N ω) w aux ^ (n+2)
              ∂(μ.restrict (A N)))) :
    VagueLawConverges μ (fun N ω => (X N ω).val.1)
      (sineBetaLaw β hβ : Measure LocalCountingMeasure) := by
  apply bourgade_huang_theorem_1_9_unbundled β hβ μ X A hX hA hprob _ herr
  intro N q
  cases q with
  | zero =>
      simpa only [pow_zero] using
        (integrable_const (1 : ℝ) : Integrable _ (μ.restrict (A N)))
  | succ n =>
      simpa only [anchoredNevanlinna_I, Real.rpow_natCast] using
        hm N (n + 1 : ℕ) (by positivity) Complex.I (by simp)

end BourgadeHuang.RationalBulk
