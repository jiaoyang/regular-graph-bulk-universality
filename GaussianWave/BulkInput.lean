import GaussianWave.UniformStars
import GaussianWave.StarQuadraticInput

/-!
# The reduced quantitative input implies uniform normalized Gaussian stars

The only probabilistic source inputs in this theorem are the explicit
qualitative BS classification on common good events and the reduced one-edge
quadratic bound on another common good event. The root fourth bound and the
uniform Wasserstein conclusion are proved consequences.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ENNReal

namespace GaussianWave

/-- Separate high-probability graph events may be intersected. -/
theorem bad_probability_inter_tendsto_zero
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (A B : ∀ n, Set (Ω n))
    (hA : Tendsto (fun n => (P n (A n)ᶜ).toReal) atTop (𝓝 0))
    (hB : Tendsto (fun n => (P n (B n)ᶜ).toReal) atTop (𝓝 0)) :
    Tendsto (fun n => (P n (A n ∩ B n)ᶜ).toReal) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => ENNReal.toReal_nonneg)
    (fun n => ?_) (by simpa using hA.add hB)
  rw [Set.compl_inter]
  have h := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨measure_ne_top (P n) _, measure_ne_top (P n) _⟩)
    (measure_union_le (μ := P n) ((A n)ᶜ) ((B n)ᶜ))
  rwa [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at h

/-- A source-faithful qualitative classification uniform over good graphs
and candidate eigenvector selections. No variance normalization is included. -/
def UniformBSOn
    {d k : ℕ} {N : ℕ → ℕ} {Ω : ℕ → Type*}
    {S : ∀ n, Ω n → Type*}
    (D : ∀ n ω, S n ω → RegularEigenData d (N n) k)
    (K : Set ℝ) (δ : ℕ → ℝ) (good : ∀ n, Set (Ω n)) : Prop :=
  ∀ r : ℕ → ℕ, StrictMono r → ∀ ω : ∀ j, Ω (r j),
    ∀ s : ∀ j, S (r j) (ω j),
    (∀ j, ω j ∈ good (r j)) →
    (∀ j, StarAdmissible (D (r j) (ω j) (s j)) K (δ (r j))) →
    ∀ E ∈ K, (∀ i, Tendsto (fun j => (D (r j) (ω j) (s j)).eigenvalue i)
      atTop (𝓝 E)) →
    BSJointClassification (fun j => (D (r j) (ω j) (s j)).eigenStarLaw)

/-- The bulk eigenvector input: an explicit one-edge quadratic estimate,
together with published qualitative classification, yields the uniform
normalized, independent-channel Gaussian star limit in graph probability.

The error only needs to tend to zero for this qualitative conclusion.
Polynomial decay is used separately in the spectral-tail summation step.
-/
theorem uniformStar_wasserstein_of_oneEdgeQuadraticBound
    {d k : ℕ} (hd : 3 ≤ d) (hk : 0 < k) (leaf : Fin d)
    (N : ℕ → ℕ) {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (S : ∀ n, Ω n → Type*)
    (D : ∀ n ω, S n ω → RegularEigenData d (N n) k)
    (K : Set ℝ) (hK : IsCompact K) (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0))
    (bsGood qGood : ∀ n, Set (Ω n))
    (hbsBad : Tendsto (fun n => (P n (bsGood n)ᶜ).toReal) atTop (𝓝 0))
    (hqBad : Tendsto (fun n => (P n (qGood n)ᶜ).toReal) atTop (𝓝 0))
    (C : ℝ) (err : ℕ → ℝ) (herr : Tendsto err atTop (𝓝 0))
    (hQ : ∀ n ω s, ω ∈ qGood n → StarAdmissible (D n ω s) K (δ n) →
      (D n ω s).OneEdgeQuadraticBound leaf C (err n))
    (BS : UniformBSOn D K δ bsGood) :
    ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun n =>
      (P n {ω | ∃ s : S n ω, StarAdmissible (D n ω s) K (δ n) ∧
        ε ≤ wassersteinTwo (D n ω s).eigenStarLaw
          ((D n ω s).eigenStarGaussian (by omega))}).toReal) atTop (𝓝 0) := by
  let good : ∀ n, Set (Ω n) := fun n =>
    {ω | ω ∈ bsGood n ∧ ω ∈ qGood n ∧ err n ≤ 1}
  have hsmall : ∀ᶠ n in atTop, err n ≤ 1 :=
    ((tendsto_order.mp herr).2 1 zero_lt_one).mono fun _ h => h.le
  have hbad : Tendsto (fun n => (P n (good n)ᶜ).toReal) atTop (𝓝 0) := by
    apply (bad_probability_inter_tendsto_zero P bsGood qGood hbsBad hqBad).congr'
    filter_upwards [hsmall] with n hn
    have heq : good n = bsGood n ∩ qGood n := by
      ext ω
      simp only [good, Set.mem_setOf_eq, Set.mem_inter_iff]
      tauto
    rw [heq]
  have htight : TightInProbability P (fun _ _ => C + 2) := by
    intro ε hε
    refine ⟨C + 2, Eventually.of_forall (fun n => ?_)⟩
    simpa using hε
  apply uniform_normalizedStar_wasserstein_inProbability hd hk N P S D
    K hK δ hδ good hbad (fun _ _ => C + 2) htight
  · intro n ω s hg hadm i
    have hroot := (D n ω s).scalar_fourth_le_of_oneEdgeQuadraticBound leaf C (err n)
      (hQ n ω s hg.2.1 hadm) i
    linarith [hg.2.2]
  · intro r hr ω s hg hadm E hEK hEig
    exact BS r hr ω s (fun j => (hg j).1) hadm E hEK hEig

/-- The polynomial rate absorbs the mesoscopic absolute-sum loss when
`2 ε < χ`. Sizes may be arbitrary positive real numbers tending to infinity. -/
theorem polynomial_quadratic_error_tendsto_zero
    (size : ℕ → ℝ) (hsize : Tendsto size atTop atTop)
    (hpos : ∀ n, 0 < size n) (χ ε : ℝ) (hgap : 2 * ε < χ) :
    Tendsto (fun n => (size n) ^ (-χ) * (size n) ^ (2 * ε)) atTop (𝓝 0) := by
  have hlim := (tendsto_rpow_neg_atTop (show 0 < χ - 2 * ε by linarith)).comp hsize
  convert hlim using 1
  funext n
  rw [← Real.rpow_add (hpos n)]
  congr 1
  ring

end GaussianWave
