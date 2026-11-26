import GaussianWave.BS.ColoredSteinFactorization
import GaussianWave.BS.ColoredUpperBound
import GaussianWave.BS.GaussianEntropyWitness

/-!
# Genuine joint Gaussian equality for the common-energy BS upper bound

The characteristic argument covers every coefficient matrix in the full
channel-by-star space. There is no reduction to rank-one tests, and no
independence assumption on the unknown channels. Rank zero is included.
-/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace GaussianWave.BS

theorem colored_star_eq_standardVector_of_fisherDefect_zero
    (d r : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (μ : Measure ((Fin r × Fin d) → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := Fin r × Fin d)) μ) (hmom : HasIdentitySecondMoments μ)
    {t : ℝ} (ht : 0 < t)
    (hrev : ∀ i, Measure.map (edgeFlipLinear r)
      (Measure.map (fun x => (coloredStarEdgeProjection d r c i).mulVec x) μ) =
        Measure.map (fun x => (coloredStarEdgeProjection d r c i).mulVec x) μ)
    (hzero : heatFrameFisherDefect μ (coloredStarEdgeProjection d r c) t = 0)
    (hperm : ∀ p : Equiv.Perm (Fin d),
      Measure.map (fun x : (Fin r × Fin d) → ℝ => fun q => x (q.1, p q.2)) μ = μ) :
    μ = standardVector (Fin r × Fin d) := by
  by_cases hr : r = 0
  · subst r
    exact eq_standardVector_of_empty_coordinates _ μ
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
    let v := heatVariance (t + 1 / 2)
    have hv : (v : ℝ) = 1 + 2 * t := by
      change max (2 * (t + 1 / 2)) 0 = 1 + 2 * t
      rw [max_eq_left (by linarith)]
      ring
    have hfactor : ∀ w : ColoredSpace d r, (∀ a, ∑ j, w (a, j) = 0) → squareRadius w = 1 →
        ∀ a : Fin r → ℝ, ∀ s : ℝ,
        characteristicIntegral (heatedLaw μ t) (coloredRootLift d r a + s • w) =
          characteristicIntegral (Measure.map (coloredStarRootForm d r) (heatedLaw μ t)) a *
            Complex.exp (Complex.ofReal (-(1 / 2 : ℝ) * (v : ℝ) * s ^ 2)) := by
      intro w hw hunit a s
      rw [colored_star_characteristic_transverse_factorization_of_fisherDefect_zero
        d r hd c hbulk μ hμ hmom ht hrev hzero hperm w hw hunit a s, hv]
    let i₀ : Fin d := ⟨0, by omega⟩
    have hheated := colored_heated_gaussian_of_transverse_characteristics_and_reversal
      d r (by omega) hrpos μ t v c (bulk_rho_lower d hd c hbulk).1 i₀ hfactor (hrev i₀)
    have htime : (v : ℝ) / 2 = t + 1 / 2 := by rw [hv]; ring
    rw [htime] at hheated
    exact eq_standardVector_of_heatedLaw_eq_heatGaussian μ ht hheated

theorem colored_star_initialFrameEntropy_standardVector_eq_zero
    (d r : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1)
    (f : FiniteEntropyDensity (standardVector (Fin r × Fin d)))
    (g : ∀ i, FiniteEntropyDensity
      (Measure.map (fun x => (coloredStarEdgeProjection d r c i).mulVec x) (standardVector (Fin r × Fin d)))) :
    initialFrameEntropy f g = 0 := by
  have hf : f.entropy = gaussianEntropyValue (Fin r × Fin d) 1 := by
    rw [f.entropy_eq_of_measure_eq (standardVectorEntropyDensity _) rfl,
      standardVectorEntropyDensity_entropy]
  have hg (i : Fin d) : (g i).entropy = gaussianEntropyValue (Bool × Fin r) 1 := by
    rw [(g i).entropy_eq_of_measure_eq (standardVectorEntropyDensity _)
      (standardVector_map_orthonormal_rows _ (coloredStarEdgeProjection_mul_transpose d r hd c hc i)),
      standardVectorEntropyDensity_entropy]
  unfold initialFrameEntropy
  rw [hf]
  simp_rw [hg]
  apply gaussianFrameEntropyValue_eq_zero (Fin r × Fin d) (Bool × Fin r) (Fin d)
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Nat.cast_mul]
  ring

/-- The full joint common-energy equality theorem. All cross-channel
dependence is derived to be Gaussian; it is not supplied by the caller. -/
theorem colored_star_entropy_equality_iff_standardVector
    (d r : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (μ : Measure ((Fin r × Fin d) → ℝ)) [IsProbabilityMeasure μ]
    (hmom : HasIdentitySecondMoments μ)
    (f : FiniteEntropyDensity μ)
    (g : ∀ i, FiniteEntropyDensity
      (Measure.map (fun x => (coloredStarEdgeProjection d r c i).mulVec x) μ))
    (hrev : ∀ i, Measure.map (edgeFlipLinear r)
      (Measure.map (fun x => (coloredStarEdgeProjection d r c i).mulVec x) μ) =
        Measure.map (fun x => (coloredStarEdgeProjection d r c i).mulVec x) μ)
    (hperm : ∀ p : Equiv.Perm (Fin d),
      Measure.map (fun x : (Fin r × Fin d) → ℝ => fun q => x (q.1, p q.2)) μ = μ) :
    initialFrameEntropy f g = 0 ↔ μ = standardVector (Fin r × Fin d) := by
  constructor
  · intro hequality
    have hμ := integrable_squareRadius_of_identitySecondMoments μ hmom
    have hzero := (colored_star_entropy_equality_heat_and_fisher_zero d r hd c hbulk μ hμ hmom f g hrev
      hequality 1 zero_lt_one).2
    exact colored_star_eq_standardVector_of_fisherDefect_zero d r hd c hbulk μ hμ hmom zero_lt_one hrev hzero hperm
  · intro hμ
    subst μ
    exact colored_star_initialFrameEntropy_standardVector_eq_zero d r (by omega) c
      (bulk_rho_lower d hd c hbulk).1 f g

/-- Regularized strictness for arbitrary original probability laws with the
stated second moments and symmetries, including initially singular laws. -/
theorem colored_star_eq_standardVector_of_heated_entropy_zero
    (d r : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (μ : Measure ((Fin r × Fin d) → ℝ)) [IsProbabilityMeasure μ]
    (hmom : HasIdentitySecondMoments μ)
    (hrev : ∀ i, Measure.map (edgeFlipLinear r)
      (Measure.map (fun x => (coloredStarEdgeProjection d r c i).mulVec x) μ) =
        Measure.map (fun x => (coloredStarEdgeProjection d r c i).mulVec x) μ)
    (hperm : ∀ p : Equiv.Perm (Fin d),
      Measure.map (fun x : (Fin r × Fin d) → ℝ => fun q => x (q.1, p q.2)) μ = μ)
    {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hequality : heatFrameEntropy μ (coloredStarEdgeProjection d r c) t₀ = 0) :
    μ = standardVector (Fin r × Fin d) := by
  have hμ := integrable_squareRadius_of_identitySecondMoments μ hmom
  have hmono := colored_star_heatFrameEntropy_monotone d r hd c hbulk μ hμ hrev
  have hconst (u : ℝ) (hu : t₀ < u) : heatFrameEntropy μ (coloredStarEdgeProjection d r c) u = 0 := by
    apply le_antisymm (colored_star_heatFrameEntropy_nonpos d r hd c hbulk μ hmom hrev (ht₀.trans hu))
    rw [← hequality]
    exact hmono ht₀ (ht₀.trans hu) hu.le
  have hu : 0 < t₀ + 1 := by linarith
  have heq : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 (t₀ + 1)] heatFrameEntropy μ (coloredStarEdgeProjection d r c) := by
    filter_upwards [eventually_gt_nhds (by linarith : t₀ < t₀ + 1)] with u hu'
    exact (hconst u hu').symm
  have hzero := ((hasDerivAt_heatFrameEntropy μ hμ (coloredStarEdgeProjection d r c) hu).congr_of_eventuallyEq heq).unique
    (hasDerivAt_const (t₀ + 1) 0)
  exact colored_star_eq_standardVector_of_fisherDefect_zero d r hd c hbulk μ hμ hmom hu hrev hzero hperm

theorem colored_star_heated_entropy_equality_iff_standardVector
    (d r : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (μ : Measure ((Fin r × Fin d) → ℝ)) [IsProbabilityMeasure μ]
    (hmom : HasIdentitySecondMoments μ)
    (hrev : ∀ i, Measure.map (edgeFlipLinear r)
      (Measure.map (fun x => (coloredStarEdgeProjection d r c i).mulVec x) μ) =
        Measure.map (fun x => (coloredStarEdgeProjection d r c i).mulVec x) μ)
    (hperm : ∀ p : Equiv.Perm (Fin d),
      Measure.map (fun x : (Fin r × Fin d) → ℝ => fun q => x (q.1, p q.2)) μ = μ)
    {t : ℝ} (ht : 0 < t) :
    heatFrameEntropy μ (coloredStarEdgeProjection d r c) t = 0 ↔ μ = standardVector (Fin r × Fin d) := by
  constructor
  · exact colored_star_eq_standardVector_of_heated_entropy_zero d r hd c hbulk μ hmom hrev hperm ht
  · intro hμ
    subst μ
    let f := standardVectorEntropyDensity (Fin r × Fin d)
    let g := fun i : Fin d => (standardVectorEntropyDensity (Bool × Fin r)).cast
      (standardVector_map_orthonormal_rows _
        (coloredStarEdgeProjection_mul_transpose d r (by omega) c (bulk_rho_lower d hd c hbulk).1 i))
    exact (colored_star_entropy_equality_heat_and_fisher_zero d r hd c hbulk _
      (integrable_squareRadius_of_identitySecondMoments _ hmom) hmom f g hrev
      (colored_star_initialFrameEntropy_standardVector_eq_zero d r (by omega) c
        (bulk_rho_lower d hd c hbulk).1 f g) t ht).1

end GaussianWave.BS
