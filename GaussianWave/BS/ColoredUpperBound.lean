import GaussianWave.BS.ColoredFisherMonotonicity
import GaussianWave.BS.EntropyComparison

/-!
# The actual common-energy multichannel BS entropy upper bound

The whitened ambient space has r channels and d scalar star coordinates per
channel. Each edge observation keeps all 2r coordinates simultaneously.
All joint laws are allowed; channel independence is not a hypothesis.
Whitening Jacobians in physical intrinsic coordinates are a separate adapter.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace GaussianWave.BS

theorem colored_star_heatFrameEntropy_monotone
    (d r : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (μ : Measure ((Fin r × Fin d) → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := Fin r × Fin d)) μ)
    (hrev : ∀ i, Measure.map (edgeFlipLinear r)
      (Measure.map (fun x => (coloredStarEdgeProjection d r c i).mulVec x) μ) =
        Measure.map (fun x => (coloredStarEdgeProjection d r c i).mulVec x) μ) :
    MonotoneOn (heatFrameEntropy μ (coloredStarEdgeProjection d r c)) (Set.Ioi 0) :=
  monotoneOn_heatFrameEntropy_of_fisher_nonneg μ hμ (coloredStarEdgeProjection d r c)
    (fun _ ht => colored_star_heatFrameFisherDefect_nonneg d r hd c hbulk μ ht hrev)

theorem colored_star_dimension_cancellation (d r : ℕ) :
    (Fintype.card (Fin r × Fin d) : ℝ) =
      (1 / 2 : ℝ) * (Fintype.card (Fin d) : ℝ) * (Fintype.card (Bool × Fin r) : ℝ) := by
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat]
  ring

/-- No original density or finite entropy is required for the regularized
upper bound. All positive-time entropies are supplied by actual heat flow. -/
theorem colored_star_heatFrameEntropy_nonpos
    (d r : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (μ : Measure ((Fin r × Fin d) → ℝ)) [IsProbabilityMeasure μ]
    (hmom : HasIdentitySecondMoments μ)
    (hrev : ∀ i, Measure.map (edgeFlipLinear r)
      (Measure.map (fun x => (coloredStarEdgeProjection d r c i).mulVec x) μ) =
        Measure.map (fun x => (coloredStarEdgeProjection d r c i).mulVec x) μ)
    {t : ℝ} (ht : 0 < t) : heatFrameEntropy μ (coloredStarEdgeProjection d r c) t ≤ 0 := by
  have hμ := integrable_squareRadius_of_identitySecondMoments μ hmom
  have hc := (bulk_rho_lower d hd c hbulk).1
  have hdim := colored_star_dimension_cancellation d r
  have hinfty := tendsto_heatFrameEntropy_atTop μ hμ (coloredStarEdgeProjection d r c)
    (integral_squareRadius_of_identitySecondMoments μ hμ hmom)
    (fun i => integral_squareRadius_projection_of_identitySecondMoments μ hμ hmom
      (coloredStarEdgeProjection d r c i)
      (coloredStarEdgeProjection_mul_transpose d r (by omega) c hc i)) hdim
  rw [gaussianFrameEntropyValue_eq_zero _ _ _ hdim] at hinfty
  apply ge_of_tendsto hinfty
  filter_upwards [eventually_ge_atTop t] with u hu
  exact colored_star_heatFrameEntropy_monotone d r hd c hbulk μ hμ hrev ht (lt_of_lt_of_le ht hu) hu

/-- The actual multichannel upper inequality, including every positive heat
time. Its hypotheses are the ordinary law, second moments, finite entropy,
and simultaneous edge reversal of the extremal problem. -/
theorem colored_star_entropy_upper_and_heated_upper
    (d r : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (μ : Measure ((Fin r × Fin d) → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := Fin r × Fin d)) μ)
    (hmom : HasIdentitySecondMoments μ)
    (f : FiniteEntropyDensity μ)
    (g : ∀ i, FiniteEntropyDensity
      (Measure.map (fun x => (coloredStarEdgeProjection d r c i).mulVec x) μ))
    (hrev : ∀ i, Measure.map (edgeFlipLinear r)
      (Measure.map (fun x => (coloredStarEdgeProjection d r c i).mulVec x) μ) =
        Measure.map (fun x => (coloredStarEdgeProjection d r c i).mulVec x) μ) :
    initialFrameEntropy f g ≤ 0 ∧
      ∀ t, 0 < t → heatFrameEntropy μ (coloredStarEdgeProjection d r c) t ≤ 0 := by
  have hc := (bulk_rho_lower d hd c hbulk).1
  have hdim := colored_star_dimension_cancellation d r
  have hinfty := tendsto_heatFrameEntropy_atTop μ hμ (coloredStarEdgeProjection d r c)
    (integral_squareRadius_of_identitySecondMoments μ hμ hmom)
    (fun i => integral_squareRadius_projection_of_identitySecondMoments μ hμ hmom
      (coloredStarEdgeProjection d r c i)
      (coloredStarEdgeProjection_mul_transpose d r (by omega) c hc i)) hdim
  rw [gaussianFrameEntropyValue_eq_zero _ _ _ hdim] at hinfty
  exact endpoint_comparison_of_monotoneOn _ _ _
    (colored_star_heatFrameEntropy_monotone d r hd c hbulk μ hμ hrev)
    (tendsto_heatFrameEntropy_zero μ hμ (coloredStarEdgeProjection d r c) f g) hinfty

/-- BS's upper entropy bound in whitened common-energy multichannel
coordinates, without independence between the channels. -/
theorem colored_star_entropy_upper
    (d r : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (μ : Measure ((Fin r × Fin d) → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := Fin r × Fin d)) μ)
    (hmom : HasIdentitySecondMoments μ)
    (f : FiniteEntropyDensity μ)
    (g : ∀ i, FiniteEntropyDensity
      (Measure.map (fun x => (coloredStarEdgeProjection d r c i).mulVec x) μ))
    (hrev : ∀ i, Measure.map (edgeFlipLinear r)
      (Measure.map (fun x => (coloredStarEdgeProjection d r c i).mulVec x) μ) =
        Measure.map (fun x => (coloredStarEdgeProjection d r c i).mulVec x) μ) :
    f.entropy ≤ (1 / 2 : ℝ) * ∑ i, (g i).entropy := by
  exact sub_nonpos.mp
    (colored_star_entropy_upper_and_heated_upper d r hd c hbulk μ hμ hmom f g hrev).1

/-- Equality in the actual colored upper bound forces zero actual heat
Fisher defect at every positive time. -/
theorem colored_star_entropy_equality_heat_and_fisher_zero
    (d r : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (μ : Measure ((Fin r × Fin d) → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := Fin r × Fin d)) μ)
    (hmom : HasIdentitySecondMoments μ)
    (f : FiniteEntropyDensity μ)
    (g : ∀ i, FiniteEntropyDensity
      (Measure.map (fun x => (coloredStarEdgeProjection d r c i).mulVec x) μ))
    (hrev : ∀ i, Measure.map (edgeFlipLinear r)
      (Measure.map (fun x => (coloredStarEdgeProjection d r c i).mulVec x) μ) =
        Measure.map (fun x => (coloredStarEdgeProjection d r c i).mulVec x) μ)
    (hequality : initialFrameEntropy f g = 0) :
    ∀ t, 0 < t → heatFrameEntropy μ (coloredStarEdgeProjection d r c) t = 0 ∧
      heatFrameFisherDefect μ (coloredStarEdgeProjection d r c) t = 0 := by
  have hc := (bulk_rho_lower d hd c hbulk).1
  have hdim := colored_star_dimension_cancellation d r
  have hinfty := tendsto_heatFrameEntropy_atTop μ hμ (coloredStarEdgeProjection d r c)
    (integral_squareRadius_of_identitySecondMoments μ hμ hmom)
    (fun i => integral_squareRadius_projection_of_identitySecondMoments μ hμ hmom
      (coloredStarEdgeProjection d r c i)
      (coloredStarEdgeProjection_mul_transpose d r (by omega) c hc i)) hdim
  rw [gaussianFrameEntropyValue_eq_zero _ _ _ hdim] at hinfty
  have hzero := tendsto_heatFrameEntropy_zero μ hμ (coloredStarEdgeProjection d r c) f g
  rw [hequality] at hzero
  have hall := eq_of_monotoneOn_and_equal_endpoint_limits _ 0
    (colored_star_heatFrameEntropy_monotone d r hd c hbulk μ hμ hrev) hzero hinfty
  intro t ht
  refine ⟨hall t ht, ?_⟩
  have heq : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 t] heatFrameEntropy μ (coloredStarEdgeProjection d r c) := by
    filter_upwards [eventually_gt_nhds ht] with u hu
    exact (hall u hu).symm
  have hconst := (hasDerivAt_heatFrameEntropy μ hμ (coloredStarEdgeProjection d r c) ht).congr_of_eventuallyEq heq
  exact hconst.unique (hasDerivAt_const t 0)

end GaussianWave.BS
