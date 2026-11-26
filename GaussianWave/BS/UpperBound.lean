import GaussianWave.BS.FisherMonotonicity
import GaussianWave.BS.EntropyComparison

/-!
# BS's entropy upper bound in actual white coordinates

This is the upper inequality itself, not an implication from a de Bruijn,
Fisher, Gaussianity, or entropy-maximization hypothesis. The heat convolution,
score projection, weighted frame, entropy differentiation, and both entropy
endpoints have all been proved in the preceding modules.

The source energy parameter is λ=d*c. The strict-bulk condition is written in
its squared normalized form. The proof only needs reversal of each edge law;
neighbor permutation symmetry is not needed for this averaged-edge inequality.
The original intrinsic entropy differs by the fixed whitening Jacobians.
Their Gaussian-relative cancellation is a separate change-of-variables adapter.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace GaussianWave.BS

/-- The actual BS star-minus-edge entropy increases along its heat flow. -/
theorem star_heatFrameEntropy_monotone
    (d : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := Fin d)) μ)
    (hrev : ∀ i, Measure.map binarySwap
      (Measure.map (fun x => (starEdgeProjection d c i).mulVec x) μ) =
        Measure.map (fun x => (starEdgeProjection d c i).mulVec x) μ) :
    MonotoneOn (heatFrameEntropy μ (starEdgeProjection d c)) (Set.Ioi 0) :=
  monotoneOn_heatFrameEntropy_of_fisher_nonneg μ hμ (starEdgeProjection d c)
    (fun _ ht => star_heatFrameFisherDefect_nonneg d hd c hbulk μ ht hrev)

/-- The heated upper bound needs no density or finite entropy of the original
law. This form is useful for the lower-bound/classification stage. -/
theorem star_heatFrameEntropy_nonpos
    (d : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hmom : HasIdentitySecondMoments μ)
    (hrev : ∀ i, Measure.map binarySwap
      (Measure.map (fun x => (starEdgeProjection d c i).mulVec x) μ) =
        Measure.map (fun x => (starEdgeProjection d c i).mulVec x) μ)
    {t : ℝ} (ht : 0 < t) : heatFrameEntropy μ (starEdgeProjection d c) t ≤ 0 := by
  have hμ := integrable_squareRadius_of_identitySecondMoments μ hmom
  have hc := (bulk_rho_lower d hd c hbulk).1
  have hdim : (Fintype.card (Fin d) : ℝ) =
      (1 / 2 : ℝ) * (Fintype.card (Fin d) : ℝ) * (Fintype.card Bool : ℝ) := by
    simp only [Fintype.card_fin, Fintype.card_bool]
    ring
  have hinfty := tendsto_heatFrameEntropy_atTop μ hμ (starEdgeProjection d c)
    (integral_squareRadius_of_identitySecondMoments μ hμ hmom)
    (fun i => integral_squareRadius_projection_of_identitySecondMoments μ hμ hmom
      (starEdgeProjection d c i) (starEdgeProjection_mul_transpose d (by omega) c hc i)) hdim
  rw [gaussianFrameEntropyValue_eq_zero _ _ _ hdim] at hinfty
  apply ge_of_tendsto hinfty
  filter_upwards [eventually_ge_atTop t] with u hu
  exact star_heatFrameEntropy_monotone d hd c hbulk μ hμ hrev ht (lt_of_lt_of_le ht hu) hu

/-- The actual white-coordinate BS entropy upper inequality, together with its
positive-time version. All assumptions are ordinary law, moment, symmetry,
and finite-entropy hypotheses from the statement of the extremal problem. -/
theorem star_entropy_upper_and_heated_upper
    (d : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := Fin d)) μ)
    (hmom : HasIdentitySecondMoments μ)
    (f : FiniteEntropyDensity μ)
    (g : ∀ i, FiniteEntropyDensity
      (Measure.map (fun x => (starEdgeProjection d c i).mulVec x) μ))
    (hrev : ∀ i, Measure.map binarySwap
      (Measure.map (fun x => (starEdgeProjection d c i).mulVec x) μ) =
        Measure.map (fun x => (starEdgeProjection d c i).mulVec x) μ) :
    initialFrameEntropy f g ≤ 0 ∧
      ∀ t, 0 < t → heatFrameEntropy μ (starEdgeProjection d c) t ≤ 0 := by
  have hc := (bulk_rho_lower d hd c hbulk).1
  have hdim : (Fintype.card (Fin d) : ℝ) =
      (1 / 2 : ℝ) * (Fintype.card (Fin d) : ℝ) * (Fintype.card Bool : ℝ) := by
    simp only [Fintype.card_fin, Fintype.card_bool]
    ring
  have hinfty := tendsto_heatFrameEntropy_atTop μ hμ (starEdgeProjection d c)
    (integral_squareRadius_of_identitySecondMoments μ hμ hmom)
    (fun i => integral_squareRadius_projection_of_identitySecondMoments μ hμ hmom
      (starEdgeProjection d c i) (starEdgeProjection_mul_transpose d (by omega) c hc i)) hdim
  rw [gaussianFrameEntropyValue_eq_zero _ _ _ hdim] at hinfty
  exact endpoint_comparison_of_monotoneOn _ _ _
    (star_heatFrameEntropy_monotone d hd c hbulk μ hμ hrev)
    (tendsto_heatFrameEntropy_zero μ hμ (starEdgeProjection d c) f g) hinfty

/-- BS upper bound: the Gaussian value of the white-coordinate entropy
functional is zero by the proved dimension cancellation. -/
theorem star_entropy_upper
    (d : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := Fin d)) μ)
    (hmom : HasIdentitySecondMoments μ)
    (f : FiniteEntropyDensity μ)
    (g : ∀ i, FiniteEntropyDensity
      (Measure.map (fun x => (starEdgeProjection d c i).mulVec x) μ))
    (hrev : ∀ i, Measure.map binarySwap
      (Measure.map (fun x => (starEdgeProjection d c i).mulVec x) μ) =
        Measure.map (fun x => (starEdgeProjection d c i).mulVec x) μ) :
    f.entropy ≤ (1 / 2 : ℝ) * ∑ i, (g i).entropy := by
  have h := (star_entropy_upper_and_heated_upper d hd c hbulk μ hμ hmom f g hrev).1
  exact sub_nonpos.mp h

end GaussianWave.BS
