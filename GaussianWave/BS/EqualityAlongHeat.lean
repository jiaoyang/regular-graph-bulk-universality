import GaussianWave.BS.UpperBound

/-!
# Equality in the entropy upper bound forces zero heat Fisher defect

This is the first actual equality step. It uses the proved monotonicity and
both endpoint limits, rather than assuming a vanishing Fisher defect.
The subsequent smooth-density rigidity step is separate.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace GaussianWave.BS

theorem star_entropy_equality_heat_and_fisher_zero
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
        Measure.map (fun x => (starEdgeProjection d c i).mulVec x) μ)
    (hequality : initialFrameEntropy f g = 0) :
    ∀ t, 0 < t → heatFrameEntropy μ (starEdgeProjection d c) t = 0 ∧
      heatFrameFisherDefect μ (starEdgeProjection d c) t = 0 := by
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
  have hzero := tendsto_heatFrameEntropy_zero μ hμ (starEdgeProjection d c) f g
  rw [hequality] at hzero
  have hall := eq_of_monotoneOn_and_equal_endpoint_limits _ 0
    (star_heatFrameEntropy_monotone d hd c hbulk μ hμ hrev) hzero hinfty
  intro t ht
  refine ⟨hall t ht, ?_⟩
  have heq : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 t] heatFrameEntropy μ (starEdgeProjection d c) := by
    filter_upwards [eventually_gt_nhds ht] with u hu
    exact (hall u hu).symm
  have hconst := (hasDerivAt_heatFrameEntropy μ hμ (starEdgeProjection d c) ht).congr_of_eventuallyEq heq
  exact hconst.unique (hasDerivAt_const t 0)

/-- Equality already gives all of BS's observed-score constraints for each
positive heat time. The score rigidity module uses this proved conclusion. -/
theorem star_entropy_equality_scores_fixed
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
        Measure.map (fun x => (starEdgeProjection d c i).mulVec x) μ)
    (hequality : initialFrameEntropy f g = 0) {t : ℝ} (ht : 0 < t) :
    ∀ (i : Fin d) (j : Bool),
      heatDirectionalScoreL2 μ ht (starEdgeProjection d c i j) =
        conditionalScore (heatedLaw μ t)
          (MeasurableSpace.comap (fun x : Fin d → ℝ => (starEdgeProjection d c i).mulVec x) inferInstance)
          (measurable_finiteMatrixAction (starEdgeProjection d c i)).comap_le
          (heatDirectionalScoreL2 μ ht (starEdgeProjection d c i j)) :=
  star_heatFrameFisherDefect_eq_zero_scores_fixed d hd c hbulk μ ht hrev
    ((star_entropy_equality_heat_and_fisher_zero d hd c hbulk μ hμ hmom f g hrev hequality t ht).2)

end GaussianWave.BS
