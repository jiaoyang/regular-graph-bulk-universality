import GaussianWave.BS.DeBruijn
import GaussianWave.BS.HeatSymmetry

/-!
# The entropy functional and its genuine heat derivative

Each edge law here is the actual matrix pushforward of the input law. Finite
second moments of every projection are derived from the ambient second
moment. The derivative and the large-time endpoint use the proved de Bruijn
identity and Gaussian entropy squeeze. Fisher nonnegativity is a separate
geometric step; it is not asserted by these analytic identities.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace GaussianWave.BS

theorem squareRadius_matrixAction_le
    {I J : Type*} [Fintype I] [Fintype J] (O : Matrix J I ℝ) (x : I → ℝ) :
    squareRadius (O.mulVec x) ≤ (∑ j, squareRadius (O j)) * squareRadius x := by
  unfold squareRadius Matrix.mulVec dotProduct
  calc
    _ ≤ ∑ j, (∑ i, O j i ^ 2) * ∑ i, x i ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (O j) x
    _ = _ := (Finset.sum_mul ..).symm

theorem integrable_squareRadius_matrixImage
    {I J : Type*} [Fintype I] [Fintype J]
    (μ : Measure (I → ℝ)) (hμ : Integrable (squareRadius (I := I)) μ) (O : Matrix J I ℝ) :
    Integrable (squareRadius (I := J)) (Measure.map (fun x => O.mulVec x) μ) := by
  have hi : Integrable (fun x => squareRadius (O.mulVec x)) μ := by
    refine (hμ.const_mul (∑ j, squareRadius (O j))).mono'
      (continuous_squareRadius.measurable.comp (measurable_finiteMatrixAction O)).aestronglyMeasurable ?_
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (squareRadius_nonneg _)]
    exact squareRadius_matrixAction_le O x
  exact (integrable_map_measure continuous_squareRadius.measurable.aestronglyMeasurable
    (measurable_finiteMatrixAction O).aemeasurable).mpr hi

def heatFrameEntropy {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    (μ : Measure (I → ℝ)) (O : K → Matrix J I ℝ) (t : ℝ) : ℝ :=
  densityEntropy volume (heatDensity μ t) - (1 / 2 : ℝ) *
    ∑ i, densityEntropy volume (heatDensity (Measure.map (fun x => (O i).mulVec x) μ) t)

def heatFrameFisherDefect {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    (μ : Measure (I → ℝ)) (O : K → Matrix J I ℝ) (t : ℝ) : ℝ :=
  heatFisherInformation μ t - (1 / 2 : ℝ) *
    ∑ i, heatFisherInformation (Measure.map (fun x => (O i).mulVec x) μ) t

/-- The derivative of the actual star-minus-edge functional. All entropy
integrability and differentiation are consequences of the finite second
moment; there is no de Bruijn premise. -/
theorem hasDerivAt_heatFrameEntropy
    {I J K : Type*} [Fintype I] [Fintype J] [Fintype K] [DecidableEq I] [DecidableEq J]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) (O : K → Matrix J I ℝ)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (heatFrameEntropy μ O) (heatFrameFisherDefect μ O t) t := by
  classical
  letI : ∀ i, IsProbabilityMeasure (Measure.map (fun x => (O i).mulVec x) μ) :=
    fun i => isProbabilityMeasure_map (measurable_finiteMatrixAction (O i)).aemeasurable
  have hs := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    hasDerivAt_heatEntropy (Measure.map (fun x => (O i).mulVec x) μ)
      (integrable_squareRadius_matrixImage μ hμ (O i)) ht)
  exact (hasDerivAt_heatEntropy μ hμ ht).sub (hs.const_mul (1 / 2 : ℝ))

def gaussianFrameEntropyValue (I J K : Type*) [Fintype I] [Fintype J] [Fintype K] : ℝ :=
  gaussianEntropyValue I 1 - (1 / 2 : ℝ) * ∑ _i : K, gaussianEntropyValue J 1

theorem gaussianFrameEntropyValue_eq_zero
    (I J K : Type*) [Fintype I] [Fintype J] [Fintype K]
    (hdim : (Fintype.card I : ℝ) =
      (1 / 2 : ℝ) * (Fintype.card K : ℝ) * (Fintype.card J : ℝ)) :
    gaussianFrameEntropyValue I J K = 0 := by
  unfold gaussianFrameEntropyValue gaussianEntropyValue
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hdim]
  ring

/-- The dimension cancellation and the actual Gaussian entropy squeeze give
the large-time endpoint of the star-minus-edge functional. The trace
equalities are ordinary second-moment normalization, not Gaussianity. -/
theorem tendsto_heatFrameEntropy_atTop
    {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) (O : K → Matrix J I ℝ)
    (htrace : (∫ x, squareRadius x ∂μ) = (Fintype.card I : ℝ))
    (htraceEdge : ∀ i, (∫ x, squareRadius x
      ∂Measure.map (fun y => (O i).mulVec y) μ) = (Fintype.card J : ℝ))
    (hdim : (Fintype.card I : ℝ) =
      (1 / 2 : ℝ) * (Fintype.card K : ℝ) * (Fintype.card J : ℝ)) :
    Tendsto (heatFrameEntropy μ O) atTop (𝓝 (gaussianFrameEntropyValue I J K)) := by
  classical
  letI : ∀ i, IsProbabilityMeasure (Measure.map (fun x => (O i).mulVec x) μ) :=
    fun i => isProbabilityMeasure_map (measurable_finiteMatrixAction (O i)).aemeasurable
  have ha := tendsto_normalized_heatDensity_entropy_atTop μ hμ htrace
  have he := tendsto_finset_sum Finset.univ (fun i _ =>
    tendsto_normalized_heatDensity_entropy_atTop
      (Measure.map (fun x => (O i).mulVec x) μ)
      (integrable_squareRadius_matrixImage μ hμ (O i)) (htraceEdge i))
  have hh := ha.sub (he.const_mul (1 / 2 : ℝ))
  convert hh using 1
  funext t
  unfold heatFrameEntropy
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hdim]
  ring

end GaussianWave.BS
