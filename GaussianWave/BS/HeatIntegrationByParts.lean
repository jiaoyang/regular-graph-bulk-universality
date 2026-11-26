import GaussianWave.BS.MixtureFisher

/-!
# Spatial integration by parts along the genuine heat flow

The Fisher terms below are already integrable by MixtureFisher, with no
moment assumption. The logarithm-weighted terms needed for entropy are
explicit in the intermediate spatial identity and will be supplied by the
finite-second-moment heat estimates in the de Bruijn module.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianWave.BS

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem integrable_heatDensityGradient
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t) (i : I) :
    Integrable (fun x => heatDensityGradient μ t x i) := by
  refine ((integrable_heatFisherCoordinate μ ht i).add (integrable_heatDensity μ ht)).mono'
    (measurable_heatDensityGradient μ t i).aestronglyMeasurable ?_
  filter_upwards [] with x
  have hf := heatDensity_pos μ ht x
  change |heatDensityGradient μ t x i| ≤
    heatDensityGradient μ t x i ^ 2 / heatDensity μ t x + heatDensity μ t x
  have hsq := sq_nonneg (|heatDensityGradient μ t x i| - heatDensity μ t x)
  apply (mul_le_mul_right hf).mp
  have heq : (heatDensityGradient μ t x i ^ 2 / heatDensity μ t x + heatDensity μ t x) *
      heatDensity μ t x = heatDensityGradient μ t x i ^ 2 + heatDensity μ t x ^ 2 := by
    field_simp
    ring
  rw [heq]
  nlinarith [sq_abs (heatDensityGradient μ t x i)]

theorem heatDensityHessian_diagonal_eq
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t)
    (i : I) (x : I → ℝ) :
    heatDensityHessian μ t x i i =
      (∫ y, heatNoiseFisherKernel t i (x - y) ∂μ) - heatDensity μ t x / (2 * t) := by
  unfold heatDensityHessian
  have heq : (fun y => heatKernelHessian t (x - y) i i) =
      (fun y => heatNoiseFisherKernel t i (x - y) - heatKernel t (x - y) / (2 * t)) := by
    funext y
    simp only [heatKernelHessian, if_pos rfl, heatNoiseFisherKernel, ite_true]
    ring
  rw [heq, integral_sub (f := fun y => heatNoiseFisherKernel t i (x - y))
    (integrable_heatNoiseFisherKernel_shift μ ht i x)
    ((integrable_heatKernel_shift μ t x).div_const _), integral_div]
  rfl

theorem integrable_heatDensityHessian_diagonal
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t) (i : I) :
    Integrable (fun x => heatDensityHessian μ t x i i) := by
  simp_rw [heatDensityHessian_diagonal_eq μ ht i]
  exact (integrable_heatNoiseFisherMixture μ ht i).sub
    ((integrable_heatDensity μ ht).div_const _)

theorem integral_heatDensityHessian_diagonal_eq_zero
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t) (i : I) :
    (∫ x, heatDensityHessian μ t x i i) = 0 := by
  simp_rw [heatDensityHessian_diagonal_eq μ ht i]
  rw [integral_sub (f := fun x => ∫ y, heatNoiseFisherKernel t i (x - y) ∂μ)
    (integrable_heatNoiseFisherMixture μ ht i)
    ((integrable_heatDensity μ ht).div_const _),
    integral_heatNoiseFisherMixture μ ht i, integral_div, integral_heatDensity μ ht]
  ring

theorem hasLineDerivAt_log_heatDensity_coordinate
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t)
    (x : I → ℝ) (i : I) :
    HasLineDerivAt ℝ (fun y => Real.log (heatDensity μ t y))
      (heatDensityGradient μ t x i / heatDensity μ t x) x (Pi.single i 1) := by
  have h := hasDerivAt_heatDensity_coordinate μ ht x i 0
  simp only [zero_smul, add_zero] at h
  simpa only [HasLineDerivAt, zero_smul, add_zero] using h.log
    (by simpa only [zero_smul, add_zero] using (heatDensity_pos μ ht x).ne')

theorem hasLineDerivAt_heatDensityGradient_coordinate
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t)
    (x : I → ℝ) (i : I) :
    HasLineDerivAt ℝ (fun y => heatDensityGradient μ t y i)
      (heatDensityHessian μ t x i i) x (Pi.single i 1) := by
  simpa only [HasLineDerivAt, zero_smul, add_zero] using
    hasDerivAt_heatDensityGradient_coordinate μ ht x i i 0

/-- Spatial de Bruijn identity in one coordinate, using actual heat derivatives
and the already-proved finite Fisher information. The two logarithm-weighted
L1 conditions are intermediate analytic obligations, not an upper bound. -/
theorem integral_log_mul_heatDensityHessian_eq_neg_fisher
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t) (i : I)
    (hloghess : Integrable (fun x => Real.log (heatDensity μ t x) * heatDensityHessian μ t x i i))
    (hflux : Integrable (fun x => Real.log (heatDensity μ t x) * heatDensityGradient μ t x i)) :
    (∫ x, Real.log (heatDensity μ t x) * heatDensityHessian μ t x i i) =
      -(∫ x, heatFisherCoordinate μ t i x) := by
  have heq : (fun x => (heatDensityGradient μ t x i / heatDensity μ t x) *
      heatDensityGradient μ t x i) = heatFisherCoordinate μ t i := by
    funext x
    unfold heatFisherCoordinate
    ring
  have hfisher : Integrable (fun x => (heatDensityGradient μ t x i / heatDensity μ t x) *
      heatDensityGradient μ t x i) := by
    rw [heq]
    exact integrable_heatFisherCoordinate μ ht i
  have h := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.mul ℝ ℝ) hfisher hloghess hflux
    (fun x => hasLineDerivAt_log_heatDensity_coordinate μ ht x i)
    (fun x => hasLineDerivAt_heatDensityGradient_coordinate μ ht x i)
  simpa only [ContinuousLinearMap.mul_apply', heq] using h

/-- Summed spatial identity used in entropy differentiation. -/
theorem integral_log_mul_laplacian_eq_neg_fisher
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t)
    (hloghess : ∀ i, Integrable
      (fun x => Real.log (heatDensity μ t x) * heatDensityHessian μ t x i i))
    (hflux : ∀ i, Integrable
      (fun x => Real.log (heatDensity μ t x) * heatDensityGradient μ t x i)) :
    (∫ x, Real.log (heatDensity μ t x) * ∑ i, heatDensityHessian μ t x i i) =
      -heatFisherInformation μ t := by
  simp_rw [Finset.mul_sum]
  rw [integral_finset_sum _ (fun i _ => hloghess i)]
  simp_rw [integral_log_mul_heatDensityHessian_eq_neg_fisher μ ht _ (hloghess _) (hflux _)]
  unfold heatFisherInformation
  rw [integral_finset_sum _ (fun i _ => integrable_heatFisherCoordinate μ ht i)]
  exact Finset.sum_neg_distrib

end GaussianWave.BS
