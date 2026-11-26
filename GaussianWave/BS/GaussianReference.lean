import GaussianWave.BS.DensityEntropy
import GaussianWave.BS.HeatFlow

/-!
# The actual Gaussian reference in the heat-flow endpoint

The logarithm is computed from Mathlib's Gaussian density. Gibbs' inequality
then proves the ordinary Gaussian maximum-entropy bound from a second moment,
rather than assuming any Gaussian extremal principle.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace GaussianWave.BS

def squareRadius {I : Type*} [Fintype I] (x : I → ℝ) : ℝ := ∑ i, (x i) ^ 2

theorem log_centeredGaussianPDF (v : ℝ≥0) (hv : 0 < v) (x : ℝ) :
    Real.log (gaussianPDFReal 0 v x) =
      -(1 / 2 : ℝ) * Real.log (2 * Real.pi * v) - x ^ 2 / (2 * v) := by
  have hp : 0 < 2 * Real.pi * (v : ℝ) := by positivity
  rw [gaussianPDFReal, sub_zero,
    Real.log_mul (inv_ne_zero (Real.sqrt_pos.mpr hp).ne') (Real.exp_ne_zero _),
    Real.log_inv, Real.log_sqrt hp.le, Real.log_exp]
  ring

theorem log_heatKernel {I : Type*} [Fintype I] {t : ℝ} (ht : 0 < t) (x : I → ℝ) :
    Real.log (heatKernel t x) =
      -((Fintype.card I : ℝ) / 2) * Real.log (2 * Real.pi * (heatVariance t : ℝ)) -
        squareRadius x / (2 * (heatVariance t : ℝ)) := by
  rw [heatKernel, Real.log_prod _ _ (fun i _ => (gaussianPDFReal_pos 0 _ _
    (heatVariance_pos ht).ne').ne')]
  simp_rw [log_centeredGaussianPDF _ (heatVariance_pos ht)]
  simp [squareRadius, Finset.sum_sub_distrib, Finset.sum_div]
  ring

/-- The usual entropy of a centered isotropic Gaussian, in nats. -/
def gaussianEntropyValue (I : Type*) [Fintype I] (v : ℝ≥0) : ℝ :=
  (Fintype.card I : ℝ) / 2 * (1 + Real.log (2 * Real.pi * v))

theorem integrable_cross_heatKernel {I : Type*} [Fintype I]
    (f : (I → ℝ) → ℝ) {t : ℝ} (ht : 0 < t)
    (hfi : Integrable f)
    (hfq : Integrable (fun x => f x * squareRadius x)) :
    Integrable (fun x => f x * Real.log (heatKernel t x)) := by
  have heq : (fun x => f x * Real.log (heatKernel t x)) =
      (fun x => (-((Fintype.card I : ℝ) / 2) *
        Real.log (2 * Real.pi * (heatVariance t : ℝ))) * f x -
        (f x * squareRadius x) / (2 * (heatVariance t : ℝ))) := by
    funext x
    rw [log_heatKernel ht]
    ring
  rw [heq]
  exact (hfi.const_mul _).sub (hfq.div_const _)

theorem crossEntropy_heatKernel {I : Type*} [Fintype I]
    (f : (I → ℝ) → ℝ) {t : ℝ} (ht : 0 < t)
    (hfi : Integrable f)
    (hfq : Integrable (fun x => f x * squareRadius x))
    (hf : (∫ x, f x) = 1) :
    -(∫ x, f x * Real.log (heatKernel t x)) =
      (Fintype.card I : ℝ) / 2 * Real.log (2 * Real.pi * (heatVariance t : ℝ)) +
        (∫ x, f x * squareRadius x) / (2 * (heatVariance t : ℝ)) := by
  have heq : (fun x => f x * Real.log (heatKernel t x)) =
      (fun x => (-((Fintype.card I : ℝ) / 2) *
        Real.log (2 * Real.pi * (heatVariance t : ℝ))) * f x -
        (f x * squareRadius x) / (2 * (heatVariance t : ℝ))) := by
    funext x
    rw [log_heatKernel ht]
    ring
  rw [heq, integral_sub (f := fun x => (-((Fintype.card I : ℝ) / 2) *
    Real.log (2 * Real.pi * (heatVariance t : ℝ))) * f x)
    (hfi.const_mul _) (hfq.div_const _), integral_const_mul, integral_div, hf]
  ring

/-- Ordinary Gaussian maximal entropy, proved for an actual normalized density
with the Gaussian radial second moment. No BS upper bound is a premise. -/
theorem densityEntropy_le_gaussianEntropyValue {I : Type*} [Fintype I]
    (f : (I → ℝ) → ℝ) {t : ℝ} (ht : 0 < t)
    (hf0 : ∀ x, 0 ≤ f x) (hfi : Integrable f)
    (hf : (∫ x, f x) = 1)
    (hflog : Integrable (fun x => f x * Real.log (f x)))
    (hfq : Integrable (fun x => f x * squareRadius x))
    (hmoment : (∫ x, f x * squareRadius x) =
      (Fintype.card I : ℝ) * (heatVariance t : ℝ)) :
    densityEntropy volume f ≤ gaussianEntropyValue I (heatVariance t) := by
  have h := densityEntropy_le_crossEntropy volume f (heatKernel t) hf0
    (heatKernel_pos ht) hfi (integrable_heatKernel t) hf (integral_heatKernel ht)
    hflog (integrable_cross_heatKernel f ht hfi hfq)
  rw [crossEntropy_heatKernel f ht hfi hfq hf, hmoment] at h
  have hv : (heatVariance t : ℝ) ≠ 0 := by exact_mod_cast (heatVariance_pos ht).ne'
  have heq : (Fintype.card I : ℝ) / 2 *
      Real.log (2 * Real.pi * (heatVariance t : ℝ)) +
      (Fintype.card I : ℝ) * (heatVariance t : ℝ) / (2 * (heatVariance t : ℝ)) =
      gaussianEntropyValue I (heatVariance t) := by
    unfold gaussianEntropyValue
    field_simp
    ring
  rwa [heq] at h

theorem integrable_heatGaussian_coordinate_sq {I : Type*} [Fintype I]
    (t : ℝ) (i : I) : Integrable (fun x : I → ℝ => (x i) ^ 2) (heatGaussian I t) := by
  classical
  let ms : I → MeasureSpace ℝ := fun _ => ⟨gaussianReal 0 (heatVariance t)⟩
  have sf : ∀ i, @SigmaFinite ℝ _ (@volume ℝ (ms i)) := fun _ =>
    (inferInstance : SigmaFinite (gaussianReal 0 (heatVariance t)))
  let f : I → ℝ → ℝ := fun j y => if j = i then y ^ 2 else 1
  have hi : ∀ j, Integrable (f j) (@volume ℝ (ms j)) := by
    intro j
    by_cases hj : j = i
    · simpa [f, hj] using centeredGaussian_integrable_pow (heatVariance t) 2
    · simpa only [f, if_neg hj] using
        (integrable_const (μ := gaussianReal 0 (heatVariance t)) (1 : ℝ))
  have hp := @Integrable.fintype_prod_dep ℝ _ I _ (fun _ => ℝ) f ms
    sf hi
  simpa [f, ms, heatGaussian, volume_pi] using hp

theorem integral_heatGaussian_coordinate_sq {I : Type*} [Fintype I]
    (t : ℝ) (i : I) :
    (∫ x : I → ℝ, (x i) ^ 2 ∂heatGaussian I t) = (heatVariance t : ℝ) := by
  classical
  let ms : I → MeasureSpace ℝ := fun _ => ⟨gaussianReal 0 (heatVariance t)⟩
  have sf : ∀ i, @SigmaFinite ℝ _ (@volume ℝ (ms i)) := fun _ =>
    (inferInstance : SigmaFinite (gaussianReal 0 (heatVariance t)))
  let f : I → ℝ → ℝ := fun j y => if j = i then y ^ 2 else 1
  have hp := @integral_fintype_prod_eq_prod ℝ _ I _ (fun _ => ℝ) f ms
    sf
  have hf (j : I) : (∫ y, f j y ∂gaussianReal 0 (heatVariance t)) =
      if j = i then (heatVariance t : ℝ) else 1 := by
    by_cases hj : j = i <;> simp [f, hj, centeredGaussian_second_moment]
  calc
    _ = ∫ x : I → ℝ, ∏ j, f j (x j) ∂heatGaussian I t := by simp [f]
    _ = ∏ j, ∫ y, f j y ∂gaussianReal 0 (heatVariance t) := by
      simpa only [heatGaussian, ← volume_pi] using hp
    _ = _ := by simp_rw [hf]; simp

theorem integrable_heatKernel_mul_coordinate_sq {I : Type*} [Fintype I]
    {t : ℝ} (ht : 0 < t) (i : I) :
    Integrable (fun x : I → ℝ => heatKernel t x * (x i) ^ 2) := by
  have hi := integrable_heatGaussian_coordinate_sq (I := I) t i
  rw [heatGaussian_eq_withDensity ht] at hi
  have hp := (integrable_withDensity_iff_integrable_smul'
    (measurable_heatKernel t).ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mp hi
  simpa only [ENNReal.toReal_ofReal (heatKernel_nonneg _ _), smul_eq_mul] using hp

theorem integral_heatKernel_mul_coordinate_sq {I : Type*} [Fintype I]
    {t : ℝ} (ht : 0 < t) (i : I) :
    (∫ x : I → ℝ, heatKernel t x * (x i) ^ 2) = (heatVariance t : ℝ) := by
  have heq := integral_withDensity_eq_integral_toReal_smul
    (μ := (volume : Measure (I → ℝ))) (measurable_heatKernel t).ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)) (fun x => (x i) ^ 2)
  simp only [ENNReal.toReal_ofReal (heatKernel_nonneg _ _), smul_eq_mul] at heq
  rw [← heq, ← heatGaussian_eq_withDensity ht, integral_heatGaussian_coordinate_sq]

theorem integrable_heatGaussian_squareRadius {I : Type*} [Fintype I] (t : ℝ) :
    Integrable (squareRadius (I := I)) (heatGaussian I t) :=
  integrable_finset_sum _ (fun i _ => integrable_heatGaussian_coordinate_sq t i)

theorem integral_heatGaussian_squareRadius {I : Type*} [Fintype I] (t : ℝ) :
    (∫ x : I → ℝ, squareRadius x ∂heatGaussian I t) =
      (Fintype.card I : ℝ) * (heatVariance t : ℝ) := by
  unfold squareRadius
  rw [integral_finset_sum _ (fun i _ => integrable_heatGaussian_coordinate_sq t i)]
  simp [integral_heatGaussian_coordinate_sq]

theorem integrable_heatKernel_mul_squareRadius {I : Type*} [Fintype I]
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : I → ℝ => heatKernel t x * squareRadius x) := by
  have hi := integrable_heatGaussian_squareRadius (I := I) t
  rw [heatGaussian_eq_withDensity ht] at hi
  have hp := (integrable_withDensity_iff_integrable_smul'
    (measurable_heatKernel t).ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mp hi
  simpa only [ENNReal.toReal_ofReal (heatKernel_nonneg _ _), smul_eq_mul] using hp

theorem integral_heatKernel_mul_squareRadius {I : Type*} [Fintype I]
    {t : ℝ} (ht : 0 < t) :
    (∫ x : I → ℝ, heatKernel t x * squareRadius x) =
      (Fintype.card I : ℝ) * (heatVariance t : ℝ) := by
  have heq := integral_withDensity_eq_integral_toReal_smul
    (μ := (volume : Measure (I → ℝ))) (measurable_heatKernel t).ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)) squareRadius
  simp only [ENNReal.toReal_ofReal (heatKernel_nonneg _ _), smul_eq_mul] at heq
  rw [← heq, ← heatGaussian_eq_withDensity ht, integral_heatGaussian_squareRadius]

theorem integrable_heatKernel_log {I : Type*} [Fintype I] {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : I → ℝ => heatKernel t x * Real.log (heatKernel t x)) :=
  integrable_cross_heatKernel _ ht (integrable_heatKernel t)
    (integrable_heatKernel_mul_squareRadius ht)

/-- Entropy of the actual finite product Gaussian density. -/
theorem densityEntropy_heatKernel {I : Type*} [Fintype I] {t : ℝ} (ht : 0 < t) :
    densityEntropy volume (heatKernel (I := I) t) = gaussianEntropyValue I (heatVariance t) := by
  unfold densityEntropy
  rw [crossEntropy_heatKernel _ ht (integrable_heatKernel t)
    (integrable_heatKernel_mul_squareRadius ht) (integral_heatKernel ht),
    integral_heatKernel_mul_squareRadius ht]
  have hv : (heatVariance t : ℝ) ≠ 0 := by exact_mod_cast (heatVariance_pos ht).ne'
  unfold gaussianEntropyValue
  field_simp
  ring

end GaussianWave.BS
