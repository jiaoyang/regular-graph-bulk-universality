import GaussianWave.BS.HeatSymmetry

/-!
# Cancelling the actual heat noise

The characteristic factor of isotropic heat noise never vanishes. Thus once
the equality argument proves the heated law Gaussian, the original law is
Gaussian as an equality of actual probability measures.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianWave.BS

theorem heatedLaw_characteristic
    {I : Type*} [Fintype I] (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (t : ℝ) (s : I → ℝ) :
    characteristicIntegral (heatedLaw μ t) s = characteristicIntegral μ s *
      Complex.exp (↑(-(1 / 2 : ℝ) * (heatVariance t : ℝ) * squareMass s) : ℂ) := by
  unfold characteristicIntegral heatedLaw Measure.conv
  change (∫ x, (linearCharacteristic s) x ∂Measure.map
    (fun z : (I → ℝ) × (I → ℝ) => z.1 + z.2) (μ.prod (heatGaussian I t))) = _
  rw [integral_map (measurable_fst.add measurable_snd).aemeasurable
    (linearCharacteristic s).continuous.measurable.aestronglyMeasurable]
  change (∫ z : (I → ℝ) × (I → ℝ),
    Complex.exp ((↑(finiteLinearForm s (z.1 + z.2)) : ℂ) * Complex.I)
      ∂μ.prod (heatGaussian I t)) = _
  have hadd (z : (I → ℝ) × (I → ℝ)) :
      finiteLinearForm s (z.1 + z.2) = finiteLinearForm s z.1 + finiteLinearForm s z.2 := by
    simp [finiteLinearForm, mul_add, Finset.sum_add_distrib]
  simp_rw [hadd, Complex.ofReal_add, add_mul, Complex.exp_add]
  rw [integral_prod_mul
    (fun x : I → ℝ => Complex.exp ((↑(finiteLinearForm s x) : ℂ) * Complex.I))
    (fun x : I → ℝ => Complex.exp ((↑(finiteLinearForm s x) : ℂ) * Complex.I))]
  rw [show (∫ x, Complex.exp ((↑(finiteLinearForm s x) : ℂ) * Complex.I) ∂heatGaussian I t) =
    characteristicIntegral (heatGaussian I t) s from rfl, heatGaussian_characteristic]

theorem heatGaussian_half_eq_standardVector (I : Type*) [Fintype I] :
    heatGaussian I (1 / 2) = standardVector I := by
  have hv : heatVariance (1 / 2) = 1 := by
    ext
    norm_num [heatVariance]
  simp only [heatGaussian, hv, standardVector, standardNormal]

/-- Actual Gaussian deconvolution for the heat flow; no moment condition on
the unknown original law is necessary. -/
theorem eq_standardVector_of_heatedLaw_eq_heatGaussian
    {I : Type*} [Fintype I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t)
    (hheated : heatedLaw μ t = heatGaussian I (t + 1 / 2)) :
    μ = standardVector I := by
  apply measure_eq_of_linear_characteristic
  intro s
  have h := congrArg (fun ν : Measure (I → ℝ) => characteristicIntegral ν s) hheated
  change characteristicIntegral (heatedLaw μ t) s = characteristicIntegral (heatGaussian I (t + 1 / 2)) s at h
  rw [heatedLaw_characteristic, heatGaussian_characteristic] at h
  have hv : (heatVariance t : ℝ) = 2 * t := by
    exact max_eq_left (by positivity)
  have hv' : (heatVariance (t + 1 / 2) : ℝ) = 2 * (t + 1 / 2) := by
    exact max_eq_left (by linarith)
  rw [hv, hv'] at h
  have hfactor : Complex.exp (↑(-(1 / 2 : ℝ) * (2 * (t + 1 / 2)) * squareMass s) : ℂ) =
      Complex.exp (↑(-(1 / 2 : ℝ) * squareMass s) : ℂ) *
        Complex.exp (↑(-(1 / 2 : ℝ) * (2 * t) * squareMass s) : ℂ) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hfactor] at h
  have hc := (mul_right_cancel₀ (Complex.exp_ne_zero _) h)
  change characteristicIntegral μ s = characteristicIntegral (standardVector I) s
  rw [show characteristicIntegral (standardVector I) s =
      Complex.exp (↑(-(1 / 2 : ℝ) * squareMass s) : ℂ) from standardVector_characteristic s]
  exact hc

end GaussianWave.BS
