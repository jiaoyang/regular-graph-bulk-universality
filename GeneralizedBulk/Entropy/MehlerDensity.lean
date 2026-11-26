import GeneralizedBulk.Entropy.GaussianRelativeDensity
import GeneralizedBulk.Entropy.MehlerFiniteSignals
import GeneralizedBulk.Analysis.DensityMixture
import GeneralizedBulk.Analysis.PiMap

/-! The multivariate Mehler kernel is the density of the actual smoothed law. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace GeneralizedBulk.Entropy.Mehler
open GeneralizedBulk.Gaussian GeneralizedBulk.Analysis GeneralizedBulk.Entropy.Hermite
variable {I : Type*} [Fintype I]

theorem logKernel_sum (a : ℝ) (y z : I → ℝ) :
    (∑ i, logKernel 1 (z i * y i) (y i ^ 2 + z i ^ 2) a) =
      logKernel (Fintype.card I) (∑ i, z i * y i) (∑ i, (y i ^ 2 + z i ^ 2)) a := by
  have he (c e : ℝ) : logKernel 1 c e a =
      -(1 / 2 : ℝ) * Real.log (1 - a ^ 2) +
        (2 * a / (2 * (1 - a ^ 2))) * c - (a ^ 2 / (2 * (1 - a ^ 2))) * e := by
    unfold logKernel
    ring
  simp_rw [he]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold logKernel
  ring

theorem vectorKernel_factorization (a : ℝ) (ha : 0 < 1 - a ^ 2) (y z : I → ℝ) :
    vectorKernel a y z = ∏ i, gaussianRelative (a * y i) ⟨1 - a ^ 2, ha.le⟩ (z i) := by
  unfold vectorKernel kernel
  rw [← logKernel_sum, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i hi
  exact (gaussianRelative_smoothing a (y i) (z i) ha).symm

theorem continuous_vectorKernel (a : ℝ) (y : I → ℝ) : Continuous (vectorKernel a y) := by
  unfold vectorKernel kernel logKernel
  fun_prop

theorem integrable_vectorKernel (a : ℝ) (ha : 0 < 1 - a ^ 2) (y : I → ℝ) :
    Integrable (vectorKernel a y) (standardGaussian I) := by
  have hv : (⟨1 - a ^ 2, ha.le⟩ : ℝ≥0) ≠ 0 := by
    intro h
    exact (ne_of_gt ha) (congrArg (fun r : ℝ≥0 => (r : ℝ)) h)
  have h := integrable_pi_product (fun _ : I => standardNormal)
    (fun i => gaussianRelative (a * y i) ⟨1 - a ^ 2, ha.le⟩)
    (fun i => integrable_gaussianRelative _ _ hv)
  exact h.congr (ae_of_all _ (fun z => (vectorKernel_factorization a ha y z).symm))

theorem integral_vectorKernel (a : ℝ) (ha : 0 < 1 - a ^ 2) (y : I → ℝ) :
    (∫ z, vectorKernel a y z ∂standardGaussian I) = 1 := by
  have hv : (⟨1 - a ^ 2, ha.le⟩ : ℝ≥0) ≠ 0 := by
    intro h
    exact (ne_of_gt ha) (congrArg (fun r : ℝ≥0 => (r : ℝ)) h)
  simp_rw [vectorKernel_factorization a ha y]
  rw [standardGaussian, integral_pi_product]
  simp only [integral_gaussianRelative _ _ hv, Finset.prod_const_one]

theorem smoothedGaussianLaw_eq_withDensity (a : ℝ) (ha : 0 < 1 - a ^ 2) (y : I → ℝ) :
    Measure.pi (fun i => gaussianReal (a * y i) ⟨1 - a ^ 2, ha.le⟩) =
      (standardGaussian I).withDensity (fun z => ENNReal.ofReal (vectorKernel a y z)) := by
  have hv : (⟨1 - a ^ 2, ha.le⟩ : ℝ≥0) ≠ 0 := by
    intro h
    exact (ne_of_gt ha) (congrArg (fun r : ℝ≥0 => (r : ℝ)) h)
  have he (i : I) := gaussianReal_eq_standardNormal_withDensity (a * y i) _ hv
  simp_rw [he]
  rw [pi_withDensity_ofReal (fun _ : I => standardNormal)
    (fun i => gaussianRelative (a * y i) ⟨1 - a ^ 2, ha.le⟩)
    (fun i => integrable_gaussianRelative _ _ hv) (fun i => gaussianRelative_nonneg _ _)]
  congr 1
  funext z
  exact congrArg ENNReal.ofReal (vectorKernel_factorization a ha y z).symm

theorem smoothedGaussianLaw_eq_affine_map (a : ℝ) (ha : 0 < 1 - a ^ 2) (y : I → ℝ) :
    (standardGaussian I).map (fun z i => a * y i + Real.sqrt (1 - a ^ 2) * z i) =
      Measure.pi (fun i => gaussianReal (a * y i) ⟨1 - a ^ 2, ha.le⟩) := by
  rw [standardGaussian, map_pi_coordinatewise (fun _ : I => standardNormal)
    (fun i t => a * y i + Real.sqrt (1 - a ^ 2) * t) (fun i => by fun_prop)]
  congr 1
  funext i
  have he := gaussianReal_map_const_mul (μ := 0) (v := 1) (Real.sqrt (1 - a ^ 2))
  have hv : (⟨(Real.sqrt (1 - a ^ 2)) ^ 2, sq_nonneg _⟩ : ℝ≥0) * 1 =
      ⟨1 - a ^ 2, ha.le⟩ := by
    ext
    simp only [NNReal.coe_mul, NNReal.coe_one, mul_one, Real.sq_sqrt ha.le]
  simp only [mul_zero, hv] at he
  have h := gaussianReal_map_const_add (μ := 0) (v := (⟨1 - a ^ 2, ha.le⟩ : ℝ≥0)) (a * y i)
  rw [← he] at h
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at h
  simpa only [standardNormal, Function.comp_def, zero_add] using h

variable {S : Type*} [Fintype S]

theorem integrable_finiteMixtureKernel (weight : S → ℝ) (signal : S → I → ℝ)
    (a : ℝ) (ha : 0 < 1 - a ^ 2) :
    Integrable (finiteMixtureKernel weight signal a) (standardGaussian I) := by
  exact integrable_finset_sum _ (fun s _ => (integrable_vectorKernel a ha (signal s)).const_mul (weight s))

theorem integral_finiteMixtureKernel (weight : S → ℝ) (signal : S → I → ℝ)
    (hnorm : ∑ s, weight s = 1) (a : ℝ) (ha : 0 < 1 - a ^ 2) :
    (∫ z, finiteMixtureKernel weight signal a z ∂standardGaussian I) = 1 := by
  change (∫ z, ∑ s, weight s * vectorKernel a (signal s) z ∂standardGaussian I) = 1
  rw [integral_finset_sum _
    (fun s _ => (integrable_vectorKernel a ha (signal s)).const_mul (weight s))]
  simp_rw [integral_const_mul, integral_vectorKernel a ha, mul_one]
  exact hnorm

/-- The literal smoothing density of a finite signal is the density of the
corresponding mixture of Gaussian probability laws. -/
theorem finiteMixtureLaw_eq_withDensity (weight : S → ℝ) (signal : S → I → ℝ)
    (hweight : ∀ s, 0 ≤ weight s) (a : ℝ) (ha : 0 < 1 - a ^ 2) :
    (∑ s, ENNReal.ofReal (weight s) •
      Measure.pi (fun i => gaussianReal (a * signal s i) ⟨1 - a ^ 2, ha.le⟩)) =
      (standardGaussian I).withDensity
        (fun z => ENNReal.ofReal (finiteMixtureKernel weight signal a z)) := by
  rw [show (fun z => ENNReal.ofReal (finiteMixtureKernel weight signal a z)) =
    (fun z => ENNReal.ofReal (∑ s, weight s * vectorKernel a (signal s) z)) from rfl,
    withDensity_finite_mixture (standardGaussian I) weight _ hweight
      (fun s => (continuous_vectorKernel a (signal s)).measurable)
      (fun s z => (kernel_pos _ _ _ _).le)]
  apply Finset.sum_congr rfl
  intro s hs
  rw [smoothedGaussianLaw_eq_withDensity a ha]

end GeneralizedBulk.Entropy.Mehler
