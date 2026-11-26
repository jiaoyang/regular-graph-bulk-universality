import GeneralizedBulk.Entropy.HermiteOU
import GeneralizedBulk.Entropy.MehlerDensity

/-! Exact actual Hermite coefficients of the finite-signal Mehler density. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Mehler
open GeneralizedBulk.Entropy.Hermite
variable {I : Type*} [Fintype I]

/-- Polynomial moments under the actual Mehler density are integrable because
it is the actual affine Gaussian law. -/
theorem integrable_vectorKernel_mul_multiHermite (a : ℝ) (ha : 0 < 1 - a ^ 2)
    (y : I → ℝ) (α : I → ℕ) :
    Integrable (fun z => vectorKernel a y z * multiHermite I α z) (standardGaussian I) := by
  let T := fun z : I → ℝ => fun i => a * y i + Real.sqrt (1 - a ^ 2) * z i
  have hTm : Measurable T := by dsimp [T]; fun_prop
  have hmap : (standardGaussian I).map T =
      (standardGaussian I).withDensity (fun z => ENNReal.ofReal (vectorKernel a y z)) :=
    (smoothedGaussianLaw_eq_affine_map a ha y).trans (smoothedGaussianLaw_eq_withDensity a ha y)
  have hpres : MeasurePreserving T (standardGaussian I)
      ((standardGaussian I).withDensity (fun z => ENNReal.ofReal (vectorKernel a y z))) := ⟨hTm, hmap⟩
  have hi : Integrable (multiHermite I α)
      ((standardGaussian I).withDensity (fun z => ENNReal.ofReal (vectorKernel a y z))) :=
    (hpres.integrable_comp (continuous_multiHermite I α).aestronglyMeasurable).mp
      (integrable_multiHermite_affine a (Real.sqrt (1 - a ^ 2)) α y)
  have hh := (integrable_withDensity_iff_integrable_smul₀'
    (continuous_vectorKernel a y).aemeasurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun z => ENNReal.ofReal_lt_top))).mp hi
  have hk (z : I → ℝ) : 0 ≤ vectorKernel a y z := (kernel_pos _ _ _ _).le
  simpa only [ENNReal.toReal_ofReal (hk _), smul_eq_mul] using hh

/-- The exact OU power law for actual Gaussian density pairings. -/
theorem integral_vectorKernel_mul_multiHermite (a : ℝ) (ha : 0 < 1 - a ^ 2)
    (y : I → ℝ) (α : I → ℕ) :
    (∫ z, vectorKernel a y z * multiHermite I α z ∂standardGaussian I) =
      a ^ (∑ i, α i) * multiHermite I α y := by
  have hmap := (smoothedGaussianLaw_eq_affine_map a ha y).trans (smoothedGaussianLaw_eq_withDensity a ha y)
  have hi := integral_withDensity_eq_integral_toReal_smul₀ (μ := standardGaussian I)
    (continuous_vectorKernel a y).aemeasurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun z => ENNReal.ofReal_lt_top)) (multiHermite I α)
  have hk (z : I → ℝ) : 0 ≤ vectorKernel a y z := (kernel_pos _ _ _ _).le
  simp only [ENNReal.toReal_ofReal (hk _), smul_eq_mul] at hi
  have hTm : Measurable (fun z : I → ℝ => fun i => a * y i + Real.sqrt (1 - a ^ 2) * z i) := by fun_prop
  rw [← hi, ← hmap, integral_map hTm.aemeasurable (continuous_multiHermite I α).aestronglyMeasurable]
  apply integral_multiHermite_affine
  rw [Real.sq_sqrt ha.le]
  ring

variable {S : Type*} [Fintype S]

def signalHermiteMoment (weight : S → ℝ) (signal : S → I → ℝ) (α : I → ℕ) : ℝ :=
  ∑ s, weight s * multiHermite I α (signal s)

theorem integrable_finiteMixture_mul_multiHermite (weight : S → ℝ) (signal : S → I → ℝ)
    (a : ℝ) (ha : 0 < 1 - a ^ 2) (α : I → ℕ) :
    Integrable (fun z => finiteMixtureKernel weight signal a z * multiHermite I α z) (standardGaussian I) := by
  have hh := integrable_finset_sum Finset.univ (fun s _ =>
    (integrable_vectorKernel_mul_multiHermite a ha (signal s) α).const_mul (weight s))
  convert hh using 1
  funext z
  simp only [finiteMixtureKernel, Finset.sum_mul, mul_assoc]

theorem integral_finiteMixture_mul_multiHermite (weight : S → ℝ) (signal : S → I → ℝ)
    (a : ℝ) (ha : 0 < 1 - a ^ 2) (α : I → ℕ) :
    (∫ z, finiteMixtureKernel weight signal a z * multiHermite I α z ∂standardGaussian I) =
      a ^ (∑ i, α i) * signalHermiteMoment weight signal α := by
  change (∫ z, (∑ s, weight s * vectorKernel a (signal s) z) * multiHermite I α z ∂standardGaussian I) = _
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [integral_finset_sum _ (fun s _ => (integrable_vectorKernel_mul_multiHermite a ha (signal s) α).const_mul (weight s))]
  simp_rw [integral_const_mul, integral_vectorKernel_mul_multiHermite a ha]
  rw [signalHermiteMoment, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  ring

end GeneralizedBulk.Entropy.Mehler
