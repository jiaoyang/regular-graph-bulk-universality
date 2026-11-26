import GeneralizedBulk.Entropy.MehlerDensity
import GeneralizedBulk.Entropy.GaussianCondExp

/-! Genuine Gaussian conditional marginals of the Mehler smoothing density. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace GeneralizedBulk.Entropy.Mehler
open GeneralizedBulk.Gaussian GeneralizedBulk.Analysis GeneralizedBulk.Entropy.Hermite
variable {I : Type*} [Fintype I] [DecidableEq I]

def kernelFactor (observed : Finset I) (a : ℝ) (y x : I → ℝ) : ℝ :=
  vectorKernel a (fun i : observed => y i) (retainedCoordinates observed x)

theorem kernelFactor_measurable_observed (observed : Finset I) (a : ℝ) (y : I → ℝ) :
    StronglyMeasurable[coordinateSigma observed] (kernelFactor observed a y) := by
  have hr : Measurable[coordinateSigma observed] (retainedCoordinates observed) :=
    Measurable.of_comap_le le_rfl
  exact ((continuous_vectorKernel a (fun i : observed => y i)).measurable.comp hr).stronglyMeasurable

theorem kernelFactor_integrable (observed : Finset I) (a : ℝ) (ha : 0 < 1 - a ^ 2) (y : I → ℝ) :
    Integrable (kernelFactor observed a y) (standardGaussian I) :=
  ((retainedCoordinates_measurePreserving observed).integrable_comp
    (continuous_vectorKernel a (fun i : observed => y i)).aestronglyMeasurable).2
      (integrable_vectorKernel a ha _)

theorem kernelFactor_integral (observed : Finset I) (a : ℝ) (ha : 0 < 1 - a ^ 2) (y : I → ℝ) :
    (∫ x, kernelFactor observed a y x ∂standardGaussian I) = 1 := by
  have hmp := retainedCoordinates_measurePreserving observed
  have hm : AEStronglyMeasurable (vectorKernel a (fun i : observed => y i))
      (Measure.map (retainedCoordinates observed) (standardGaussian I)) := by
    rw [hmp.map_eq]
    exact (continuous_vectorKernel a _).aestronglyMeasurable
  have h := integral_map (measurable_retainedCoordinates observed).aemeasurable hm
  rw [hmp.map_eq] at h
  exact h.symm.trans (integral_vectorKernel a ha _)

theorem vectorKernel_split (observed : Finset I) (a : ℝ) (ha : 0 < 1 - a ^ 2) (y x : I → ℝ) :
    vectorKernel a y x = kernelFactor observed a y x * kernelFactor observedᶜ a y x := by
  unfold kernelFactor
  rw [vectorKernel_factorization a ha, vectorKernel_factorization a ha,
    vectorKernel_factorization a ha]
  change (∏ i : I, gaussianRelative (a * y i) ⟨1 - a ^ 2, ha.le⟩ (x i)) =
    (∏ i : observed, gaussianRelative (a * y i.val) ⟨1 - a ^ 2, ha.le⟩ (x i.val)) *
      ∏ i : (observedᶜ : Finset I), gaussianRelative (a * y i.val) ⟨1 - a ^ 2, ha.le⟩ (x i.val)
  have ho := Finset.prod_coe_sort observed (fun i : I => gaussianRelative (a * y i) ⟨1 - a ^ 2, ha.le⟩ (x i))
  have hc := Finset.prod_coe_sort observedᶜ (fun i : I => gaussianRelative (a * y i) ⟨1 - a ^ 2, ha.le⟩ (x i))
  rw [ho, hc]
  exact (Finset.prod_mul_prod_compl observed _).symm

/-- Coordinate Gaussian conditioning gives the actual lower-dimensional
Gaussian smoothing density of the retained signal. -/
theorem condExp_vectorKernel (observed : Finset I) (a : ℝ) (ha : 0 < 1 - a ^ 2) (y : I → ℝ) :
    (standardGaussian I)[vectorKernel a y | coordinateSigma observed] =ᵐ[standardGaussian I]
      kernelFactor observed a y := by
  have hg := condExp_indep_eq (coordinateSigma_le observedᶜ) (coordinateSigma_le observed)
    (kernelFactor_measurable_observed observedᶜ a y) (coordinateSigma_indep observed)
  have hf : Integrable (kernelFactor observed a y * kernelFactor observedᶜ a y) (standardGaussian I) := by
    convert integrable_vectorKernel a ha y using 1
    funext x
    exact (vectorKernel_split observed a ha y x).symm
  have hp := condExp_mul_of_stronglyMeasurable_left (kernelFactor_measurable_observed observed a y)
    hf (kernelFactor_integrable observedᶜ a ha y)
  have heq : kernelFactor observed a y * kernelFactor observedᶜ a y = vectorKernel a y := by
    funext x
    exact (vectorKernel_split observed a ha y x).symm
  rw [heq] at hp
  filter_upwards [hp, hg] with x hx hy
  rw [hx]
  simp only [Pi.mul_apply, hy, kernelFactor_integral observedᶜ a ha y, mul_one]

variable {S : Type*} [Fintype S]

/-- This is conditioning of the actual finite-mixture density, not a
separately assumed marginal-density formula. -/
theorem condExp_finiteMixtureKernel (observed : Finset I) (weight : S → ℝ)
    (signal : S → I → ℝ) (a : ℝ) (ha : 0 < 1 - a ^ 2) :
    (standardGaussian I)[finiteMixtureKernel weight signal a | coordinateSigma observed] =ᵐ[standardGaussian I]
      (fun x => finiteMixtureKernel weight (fun s => fun i : observed => signal s i) a (retainedCoordinates observed x)) := by
  have hs := condExp_finset_sum (μ := standardGaussian I)
    (fun s (_ : s ∈ (Finset.univ : Finset S)) => (integrable_vectorKernel a ha (signal s)).const_mul (weight s))
    (coordinateSigma observed)
  have hfun : (∑ s : S, (fun x : I → ℝ => weight s * vectorKernel a (signal s) x)) =
      finiteMixtureKernel weight signal a := by
    funext x
    simp only [finiteMixtureKernel, Finset.sum_apply]
  rw [hfun] at hs
  have hterm (s : S) :
      (standardGaussian I)[(fun x => weight s * vectorKernel a (signal s) x) | coordinateSigma observed] =ᵐ[standardGaussian I]
        (fun x => weight s * kernelFactor observed a (signal s) x) := by
    have hm := condExp_smul (μ := standardGaussian I) (weight s) (vectorKernel a (signal s)) (coordinateSigma observed)
    filter_upwards [hm, condExp_vectorKernel observed a ha (signal s)] with x hx hy
    simpa only [Pi.smul_apply, smul_eq_mul, hy] using hx
  have hall := ae_all_iff.mpr hterm
  filter_upwards [hs, hall] with x hx hy
  rw [hx]
  simp only [Finset.sum_apply, finiteMixtureKernel, kernelFactor]
  exact Finset.sum_congr rfl (fun s _ => hy s)

end GeneralizedBulk.Entropy.Mehler
