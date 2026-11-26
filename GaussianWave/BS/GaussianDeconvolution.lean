import GaussianWave.BS.IndependentAddition
import GaussianWave.GaussianContinuity

/-! A fixed independent Gaussian wave can be removed by exact
characteristic-function cancellation; no vanishing-noise limit is required. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GaussianWave.BS

theorem independentAddLaw_characteristic_one {I : Type*} [Fintype I]
    (μ ν : Measure (I → ℝ)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (t : I → ℝ) :
    (∫ z,Complex.exp ((↑(finiteLinearForm t z) : ℂ)*Complex.I) ∂independentAddLaw μ ν 1) =
      (∫ x,Complex.exp ((↑(finiteLinearForm t x) : ℂ)*Complex.I) ∂μ)*
        (∫ y,Complex.exp ((↑(finiteLinearForm t y) : ℂ)*Complex.I) ∂ν) := by
  have hA : Measurable (fun p : (I → ℝ) × (I → ℝ) => p.1+(1 : ℝ) • p.2) :=
    (continuous_fst.add (continuous_const.smul continuous_snd)).measurable
  have hchar : AEStronglyMeasurable
      (fun z : I → ℝ => Complex.exp ((↑(finiteLinearForm t z) : ℂ)*Complex.I))
      (Measure.map (fun p : (I → ℝ) × (I → ℝ) => p.1+(1 : ℝ) • p.2) (μ.prod ν)) :=
    (linearCharacteristic t).continuous.aestronglyMeasurable
  rw [independentAddLaw,integral_map hA.aemeasurable hchar]
  have he (p : (I → ℝ) × (I → ℝ)) :
      Complex.exp ((↑(finiteLinearForm t (p.1+(1 : ℝ) • p.2)) : ℂ)*Complex.I) =
        Complex.exp ((↑(finiteLinearForm t p.1) : ℂ)*Complex.I)*
          Complex.exp ((↑(finiteLinearForm t p.2) : ℂ)*Complex.I) := by
    have hlin : finiteLinearForm t (p.1+(1 : ℝ) • p.2)=finiteLinearForm t p.1+finiteLinearForm t p.2 := by
      simp only [one_smul,finiteLinearForm,Pi.add_apply,mul_add,Finset.sum_add_distrib]
    rw [hlin,Complex.ofReal_add,add_mul,Complex.exp_add]
  simp_rw [he]
  exact integral_prod_mul
    (fun x : I → ℝ => Complex.exp ((↑(finiteLinearForm t x) : ℂ)*Complex.I))
    (fun y : I → ℝ => Complex.exp ((↑(finiteLinearForm t y) : ℂ)*Complex.I))

theorem hasGaussianCovariance_of_independent_gaussian_addition
    {I : Type*} [Fintype I] (μ ν : Measure (I → ℝ)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (C S : Matrix I I ℝ)
    (hν : HasGaussianCovariance ν S) (hsum : HasGaussianCovariance (independentAddLaw μ ν 1) (C+S)) :
    HasGaussianCovariance μ C := by
  intro t
  apply mul_right_cancel₀ (Complex.exp_ne_zero
    (↑(-(1/2 : ℝ)*finiteCovarianceQuadratic S t) : ℂ))
  have h := independentAddLaw_characteristic_one μ ν t
  rw [hsum t,hν t] at h
  rw [← h,← Complex.exp_add]
  congr 1
  have hq : finiteCovarianceQuadratic (C+S) t = finiteCovarianceQuadratic C t+finiteCovarianceQuadratic S t := by
    simp only [finiteCovarianceQuadratic,Matrix.add_apply,mul_add,add_mul,Finset.sum_add_distrib]
  rw [hq]
  push_cast
  ring

end GaussianWave.BS
