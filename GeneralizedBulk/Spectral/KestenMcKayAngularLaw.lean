import GeneralizedBulk.Spectral.KestenMcKayFourier
import Mathlib.MeasureTheory.Measure.WithDensityFinite

/-! The genuine angular Kesten–McKay probability law and exact Fourier
moments against that law. -/
noncomputable section
open scoped ComplexConjugate
open MeasureTheory Set
namespace GeneralizedBulk.KestenMcKay
open GeneralizedBulk.Spectral

def angularLaw (d : ℝ) : Measure ℝ :=
  (volume.restrict (Icc (-(Real.pi / 2)) (Real.pi / 2))).withDensity
    (fun theta => ENNReal.ofReal (angularDensity d theta))

theorem angularDensity_nonneg (d : ℝ) (hd : 3 ≤ d) (theta : ℝ) : 0 ≤ angularDensity d theta := by
  unfold angularDensity
  have hD : 0 ≤ d := by linarith
  have hQ : 0 ≤ d - 1 := by linarith
  exact div_nonneg (by positivity) (mul_pos Real.pi_pos (angularDenominator_pos d hd theta)).le

theorem angularLaw_isProbability (d : ℝ) (hd : 3 ≤ d) : IsProbabilityMeasure (angularLaw d) := by
  constructor
  rw [angularLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal (continuous_angularDensity d hd).integrableOn_Icc
    (Filter.Eventually.of_forall (angularDensity_nonneg d hd))]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_angularDensity d hd]
  norm_num

theorem integral_angularLaw_complex (d : ℝ) (hd : 3 ≤ d) (f : ℝ → ℂ) :
    (∫ theta, f theta ∂angularLaw d) =
      ∫ theta in -(Real.pi / 2)..Real.pi / 2, (angularDensity d theta : ℂ) * f theta := by
  rw [angularLaw, integral_withDensity_eq_integral_toReal_smul
    (continuous_angularDensity d hd).measurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (angularDensity_nonneg d hd _), Complex.real_smul]
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), ← integral_Icc_eq_integral_Ioc]

theorem angularLaw_mode (d : ℝ) (hd : 3 ≤ d) (k : ℕ) :
    (∫ theta, angularMode k theta ∂angularLaw d) =
      if k = 0 then 1 else -((d - 2 : ℝ) : ℂ) / 2 * ((-1 / (d - 1) : ℝ) : ℂ) ^ k := by
  rw [integral_angularLaw_complex d hd]
  exact integral_angularDensity_mode d hd k

theorem angularLaw_mode_neg (d : ℝ) (hd : 3 ≤ d) (k : ℕ) :
    (∫ theta, angularMode (-(k : ℤ)) theta ∂angularLaw d) =
      if k = 0 then 1 else -((d - 2 : ℝ) : ℂ) / 2 * ((-1 / (d - 1) : ℝ) : ℂ) ^ k := by
  simp_rw [← angularMode_conj]
  rw [integral_conj, angularLaw_mode d hd]
  by_cases hk : k = 0 <;> simp [hk, map_ofNat]

end GeneralizedBulk.KestenMcKay
