import GeneralizedBulk.Spectral.KestenMcKayPushforward

/-! Stability in the energy parameter for the actual regularized
Kesten–McKay potential. -/
noncomputable section
open Set MeasureTheory
namespace GeneralizedBulk.KestenMcKay
open GeneralizedBulk.Spectral

theorem regularizedLog_symm (E eta t : ℝ) : regularizedLog E eta t = regularizedLog t eta E := by
  unfold regularizedLog
  congr 2
  ring

theorem regularizedPotential_energy_lipschitz (d : ℝ) (hd : 3 ≤ d)
    (E F eta : ℝ) (heta : 0 < eta) :
    |regularizedPotential d E eta - regularizedPotential d F eta| ≤ eta⁻¹ * |E - F| := by
  have hab : -radius d ≤ radius d := by linarith [radius_pos d hd]
  have hcont (A : ℝ) : Continuous (regularizedLog A eta) := continuous_iff_continuousAt.mpr
    (fun x => (regularizedLog_hasDerivAt A eta heta x).continuousAt)
  have hi (A : ℝ) : IntervalIntegrable (fun x => regularizedLog A eta x * rawDensity d x) volume (-radius d) (radius d) :=
    ((hcont A).continuousOn.mul (continuousOn_rawDensity d hd)).intervalIntegrable_of_Icc hab
  have hpoint (x : ℝ) : |regularizedLog E eta x - regularizedLog F eta x| ≤ eta⁻¹ * |E - F| := by
    rw [regularizedLog_symm E eta x, regularizedLog_symm F eta x]
    exact regularizedLog_lipschitz x eta heta E F
  have hdom : ∀ᵐ x ∂volume.restrict (uIoc (-radius d) (radius d)),
      ‖(regularizedLog E eta x - regularizedLog F eta x) * rawDensity d x‖ ≤
        (eta⁻¹ * |E - F|) * rawDensity d x := by
    apply (ae_restrict_iff' measurableSet_uIoc).mpr
    apply ae_of_all
    intro x hx
    rw [uIoc_of_le hab] at hx
    have hx' : x ∈ Icc (-radius d) (radius d) := ⟨hx.1.le, hx.2⟩
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (rawDensity_nonneg d hd hx')]
    exact mul_le_mul_of_nonneg_right (hpoint x) (rawDensity_nonneg d hd hx')
  have hr : IntervalIntegrable (rawDensity d) volume (-radius d) (radius d) :=
    (continuousOn_rawDensity d hd).intervalIntegrable_of_Icc hab
  have hh := intervalIntegral.norm_integral_le_of_norm_le hdom (hr.const_mul (eta⁻¹ * |E - F|))
  rw [intervalIntegral.integral_const_mul, integral_rawDensity d hd, mul_one,
    abs_of_nonneg (by positivity : 0 ≤ eta⁻¹ * |E - F|), Real.norm_eq_abs] at hh
  unfold regularizedPotential
  rw [← intervalIntegral.integral_sub (hi E) (hi F)]
  simpa only [sub_mul] using hh

end GeneralizedBulk.KestenMcKay
