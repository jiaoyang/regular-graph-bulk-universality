import GeneralizedBulk.Spectral.KestenMcKayAngularLaw

/-! Paired powers arising from the two logarithmic factors of the tree
spectral parametrization. -/
noncomputable section
open scoped ComplexConjugate
open MeasureTheory
namespace GeneralizedBulk.KestenMcKay
open GeneralizedBulk.Spectral

def pairedPower (u : ℂ) (n : ℕ) (theta : ℝ) : ℂ :=
  (u * circlePoint 1 theta) ^ n + (-u * circlePoint 1 (-theta)) ^ n

theorem angularDensity_neg (d theta : ℝ) : angularDensity d (-theta) = angularDensity d theta := by
  simp only [angularDensity, Real.cos_neg, Real.sin_neg, neg_sq]

theorem angularLaw_integral_neg (d : ℝ) (hd : 3 ≤ d) (f : ℝ → ℂ) :
    (∫ theta, f (-theta) ∂angularLaw d) = ∫ theta, f theta ∂angularLaw d := by
  rw [integral_angularLaw_complex d hd, integral_angularLaw_complex d hd]
  have hh := intervalIntegral.integral_comp_neg
    (a := -(Real.pi / 2)) (b := Real.pi / 2) (fun theta => (angularDensity d theta : ℂ) * f theta)
  simp only [neg_neg, angularDensity_neg] at hh
  exact hh

theorem circlePoint_one_pow_two_mul (theta : ℝ) (k : ℕ) :
    circlePoint 1 theta ^ (2 * k) = angularMode k theta := by
  unfold circlePoint angularMode
  simp only [Complex.ofReal_one, one_mul]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem pairedPower_even (u : ℂ) (k : ℕ) (theta : ℝ) :
    pairedPower u (2 * k) theta = u ^ (2 * k) * (angularMode k theta + angularMode (-(k : ℤ)) theta) := by
  have he : Even (2 * k) := ⟨k, by omega⟩
  unfold pairedPower
  rw [mul_pow, mul_pow, he.neg_pow, circlePoint_one_pow_two_mul, circlePoint_one_pow_two_mul]
  have hm : angularMode k (-theta) = angularMode (-(k : ℤ)) theta := by
    unfold angularMode
    congr 1
    push_cast
    ring
  rw [hm]
  ring

theorem pairedPower_odd_neg (u : ℂ) (k : ℕ) (theta : ℝ) :
    pairedPower u (2 * k + 1) (-theta) = -pairedPower u (2 * k + 1) theta := by
  have ho : Odd (2 * k + 1) := ⟨k, by omega⟩
  simp only [pairedPower, neg_neg, mul_pow, ho.neg_pow]
  ring

theorem integral_pairedPower_odd (d : ℝ) (hd : 3 ≤ d) (u : ℂ) (k : ℕ) :
    (∫ theta, pairedPower u (2 * k + 1) theta ∂angularLaw d) = 0 := by
  have hh := angularLaw_integral_neg d hd (pairedPower u (2 * k + 1))
  simp_rw [pairedPower_odd_neg] at hh
  rw [integral_neg] at hh
  have ht : (2 : ℂ) * (∫ theta, pairedPower u (2 * k + 1) theta ∂angularLaw d) = 0 := by
    linear_combination -hh
  exact (mul_eq_zero.mp ht).resolve_left (by norm_num)

theorem integrable_angularMode (d : ℝ) (hd : 3 ≤ d) (k : ℤ) :
    Integrable (angularMode k) (angularLaw d) := by
  letI := angularLaw_isProbability d hd
  exact (integrable_const (1 : ℝ)).mono' (continuous_angularMode k).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun theta => (angularMode_norm k theta).le))

theorem pairedPower_norm_bound (u : ℂ) (n : ℕ) (theta : ℝ) :
    ‖pairedPower u n theta‖ ≤ 2 * ‖u‖ ^ n := by
  unfold pairedPower
  have hh := norm_add_le ((u * circlePoint 1 theta) ^ n) ((-u * circlePoint 1 (-theta)) ^ n)
  simpa only [norm_pow, norm_mul, circlePoint_norm, abs_one, mul_one, norm_neg, two_mul] using hh

theorem continuous_pairedPower (u : ℂ) (n : ℕ) : Continuous (pairedPower u n) := by
  unfold pairedPower circlePoint
  fun_prop

theorem integrable_pairedPower (d : ℝ) (hd : 3 ≤ d) (u : ℂ) (n : ℕ) :
    Integrable (pairedPower u n) (angularLaw d) := by
  letI := angularLaw_isProbability d hd
  exact (integrable_const (2 * ‖u‖ ^ n)).mono' (continuous_pairedPower u n).aestronglyMeasurable
    (Filter.Eventually.of_forall (pairedPower_norm_bound u n))

/-- Exact even paired-power expectations, computed against the actual angular
law and its proved Fourier moments. -/
theorem integral_pairedPower_even (d : ℝ) (hd : 3 ≤ d) (u : ℂ) (k : ℕ) :
    (∫ theta, pairedPower u (2 * k) theta ∂angularLaw d) =
      if k = 0 then 2 else -((d - 2 : ℝ) : ℂ) * u ^ (2 * k) * ((-1 / (d - 1) : ℝ) : ℂ) ^ k := by
  simp_rw [pairedPower_even]
  rw [integral_const_mul, integral_add (integrable_angularMode d hd _) (integrable_angularMode d hd _),
    angularLaw_mode d hd, angularLaw_mode_neg d hd]
  by_cases hk : k = 0
  · subst k; simp <;> norm_num
  · simp only [if_neg hk]
    ring

end GeneralizedBulk.KestenMcKay
