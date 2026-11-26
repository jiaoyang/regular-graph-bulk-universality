import GeneralizedBulk.Entropy.GaussianExponentialMoments

/-! Orthogonality to every Hermite polynomial annihilates the actual Fourier
transform, by a proved exponentially dominated Taylor expansion. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Hermite
variable {I : Type*} [Fintype I] [DecidableEq I]

def HermiteOrthogonal (f : Lp ℝ 2 (standardGaussian I)) : Prop :=
  ∀ a : I → ℕ, @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ f (multiLp I a) = 0

theorem integral_mul_eq_zero_of_filtration (f : Lp ℝ 2 (standardGaussian I)) (hf : HermiteOrthogonal f)
    {P : (I → ℝ) → ℝ} {degree : ℕ} (hP : P ∈ functionFiltration degree) :
    (∫ x, f x * P x ∂standardGaussian I) = 0 := by
  dsimp only [HermiteOrthogonal] at hf
  obtain ⟨coeff, hc⟩ := exists_functionFiltration_coefficients I hP
  have hinner : @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ f (chaosLp (atMostIndexNat I) coeff) = 0 := by
    simp only [chaosLp, inner_sum, inner_smul_right, hf, mul_zero, Finset.sum_const_zero]
  rw [L2.inner_def] at hinner
  calc
    _ = ∫ x, @inner ℝ ℝ _ (f x) (chaosLp (atMostIndexNat I) coeff x) ∂standardGaussian I := by
      apply integral_congr_ae
      filter_upwards [chaosLp_ae (atMostIndexNat I) coeff] with x hx
      rw [hx, hc]
      simp only [RCLike.inner_apply, conj_trivial, mul_comm]
    _ = 0 := hinner

theorem integral_mul_linearForm_pow_eq_zero (f : Lp ℝ 2 (standardGaussian I)) (hf : HermiteOrthogonal f)
    (t : I → ℝ) (n : ℕ) : (∫ x, f x * linearForm t x ^ n ∂standardGaussian I) = 0 := by
  apply integral_mul_eq_zero_of_filtration f hf
  have hh := linearForm_pow_mul_mem (I := I) (one_mem_functionFiltration (I := I)) t n
  simpa only [mul_one, Nat.zero_add] using hh

private theorem real_exp_hasSum (x : ℝ) : HasSum (fun n : ℕ => x ^ n / (n.factorial : ℝ)) (Real.exp x) := by
  simpa only [← Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp ℝ x

private theorem complex_exp_hasSum (x : ℂ) : HasSum (fun n : ℕ => x ^ n / (n.factorial : ℂ)) (Complex.exp x) := by
  simpa only [← Complex.exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp ℂ x

/-- No completeness assumption enters: the exponentially integrable Gaussian
majorant permits termwise integration for an arbitrary Gaussian L² vector. -/
theorem hermiteOrthogonal_fourier_zero (f : Lp ℝ 2 (standardGaussian I)) (hf : HermiteOrthogonal f)
    (t : I → ℝ) :
    (∫ x, (f x : ℂ) * Complex.exp ((linearForm t x : ℂ) * Complex.I) ∂standardGaussian I) = 0 := by
  let F : ℕ → (I → ℝ) → ℂ := fun n x => (f x : ℂ) * (((linearForm t x : ℂ) * Complex.I) ^ n / (n.factorial : ℂ))
  let B : ℕ → (I → ℝ) → ℝ := fun n x => |f x| * (|linearForm t x| ^ n / (n.factorial : ℝ))
  have hsum (x : I → ℝ) : HasSum (fun n => B n x) (|f x| * Real.exp |linearForm t x|) :=
    (real_exp_hasSum |linearForm t x|).mul_left |f x|
  have hFmeas (n : ℕ) : AEStronglyMeasurable (F n) (standardGaussian I) := by
    have hpoly : Continuous (fun x : I → ℝ => ((linearForm t x : ℂ) * Complex.I) ^ n / (n.factorial : ℂ)) := by
      unfold linearForm
      fun_prop
    exact (Complex.continuous_ofReal.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f)).mul hpoly.aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ x ∂standardGaussian I, ‖F n x‖ ≤ B n x := by
    filter_upwards with x
    simp only [F, B, norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_I, mul_one, Complex.norm_natCast, Nat.cast_nonneg, abs_of_nonneg, le_refl]
  have hBint : Integrable (fun x => ∑' n, B n x) (standardGaussian I) := by
    have heq : (fun x => ∑' n, B n x) = fun x => |f x| * Real.exp |linearForm t x| :=
      funext (fun x => (hsum x).tsum_eq)
    rw [heq]
    exact integrable_abs_Lp_mul_exp_abs_linearForm f t
  have hlim : ∀ᵐ x ∂standardGaussian I,
      HasSum (fun n => F n x) ((f x : ℂ) * Complex.exp ((linearForm t x : ℂ) * Complex.I)) := by
    filter_upwards with x
    exact (complex_exp_hasSum _).mul_left (f x : ℂ)
  have hser := hasSum_integral_of_dominated_convergence B hFmeas hbound
    (Eventually.of_forall (fun x => (hsum x).summable)) hBint hlim
  have hterm (n : ℕ) : (∫ x, F n x ∂standardGaussian I) = 0 := by
    have heq : F n = fun x => ((f x * linearForm t x ^ n : ℝ) : ℂ) * (Complex.I ^ n / (n.factorial : ℂ)) := by
      funext x
      simp only [F, mul_pow, Complex.ofReal_mul, Complex.ofReal_pow]
      ring
    rw [heq, integral_mul_const, integral_complex_ofReal,
      integral_mul_linearForm_pow_eq_zero f hf t n, Complex.ofReal_zero, zero_mul]
  have hser0 : HasSum (fun _ : ℕ => (0 : ℂ))
      (∫ x, (f x : ℂ) * Complex.exp ((linearForm t x : ℂ) * Complex.I) ∂standardGaussian I) := by
    simpa only [hterm] using hser
  exact hser0.unique hasSum_zero

end GeneralizedBulk.Entropy.Hermite
