import GeneralizedBulk.Entropy.HermiteEnergy

/-! The Hermite lowering functions are actual coordinate derivatives. -/
noncomputable section
open MeasureTheory Filter Polynomial
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Hermite

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Coordinate factorization, on the actual Gaussian polynomial functions. -/
theorem multiHermite_update_factor (a : I → ℕ) (i : I) (x : I → ℝ) (t : ℝ) :
    multiHermite I a (Function.update x i t) = (hermite (a i)).eval t *
      ∏ j ∈ Finset.univ.erase i, (hermite (a j)).eval (x j) := by
  unfold multiHermite
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j => (hermite (a j)).eval ((Function.update x i t) j)) (Finset.mem_univ i)]
  rw [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  rw [Function.update_of_ne hji]

/-- The actual derivative along a coordinate line is the lowering formula. -/
theorem hasDerivAt_multiHermite_coordinate (a : I → ℕ) (i : I) (x : I → ℝ) :
    HasDerivAt (fun t : ℝ => multiHermite I a (Function.update x i (x i + t)))
      ((a i : ℝ) * multiHermite I (lower a i) x) 0 := by
  have hp0 : HasDerivAt (fun t : ℝ => (hermite (a i)).eval (x i + t))
      ((hermite (a i)).derivative.eval (x i)) 0 := by
    simpa only [id_eq, add_zero, mul_one] using
      ((hermite (a i)).hasDerivAt (x i + 0)).comp 0 ((hasDerivAt_id (0 : ℝ)).const_add (x i))
  have hp := hp0.mul_const (∏ j ∈ Finset.univ.erase i, (hermite (a j)).eval (x j))
  have hfun : (fun t : ℝ => multiHermite I a (Function.update x i (x i + t))) =
      (fun t : ℝ => (hermite (a i)).eval (x i + t) *
        ∏ j ∈ Finset.univ.erase i, (hermite (a j)).eval (x j)) := by
    funext t
    exact multiHermite_update_factor a i x (x i + t)
  rw [hfun]
  convert hp using 1
  by_cases hai : a i = 0
  · simp [hai, hermite]
  · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hai
    have hl : multiHermite I (lower a i) x = (hermite n).eval (x i) *
        ∏ j ∈ Finset.univ.erase i, (hermite (a j)).eval (x j) := by
      have he := multiHermite_update_factor (lower a i) i x (x i)
      rw [Function.update_eq_self] at he
      rw [he]
      simp only [lower, Function.update_self, hn, Nat.add_sub_cancel]
      congr 1
      apply Finset.prod_congr rfl
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      rw [Function.update_of_ne hji]
    rw [hl, hn, derivative_hermite_succ]
    simp only [eval_smul, smul_eq_mul, mul_one, Nat.cast_succ]
    ring

variable {K : Type*} [Fintype K]

def chaosFunction (a : K → I → ℕ) (coeff : K → ℝ) (x : I → ℝ) : ℝ :=
  ∑ k, coeff k * multiHermite I (a k) x

def chaosDerivativeFunction (a : K → I → ℕ) (coeff : K → ℝ) (i : I) (x : I → ℝ) : ℝ :=
  ∑ k, coeff k * (a k i : ℝ) * multiHermite I (lower (a k) i) x

/-- Finite homogeneous Gaussian chaos is differentiated as an actual
polynomial function; the L² derivative above is its genuine representative. -/
theorem hasDerivAt_chaosFunction_coordinate (a : K → I → ℕ) (coeff : K → ℝ)
    (i : I) (x : I → ℝ) :
    HasDerivAt (fun t : ℝ => chaosFunction a coeff (Function.update x i (x i + t)))
      (chaosDerivativeFunction a coeff i x) 0 := by
  simpa only [chaosFunction, chaosDerivativeFunction, mul_assoc] using
    HasDerivAt.sum (u := Finset.univ) (fun k _ =>
      (hasDerivAt_multiHermite_coordinate (a k) i x).const_mul (coeff k))

theorem finite_real_Lp_sum_ae {Ω J : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (s : Finset J) (f : J → Lp ℝ 2 μ) (raw : J → Ω → ℝ)
    (hf : ∀ j, (f j : Ω → ℝ) =ᵐ[μ] raw j) :
    ((∑ j ∈ s, f j : Lp ℝ 2 μ) : Ω → ℝ) =ᵐ[μ] (fun x => ∑ j ∈ s, raw j x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, Pi.zero_apply] using Lp.coeFn_zero ℝ 2 μ
  | @insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    filter_upwards [Lp.coeFn_add (f j) (∑ k ∈ s, f k), hf j, ih] with x hsum hjx hsx
    simpa only [Pi.add_apply, hjx, hsx] using hsum

theorem chaosLp_ae (a : K → I → ℕ) (coeff : K → ℝ) :
    (chaosLp a coeff : (I → ℝ) → ℝ) =ᵐ[standardGaussian I] chaosFunction a coeff := by
  apply finite_real_Lp_sum_ae _ _ _ _
  intro k
  filter_upwards [Lp.coeFn_smul (coeff k) (multiLp I (a k)), multiLp_ae I (a k)] with x hs hx
  simpa only [Pi.smul_apply, smul_eq_mul, hx] using hs

theorem chaosDerivativeLp_ae (a : K → I → ℕ) (coeff : K → ℝ) (i : I) :
    (chaosDerivativeLp a coeff i : (I → ℝ) → ℝ) =ᵐ[standardGaussian I]
      chaosDerivativeFunction a coeff i := by
  apply finite_real_Lp_sum_ae _ _ _ _
  intro k
  filter_upwards [Lp.coeFn_smul (coeff k) (derivativeLp (a k) i), derivativeLp_ae (a k) i] with x hs hx
  simpa only [Pi.smul_apply, smul_eq_mul, hx, mul_assoc] using hs

theorem integral_sq_real_Lp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Lp ℝ 2 μ) :
    (∫ x, f x ^ 2 ∂μ) = ‖f‖ ^ 2 := by
  simpa only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs] using (L2.inner_def (𝕜 := ℝ) f f).symm

theorem integral_chaosFunction_sq (a : K → I → ℕ) (coeff : K → ℝ) :
    (∫ x, chaosFunction a coeff x ^ 2 ∂standardGaussian I) = ‖chaosLp a coeff‖ ^ 2 := by
  rw [← integral_sq_real_Lp]
  exact integral_congr_ae ((chaosLp_ae a coeff).symm.mono (fun x hx => congrArg (fun z : ℝ => z ^ 2) hx))

theorem integral_chaosDerivativeFunction_sq (a : K → I → ℕ) (coeff : K → ℝ) (i : I) :
    (∫ x, chaosDerivativeFunction a coeff i x ^ 2 ∂standardGaussian I) =
      ‖chaosDerivativeLp a coeff i‖ ^ 2 := by
  rw [← integral_sq_real_Lp]
  exact integral_congr_ae ((chaosDerivativeLp_ae a coeff i).symm.mono (fun x hx => congrArg (fun z : ℝ => z ^ 2) hx))

/-- Exact derivative energy, stated entirely in terms of ordinary integrals
of the actual Gaussian polynomial and its actual coordinate derivatives. -/
theorem integral_chaos_derivative_energy (a : K → I → ℕ) (ha : Function.Injective a)
    (coeff : K → ℝ) (degree : ℕ) (hdegree : ∀ k, ∑ i, a k i = degree) :
    (∑ i, ∫ x, chaosDerivativeFunction a coeff i x ^ 2 ∂standardGaussian I) =
      (degree : ℝ) * ∫ x, chaosFunction a coeff x ^ 2 ∂standardGaussian I := by
  simp_rw [integral_chaosDerivativeFunction_sq, integral_chaosFunction_sq]
  exact chaos_derivative_energy a ha coeff degree hdegree

end GeneralizedBulk.Entropy.Hermite
