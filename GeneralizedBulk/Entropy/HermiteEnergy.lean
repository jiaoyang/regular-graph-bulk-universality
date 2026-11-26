import GeneralizedBulk.Entropy.HermiteMultivariate

/-! Concrete finite Gaussian chaos and its exact derivative energy. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Hermite

variable {I : Type*} [Fintype I] [DecidableEq I]

def lower (a : I → ℕ) (i : I) : I → ℕ := Function.update a i (a i - 1)

omit [Fintype I] in
theorem lower_injective_positive {a b : I → ℕ} (i : I) (ha : 0 < a i) (hb : 0 < b i)
    (h : lower a i = lower b i) : a = b := by
  funext j
  have hj := congrFun h j
  by_cases hji : j = i
  · subst j
    simp only [lower, Function.update_self] at hj
    omega
  · simpa only [lower, Function.update_of_ne hji] using hj

/-- Factorial weights transform exactly under the Hermite lowering operator. -/
theorem multiFactorial_lower (a : I → ℕ) (i : I) (ha : 0 < a i) :
    multiFactorial I a = (a i : ℝ) * multiFactorial I (lower a i) := by
  classical
  have ht (j : I) : ((a j).factorial : ℝ) =
      (if j = i then (a i : ℝ) else 1) * ((lower a i j).factorial : ℝ) := by
    by_cases hji : j = i
    · subst j
      cases h : a i with
      | zero => omega
      | succ n => simp [lower, h, Nat.factorial_succ]
    · simp [lower, hji]
  unfold multiFactorial
  simp_rw [ht]
  rw [Finset.prod_mul_distrib]
  simp

/-- The derivative basis is an actual L² Gaussian function. -/
def derivativeLp (a : I → ℕ) (i : I) : Lp ℝ 2 (standardGaussian I) :=
  (a i : ℝ) • multiLp I (lower a i)

theorem derivativeLp_ae (a : I → ℕ) (i : I) :
    (derivativeLp a i : (I → ℝ) → ℝ) =ᵐ[standardGaussian I]
      (fun x => (a i : ℝ) * multiHermite I (lower a i) x) := by
  filter_upwards [Lp.coeFn_smul (a i : ℝ) (multiLp I (lower a i)), multiLp_ae I (lower a i)] with x hs hx
  simpa only [derivativeLp, Pi.smul_apply, smul_eq_mul, hx] using hs

/-- Exact Gaussian inner products of the actual coordinate derivatives. -/
theorem derivativeLp_inner (a b : I → ℕ) (i : I) :
    @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ (derivativeLp a i) (derivativeLp b i) =
      if a = b then (a i : ℝ) * multiFactorial I a else 0 := by
  simp only [derivativeLp, inner_smul_left, inner_smul_right, starRingEnd_apply,
    star_trivial, multiLp_inner]
  by_cases hab : a = b
  · subst b
    simp only [↓reduceIte]
    by_cases hai : a i = 0
    · simp [hai]
    · rw [multiFactorial_lower a i (Nat.pos_of_ne_zero hai)]
  · simp only [hab, ↓reduceIte]
    by_cases hai : a i = 0
    · simp [hai]
    by_cases hbi : b i = 0
    · simp [hbi]
    have hl : lower a i ≠ lower b i := fun h => hab
      (lower_injective_positive i (Nat.pos_of_ne_zero hai) (Nat.pos_of_ne_zero hbi) h)
    simp [hl]

section FiniteChaos
variable {K : Type*} [Fintype K]

/-- A finite actual Gaussian chaos, with distinct Hermite multiindices. -/
def chaosLp (a : K → I → ℕ) (coeff : K → ℝ) : Lp ℝ 2 (standardGaussian I) :=
  ∑ k, coeff k • multiLp I (a k)

def chaosDerivativeLp (a : K → I → ℕ) (coeff : K → ℝ) (i : I) : Lp ℝ 2 (standardGaussian I) :=
  ∑ k, coeff k • derivativeLp (a k) i

omit [DecidableEq I] in
/-- The true L² norm of a finite Hermite chaos is its factorial-weighted
coefficient norm. -/
theorem chaosLp_norm_sq (a : K → I → ℕ) (ha : Function.Injective a) (coeff : K → ℝ) :
    ‖chaosLp a coeff‖ ^ 2 = ∑ k, coeff k ^ 2 * multiFactorial I (a k) := by
  classical
  rw [← real_inner_self_eq_norm_sq]
  simp only [chaosLp, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    starRingEnd_apply, star_trivial, multiLp_inner]
  simp_rw [ha.eq_iff]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem chaosDerivativeLp_norm_sq (a : K → I → ℕ) (ha : Function.Injective a)
    (coeff : K → ℝ) (i : I) :
    ‖chaosDerivativeLp a coeff i‖ ^ 2 =
      ∑ k, coeff k ^ 2 * (a k i : ℝ) * multiFactorial I (a k) := by
  classical
  rw [← real_inner_self_eq_norm_sq]
  simp only [chaosDerivativeLp, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    starRingEnd_apply, star_trivial, derivativeLp_inner]
  simp_rw [ha.eq_iff]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- The exact Gaussian chaos derivative-energy identity. It holds for every
degree and every finite coefficient family, for the actual Gaussian L² norm. -/
theorem chaos_derivative_energy (a : K → I → ℕ) (ha : Function.Injective a)
    (coeff : K → ℝ) (degree : ℕ) (hdegree : ∀ k, ∑ i, a k i = degree) :
    (∑ i, ‖chaosDerivativeLp a coeff i‖ ^ 2) = (degree : ℝ) * ‖chaosLp a coeff‖ ^ 2 := by
  simp_rw [chaosDerivativeLp_norm_sq a ha coeff]
  rw [Finset.sum_comm, chaosLp_norm_sq a ha coeff, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  calc
    (∑ i, coeff k ^ 2 * (a k i : ℝ) * multiFactorial I (a k)) =
        (coeff k ^ 2 * multiFactorial I (a k)) * ∑ i, (a k i : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by rw [← Nat.cast_sum, hdegree]; ring

end FiniteChaos
end GeneralizedBulk.Entropy.Hermite
