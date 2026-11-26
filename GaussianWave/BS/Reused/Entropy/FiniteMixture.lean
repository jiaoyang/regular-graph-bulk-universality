import GaussianWave.BS.Reused.Entropy.FiniteShannon

/-! Finite entropy splitting and mixture inequalities, including zero masses. -/
noncomputable section
open scoped BigOperators Classical

namespace GaussianWave.BS.Reused.Entropy.Finite

lemma negMulLog_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.negMulLog (x+y) ≤ Real.negMulLog x+Real.negMulLog y := by
  by_cases hx0 : x = 0
  · subst x; simp
  by_cases hy0 : y = 0
  · subst y; simp
  have hx' := lt_of_le_of_ne hx (Ne.symm hx0)
  have hy' := lt_of_le_of_ne hy (Ne.symm hy0)
  have hlx := Real.log_le_log hx' (le_add_of_nonneg_right hy)
  have hly := Real.log_le_log hy' (le_add_of_nonneg_left hx)
  unfold Real.negMulLog
  nlinarith [mul_le_mul_of_nonneg_left hlx hx,mul_le_mul_of_nonneg_left hly hy]

theorem entropy_add_le {A : Type*} [Fintype A] (p q : A → ℝ)
    (hp : ∀ a,0 ≤ p a) (hq : ∀ a,0 ≤ q a) :
    entropy (fun a => p a+q a) ≤ entropy p+entropy q := by
  rw [entropy,entropy,entropy,← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun a ha => negMulLog_add_le (hp a) (hq a))

theorem entropy_scale {A : Type*} [Fintype A] (c : ℝ) (p : A → ℝ) :
    entropy (fun a => c*p a) = c*entropy p+Real.negMulLog c*(∑ a,p a) := by
  simp only [entropy,Real.negMulLog_mul,Finset.sum_add_distrib,← Finset.sum_mul,← Finset.mul_sum]
  ring

theorem entropy_lower_total {A : Type*} [Fintype A] (p : A → ℝ) (hp : ∀ a,0 ≤ p a) :
    Real.negMulLog (∑ a,p a) ≤ entropy p := by
  have h : ∀ s : Finset A, Real.negMulLog (∑ a ∈ s,p a) ≤ ∑ a ∈ s,Real.negMulLog (p a) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha,Finset.sum_insert ha]
      exact (negMulLog_add_le (hp a) (Finset.sum_nonneg (fun a ha => hp a))).trans (add_le_add_left ih _)
  exact h Finset.univ

theorem entropy_nonneg {A : Type*} [Fintype A] (p : A → ℝ)
    (hp : ∀ a,0 ≤ p a) (hsum : ∑ a,p a = 1) : 0 ≤ entropy p := by
  have h := entropy_lower_total p hp
  simpa only [hsum,Real.negMulLog_one] using h

theorem entropy_mixture_lower {A : Type*} [Fintype A]
    (p q : A → ℝ) (hp : ∀ a,0 ≤ p a) (hq : ∀ a,0 ≤ q a)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b = 1) :
    a*entropy p+b*entropy q ≤ entropy (fun x => a*p x+b*q x) := by
  have h := entropy_concave_mixture (fun i : Fin 2 => ![a,b] i)
    (by intro i; fin_cases i <;> simp [ha,hb])
    (by simpa only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one] using hab)
    (fun i : Fin 2 => ![p,q] i) (by intro i x; fin_cases i <;> simp [hp,hq])
  simpa only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one] using h

theorem entropy_mixture_upper {A : Type*} [Fintype A]
    (p q : A → ℝ) (hp : ∀ a,0 ≤ p a) (hq : ∀ a,0 ≤ q a)
    (hpsum : ∑ x,p x = 1) (hqsum : ∑ x,q x = 1)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    entropy (fun x => a*p x+b*q x) ≤
      a*entropy p+b*entropy q+Real.negMulLog a+Real.negMulLog b := by
  apply (entropy_add_le (fun x => a*p x) (fun x => b*q x)
    (fun x => mul_nonneg ha (hp x)) (fun x => mul_nonneg hb (hq x))).trans_eq
  rw [entropy_scale,entropy_scale,hpsum,hqsum]
  ring

end GaussianWave.BS.Reused.Entropy.Finite
