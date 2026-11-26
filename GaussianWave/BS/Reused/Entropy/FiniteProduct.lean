import GaussianWave.BS.Reused.Entropy.FiniteShannon

/-! Literal Shannon entropy of finite independent product colorings. -/
noncomputable section
open scoped BigOperators Classical

namespace GaussianWave.BS.Reused.Entropy.Finite

theorem entropy_product {A B : Type*} [Fintype A] [Fintype B]
    (p : A → ℝ) (q : B → ℝ) (hp : ∑ a,p a = 1) (hq : ∑ b,q b = 1) :
    entropy (fun z : A × B => p z.1*q z.2) = entropy p+entropy q := by
  simp only [entropy,Fintype.sum_prod_type,Real.negMulLog_mul,Finset.sum_add_distrib,
    ← Finset.sum_mul,← Finset.mul_sum,hp,hq,one_mul,mul_one]

/-- This is the actual finite product probability mass, with position-dependent
one-site laws, rather than an assumed independence certificate. -/
def productMass {A : Type*} {N : ℕ} (p : Fin N → A → ℝ) (w : Fin N → A) : ℝ :=
  ∏ v,p v (w v)

theorem productMass_nonneg {A : Type*} {N : ℕ} (p : Fin N → A → ℝ)
    (hp : ∀ v a,0 ≤ p v a) (w : Fin N → A) : 0 ≤ productMass p w :=
  Finset.prod_nonneg (fun v hv => hp v (w v))

theorem productMass_sum {A : Type*} [Fintype A] {N : ℕ} (p : Fin N → A → ℝ)
    (hp : ∀ v,∑ a,p v a = 1) : (∑ w : Fin N → A,productMass p w) = 1 := by
  have h := Finset.prod_univ_sum (fun _v : Fin N => (Finset.univ : Finset A)) p
  simpa only [hp,Finset.prod_const_one,Fintype.piFinset_univ,productMass] using h.symm

set_option maxHeartbeats 1000000 in
theorem entropy_productMass {A : Type*} [Fintype A] (N : ℕ)
    (p : Fin N → A → ℝ) (hp : ∀ v,∑ a,p v a = 1) :
    entropy (productMass p) = ∑ v,entropy (p v) := by
  induction N with
  | zero => simp [entropy,productMass]
  | succ N ih =>
    let tail : Fin N → A → ℝ := fun j => p j.succ
    have htail : ∀ j,∑ a,tail j a = 1 := fun j => hp j.succ
    have he : entropy (productMass p) =
        entropy (fun z : A × (Fin N → A) => p 0 z.1*productMass tail z.2) := by
      unfold entropy
      rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (N+1) => A))]
      apply Finset.sum_congr rfl
      intro z hz
      congr 1
      simp only [productMass,Fin.prod_univ_succ,Fin.consEquiv_apply,Fin.cons_zero,Fin.cons_succ,tail]
    rw [he,entropy_product (p 0) (productMass tail) (hp 0) (productMass_sum tail htail),
      ih tail htail,Fin.sum_univ_succ]

end GaussianWave.BS.Reused.Entropy.Finite
