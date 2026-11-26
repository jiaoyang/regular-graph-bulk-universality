import BourgadeHuang.MultivariateExponentialLoop

/-! Polynomial test functions derived from the original mixed-word hierarchy.
The syntax below is only an induction device; all conclusions concern the actual
integrals of its evaluated complex polynomial and its directional derivative. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace BourgadeHuang

inductive LoopTest (m : ℕ) where
  | const : ℂ → LoopTest m
  | add : LoopTest m → LoopTest m → LoopTest m
  | mulVar : Fin m → LoopTest m → LoopTest m

namespace LoopTest

def eval {m : ℕ} : LoopTest m → (Fin m → ℂ) → ℂ
  | .const c, _ => c
  | .add P Q, X => P.eval X + Q.eval X
  | .mulVar i P, X => X i * P.eval X

def directional {m : ℕ} : LoopTest m → (Fin m → ℂ) → (Fin m → ℂ) → ℂ
  | .const _, _, _ => 0
  | .add P Q, X, J => P.directional X J + Q.directional X J
  | .mulVar i P, X, J => J i * P.eval X + X i * P.directional X J

def scale {m : ℕ} (c : ℂ) : LoopTest m → LoopTest m
  | .const a => .const (c*a)
  | .add P Q => .add (P.scale c) (Q.scale c)
  | .mulVar i P => .mulVar i (P.scale c)

def mul {m : ℕ} : LoopTest m → LoopTest m → LoopTest m
  | .const c, Q => Q.scale c
  | .add P R, Q => .add (P.mul Q) (R.mul Q)
  | .mulVar i P, Q => .mulVar i (P.mul Q)

def pow {m : ℕ} (P : LoopTest m) : ℕ → LoopTest m
  | 0 => .const 1
  | n+1 => P.mul (P.pow n)

theorem eval_scale {m : ℕ} (P : LoopTest m) (c : ℂ) (X : Fin m → ℂ) :
    (P.scale c).eval X = c * P.eval X := by
  induction P with
  | const a => rfl
  | add P Q ihP ihQ => simp only [scale, eval, ihP, ihQ]; ring
  | mulVar i P ih => simp only [scale, eval, ih]; ring

theorem directional_scale {m : ℕ} (P : LoopTest m) (c : ℂ) (X J : Fin m → ℂ) :
    (P.scale c).directional X J = c * P.directional X J := by
  induction P with
  | const a => simp [scale, directional]
  | add P Q ihP ihQ => simp only [scale, directional, ihP, ihQ]; ring
  | mulVar i P ih => simp only [scale, directional, eval_scale, ih]; ring

theorem eval_mul {m : ℕ} (P Q : LoopTest m) (X : Fin m → ℂ) :
    (P.mul Q).eval X = P.eval X * Q.eval X := by
  induction P with
  | const c => exact eval_scale Q c X
  | add P R ihP ihR => simp only [mul, eval, ihP, ihR]; ring
  | mulVar i P ih => simp only [mul, eval, ih]; ring

theorem directional_mul {m : ℕ} (P Q : LoopTest m) (X J : Fin m → ℂ) :
    (P.mul Q).directional X J =
      P.directional X J * Q.eval X + P.eval X * Q.directional X J := by
  induction P with
  | const c => simp [mul, eval, directional, directional_scale]
  | add P R ihP ihR => simp only [mul, directional, eval, ihP, ihR]; ring
  | mulVar i P ih => simp only [mul, directional, eval_mul, eval, ih]; ring

theorem eval_pow {m : ℕ} (P : LoopTest m) (n : ℕ) (X : Fin m → ℂ) :
    (P.pow n).eval X = P.eval X ^ n := by
  induction n with
  | zero => simp [pow, eval]
  | succ n ih => rw [pow, eval_mul, ih, pow_succ]; ring

theorem directional_pow {m : ℕ} (P : LoopTest m) (n : ℕ) (X J : Fin m → ℂ) :
    (P.pow n).directional X J = (n:ℂ) * P.eval X ^ (n-1) * P.directional X J := by
  induction n with
  | zero => simp [pow, directional]
  | succ n ih =>
    rw [pow, directional_mul, eval_pow, ih]
    cases n with
    | zero => simp [pow, eval, directional]
    | succ n => simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]; ring

end LoopTest

private theorem interaction_sum_cons {n : ℕ} (X J : Fin n → ℂ) (x j : ℂ) :
    (∑ a : Fin (n+1), (Fin.cons (α := fun _ => ℂ) j J) a * excludedProduct (Fin.cons (α := fun _ => ℂ) x X) a) =
      j * (∏ a, X a) + x * ∑ a, J a * excludedProduct X a := by
  have hl : HasDerivAt (fun z : ℂ => ∏ a : Fin (n+1),
      ((Fin.cons (α := fun _ => ℂ) x X) a + z * (Fin.cons (α := fun _ => ℂ) j J) a))
      (∑ a : Fin (n+1), (Fin.cons (α := fun _ => ℂ) j J) a * excludedProduct (Fin.cons (α := fun _ => ℂ) x X) a) 0 := by
    have h := HasDerivAt.finset_prod (fun a (_ : a ∈ (Finset.univ : Finset (Fin (n+1)))) =>
      (hasDerivAt_const 0 ((Fin.cons (α := fun _ => ℂ) x X) a)).add
        ((hasDerivAt_id 0).mul_const ((Fin.cons (α := fun _ => ℂ) j J) a)))
    simpa only [id_eq, zero_mul, add_zero, zero_add, one_mul, smul_eq_mul,
      excludedProduct, mul_comm ((Fin.cons (α := fun _ => ℂ) j J) _)] using h
  have htail : HasDerivAt (fun z : ℂ => ∏ a : Fin n, (X a + z * J a))
      (∑ a : Fin n, J a * excludedProduct X a) 0 := by
    have h := HasDerivAt.finset_prod (fun a (_ : a ∈ (Finset.univ : Finset (Fin n))) =>
      (hasDerivAt_const 0 (X a)).add ((hasDerivAt_id 0).mul_const (J a)))
    simpa only [id_eq, zero_mul, add_zero, zero_add, one_mul, smul_eq_mul,
      excludedProduct, mul_comm (J _)] using h
  have hr := ((hasDerivAt_const 0 x).add ((hasDerivAt_id 0).mul_const j)).mul htail
  have heq : (fun z : ℂ => ∏ a : Fin (n+1), ((Fin.cons (α := fun _ => ℂ) x X) a + z * (Fin.cons (α := fun _ => ℂ) j J) a)) =
      (fun z : ℂ => (x + z*j) * ∏ a : Fin n, (X a + z*J a)) := by
    funext z
    rw [Fin.prod_univ_succ]
    simp
  rw [heq] at hl
  simpa only [id_eq, zero_mul, add_zero, zero_add, one_mul] using hl.unique hr

/-- Every finite polynomial in off-real resolvents is a legitimate test in the
exact hierarchy. The directional derivative includes all repetitions. -/
theorem exactHierarchy_polynomial_test
    (ν : Measure AnchoredCountingState) (β : Beta) (hh : ExactAnchoredHierarchy ν β)
    {m : ℕ} {w : ℂ} {v : Fin m → ℂ} (hw : w.im ≠ 0) (hv : ∀ i, (v i).im ≠ 0)
    (P : LoopTest m) :
    let X := fun s : AnchoredCountingState => fun i => anchoredNevanlinna s (v i)
    let J := fun s : AnchoredCountingState => fun i => (2/β.value) * anchoredInteraction s w (v i)
    Integrable (fun s => anchoredLoopHead β s w * P.eval (X s) + P.directional (X s) (J s)) ν ∧
      (∫ s, anchoredLoopHead β s w * P.eval (X s) + P.directional (X s) (J s) ∂ν) = 0 := by
  let X := fun s : AnchoredCountingState => fun i => anchoredNevanlinna s (v i)
  let J := fun s : AnchoredCountingState => fun i => (2/β.value) * anchoredInteraction s w (v i)
  have hstrong (P : LoopTest m) : ∀ (n : ℕ) (u : Fin n → ℂ) (hu : ∀ i, (u i).im ≠ 0),
      Integrable (fun s => anchoredLoopHead β s w * P.eval (X s) * (∏ i, anchoredNevanlinna s (u i)) +
        P.directional (X s) (J s) * (∏ i, anchoredNevanlinna s (u i)) +
        P.eval (X s) * ∑ i, ((2/β.value) * anchoredInteraction s w (u i)) *
          excludedProduct (fun a => anchoredNevanlinna s (u a)) i) ν ∧
      (∫ s, anchoredLoopHead β s w * P.eval (X s) * (∏ i, anchoredNevanlinna s (u i)) +
        P.directional (X s) (J s) * (∏ i, anchoredNevanlinna s (u i)) +
        P.eval (X s) * ∑ i, ((2/β.value) * anchoredInteraction s w (u i)) *
          excludedProduct (fun a => anchoredNevanlinna s (u a)) i ∂ν) = 0 := by
    induction P with
    | const c =>
      intro n u hu
      obtain ⟨hi,hz⟩ := hh n w hw u hu
      have heq (s : AnchoredCountingState) :
          anchoredLoopHead β s w * c * (∏ i, anchoredNevanlinna s (u i)) +
          0 * (∏ i, anchoredNevanlinna s (u i)) +
          c * ∑ i, ((2/β.value) * anchoredInteraction s w (u i)) *
            excludedProduct (fun a => anchoredNevanlinna s (u a)) i = c * anchoredLoopIntegrand β s w u := by
        simp only [anchoredLoopIntegrand, anchoredLoopHead]
        simp_rw [mul_assoc (2 / β.value)]
        rw [← Finset.mul_sum]
        ring
      simpa only [LoopTest.eval, LoopTest.directional, heq, integral_const_mul, hz, mul_zero] using
        And.intro (hi.const_mul c) (show c * (∫ s, anchoredLoopIntegrand β s w u ∂ν) = 0 by rw [hz,mul_zero])
    | add P Q ihP ihQ =>
      intro n u hu
      obtain ⟨hPi,hPz⟩ := ihP n u hu
      obtain ⟨hQi,hQz⟩ := ihQ n u hu
      constructor
      · convert hPi.add hQi using 1 <;> ext s <;> simp only [Pi.add_apply, LoopTest.eval,LoopTest.directional] <;> ring
      · have hz := congrArg₂ (fun a b : ℂ => a+b) hPz hQz
        dsimp only at hz
        rw [← integral_add hPi hQi] at hz
        convert hz using 1
        · apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun s => by
            simp only [LoopTest.eval,LoopTest.directional]; ring)
        · simp
    | mulVar i P ih =>
      intro n u hu
      have hcons : ∀ j, ((Fin.cons (α := fun _ => ℂ) (v i) u) j).im ≠ 0 := by
        intro j
        refine Fin.cases (hv i) (fun j => hu j) j
      obtain ⟨hi,hz⟩ := ih (n+1) (Fin.cons (α := fun _ => ℂ) (v i) u) hcons
      have heq (s : AnchoredCountingState) :
          (∑ a : Fin (n+1), ((2/β.value) * anchoredInteraction s w ((Fin.cons (α := fun _ => ℂ) (v i) u) a)) *
            excludedProduct (fun a => anchoredNevanlinna s ((Fin.cons (α := fun _ => ℂ) (v i) u) a)) a) =
          J s i * (∏ a, anchoredNevanlinna s (u a)) + X s i *
            ∑ a, ((2/β.value) * anchoredInteraction s w (u a)) *
              excludedProduct (fun b => anchoredNevanlinna s (u b)) a := by
        have hXc : (fun a => anchoredNevanlinna s ((Fin.cons (α := fun _ => ℂ) (v i) u) a)) =
            Fin.cons (α := fun _ => ℂ) (X s i) (fun a => anchoredNevanlinna s (u a)) := by
          funext a
          exact Fin.cases rfl (fun _ => rfl) a
        have hJc : (fun a => (2/β.value) * anchoredInteraction s w ((Fin.cons (α := fun _ => ℂ) (v i) u) a)) =
            Fin.cons (α := fun _ => ℂ) (J s i) (fun a => (2/β.value) * anchoredInteraction s w (u a)) := by
          funext a
          exact Fin.cases rfl (fun _ => rfl) a
        simp only [hXc, congrFun hJc]
        exact interaction_sum_cons _ _ _ _
      constructor
      · convert hi using 1
        ext s
        dsimp only
        rw [heq,Fin.prod_univ_succ]
        simp only [LoopTest.eval,LoopTest.directional,Fin.cons_zero,Fin.cons_succ,X,J]
        ring
      · convert hz using 1
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun s => by
          dsimp only
          rw [heq,Fin.prod_univ_succ]
          simp only [LoopTest.eval,LoopTest.directional,Fin.cons_zero,Fin.cons_succ,X,J]
          ring)
  simpa only [Fin.prod_univ_zero,Fin.sum_univ_zero,mul_one,mul_zero,add_zero] using
    hstrong P 0 Fin.elim0 (fun i => Fin.elim0 i)

end BourgadeHuang
