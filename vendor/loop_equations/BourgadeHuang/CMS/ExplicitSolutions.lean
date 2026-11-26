import BourgadeHuang.CMS.ExplicitFunctions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NthRewrite

noncomputable section
open scoped BigOperators

namespace BourgadeHuang.CMS

/-- Incidence of a coordinate in one ordered difference. -/
def pairSlope {d : ℕ} (i : Fin d) (p : Fin d × Fin d) : ℂ :=
  (if p.1 = i then 1 else 0) - (if p.2 = i then 1 else 0)

/-- A finite, branch-free logarithmic derivative, prior to collecting by neighbors. -/
def pairLogDerivative {d : ℕ} (σ : Fin d → Sign) (i : Fin d) (z : Point d) : ℂ :=
  ∑ p ∈ oppositePairs σ, -pairSlope i p / (z p.1 - z p.2)

/-- The neighbor-sum logarithmic derivative of Appendix D.2. -/
def psi {d : ℕ} (σ : Fin d → Sign) (i : Fin d) (z : Point d) : ℂ :=
  - ∑ j ∈ Finset.univ.erase i, if σ j ≠ σ i then (z i - z j)⁻¹ else 0

theorem delta_ne_zero {d : ℕ} (σ : Fin d → Sign) {z : Point d}
    (hz : CollisionFree z) : delta σ z ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact inv_ne_zero (hz.sub_ne_zero (ne_of_lt (Finset.mem_filter.mp hp).2.1))

theorem explicitSolution_ne_zero {d : ℕ} (σ : Fin d → Sign) {z : Point d}
    (hz : CollisionFree z) : explicitSolution σ z ≠ 0 :=
  mul_ne_zero (Complex.exp_ne_zero _) (delta_ne_zero σ hz)

theorem hasDerivAt_pairInverse {d : ℕ} (z : Point d) (i : Fin d)
    (p : Fin d × Fin d) (hp : z p.1 - z p.2 ≠ 0) :
    HasDerivAt
      (fun w : ℂ => (Function.update z i w p.1 - Function.update z i w p.2)⁻¹)
      ((-pairSlope i p / (z p.1 - z p.2)) * (z p.1 - z p.2)⁻¹) (z i) := by
  have hd := (hasDerivAt_update_coord z i p.1).sub (hasDerivAt_update_coord z i p.2)
  have h := hd.inv (by simpa using hp)
  convert h using 1 <;> simp only [Function.update_eq_self, pairSlope]
  field_simp [hp] <;> ring <;> simp

theorem hasDerivAt_delta {d : ℕ} (σ : Fin d → Sign) {z : Point d}
    (hz : CollisionFree z) (i : Fin d) :
    HasDerivAt (fun w : ℂ => delta σ (Function.update z i w))
      (pairLogDerivative σ i z * delta σ z) (z i) := by
  have h := hasDerivAt_finset_prod_log (oppositePairs σ)
    (fun p w => (Function.update z i w p.1 - Function.update z i w p.2)⁻¹)
    (fun p => -pairSlope i p / (z p.1 - z p.2)) (z i)
    (fun p hp => by
      have hp' := (Finset.mem_filter.mp hp).2.1
      simpa using hasDerivAt_pairInverse z i p (hz.sub_ne_zero (ne_of_lt hp')))
  simpa [delta, pairLogDerivative] using h

theorem hasDerivAt_phase {d : ℕ} (σ : Fin d → Sign) (z : Point d) (i : Fin d) :
    HasDerivAt (fun w : ℂ => phase σ (Function.update z i w))
      (Complex.I * signValue (σ i)) (z i) := by
  have h := (HasDerivAt.sum (u := Finset.univ)
    (fun j _ => (hasDerivAt_update_coord z i j).const_mul (signValue (σ j)))).const_mul Complex.I
  simpa [phase, mul_ite] using h

theorem hasDerivAt_explicitSolution_pair {d : ℕ} (σ : Fin d → Sign) {z : Point d}
    (hz : CollisionFree z) (i : Fin d) :
    HasDerivAt (fun w : ℂ => explicitSolution σ (Function.update z i w))
      ((Complex.I * signValue (σ i) + pairLogDerivative σ i z) *
        explicitSolution σ z) (z i) := by
  have h := ((hasDerivAt_phase σ z i).cexp).mul (hasDerivAt_delta σ hz i)
  convert h using 1 <;> simp only [explicitSolution, Function.update_eq_self]
  ring

theorem partial_explicitSolution_pair {d : ℕ} (σ : Fin d → Sign) {z : Point d}
    (hz : CollisionFree z) (i : Fin d) :
    coordDeriv i (explicitSolution σ) z =
      (Complex.I * signValue (σ i) + pairLogDerivative σ i z) * explicitSolution σ z :=
  (hasDerivAt_explicitSolution_pair σ hz i).deriv


private theorem sum_oppositePairs_first {d : ℕ} (σ : Fin d → Sign) (i : Fin d)
    (f : Fin d × Fin d → ℂ) :
    (∑ p ∈ oppositePairs σ, if p.1 = i then f p else 0) =
      ∑ j, if i < j ∧ σ i ≠ σ j then f (i, j) else 0 := by
  classical
  simp only [oppositePairs, Finset.sum_filter, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · apply Finset.sum_congr rfl
    intro j _
    simp
  · intro j _ hji
    simp [hji]
  · simp

private theorem sum_oppositePairs_second {d : ℕ} (σ : Fin d → Sign) (i : Fin d)
    (f : Fin d × Fin d → ℂ) :
    (∑ p ∈ oppositePairs σ, if p.2 = i then f p else 0) =
      ∑ j, if j < i ∧ σ j ≠ σ i then f (j, i) else 0 := by
  classical
  simp only [oppositePairs, Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hki
    simp [hki]
  · simp

theorem pairLogDerivative_eq_psi {d : ℕ} (σ : Fin d → Sign)
    (i : Fin d) (z : Point d) : pairLogDerivative σ i z = psi σ i z := by
  classical
  have hterm : ∀ p : Fin d × Fin d,
      -pairSlope i p / (z p.1 - z p.2) =
        (if p.2 = i then (z p.1 - z p.2)⁻¹ else 0) -
        (if p.1 = i then (z p.1 - z p.2)⁻¹ else 0) := by
    intro p
    simp only [pairSlope, neg_sub, sub_div, ite_div, one_div, zero_div]
  simp_rw [pairLogDerivative, hterm]
  rw [Finset.sum_sub_distrib, sum_oppositePairs_second, sum_oppositePairs_first]
  unfold psi
  rw [← Finset.sum_sub_distrib]
  have herase : (∑ j ∈ Finset.univ.erase i,
      if σ j ≠ σ i then (z i - z j)⁻¹ else 0) =
      ∑ j, if σ j ≠ σ i then (z i - z j)⁻¹ else 0 := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
    simp
  rw [herase, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rcases lt_trichotomy j i with hji | rfl | hij
  · have hnot : ¬ i < j := not_lt.mpr (le_of_lt hji)
    by_cases hs : σ j = σ i
    · simp [hji, hnot, hs]
    · simp only [hji, hnot, hs, true_and, if_true, if_false, sub_zero]
      rw [show z j - z i = -(z i - z j) by ring, inv_neg]
      simp [hs]
  · simp
  · have hnot : ¬ j < i := not_lt.mpr (le_of_lt hij)
    by_cases hs : σ j = σ i
    · simp [hij, hnot, hs]
    · have hsi : σ i ≠ σ j := Ne.symm hs
      simp [hij, hnot, hs, hsi]

theorem hasDerivAt_explicitSolution {d : ℕ} (σ : Fin d → Sign) {z : Point d}
    (hz : CollisionFree z) (i : Fin d) :
    HasDerivAt (fun w : ℂ => explicitSolution σ (Function.update z i w))
      ((Complex.I * signValue (σ i) + psi σ i z) * explicitSolution σ z) (z i) := by
  simpa [pairLogDerivative_eq_psi] using hasDerivAt_explicitSolution_pair σ hz i

/-- The first derivative formula displayed immediately before (D.10). -/
theorem partial_explicitSolution {d : ℕ} (σ : Fin d → Sign) {z : Point d}
    (hz : CollisionFree z) (i : Fin d) :
    coordDeriv i (explicitSolution σ) z =
      (Complex.I * signValue (σ i) + psi σ i z) * explicitSolution σ z :=
  (hasDerivAt_explicitSolution σ hz i).deriv


/-- The positive inverse-square sum obtained by differentiating `psi`. -/
def psiDerivative {d : ℕ} (σ : Fin d → Sign) (i : Fin d) (z : Point d) : ℂ :=
  ∑ j ∈ Finset.univ.erase i, if σ j ≠ σ i then (z i - z j)⁻¹ ^ 2 else 0

theorem hasDerivAt_psi {d : ℕ} (σ : Fin d → Sign) {z : Point d}
    (hz : CollisionFree z) (i : Fin d) :
    HasDerivAt (fun w : ℂ => psi σ i (Function.update z i w))
      (psiDerivative σ i z) (z i) := by
  have h : HasDerivAt
      (fun w : ℂ => ∑ j ∈ Finset.univ.erase i,
        if σ j ≠ σ i then (Function.update z i w i - Function.update z i w j)⁻¹ else 0)
      (∑ j ∈ Finset.univ.erase i,
        if σ j ≠ σ i then -(z i - z j)⁻¹ ^ 2 else 0) (z i) := by
    apply HasDerivAt.sum
    intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    by_cases hs : σ j ≠ σ i
    · have hd := ((hasDerivAt_id (z i)).sub_const (z j)).inv (hz.sub_ne_zero (Ne.symm hji))
      convert hd using 1 <;> simp [hs, Function.update_of_ne hji, inv_pow, div_eq_mul_inv]
    · simpa [hs] using hasDerivAt_const (z i) (0 : ℂ)
  have hcoeff : -(∑ j ∈ Finset.univ.erase i,
      if σ j ≠ σ i then -(z i - z j)⁻¹ ^ 2 else 0) = psiDerivative σ i z := by
    rw [← Finset.sum_neg_distrib]
    unfold psiDerivative
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  have hh := h.neg
  rw [hcoeff] at hh
  exact hh

/-- Collision-freeness persists for all sufficiently small coordinate perturbations. -/
theorem eventually_collisionFree_update {d : ℕ} {z : Point d}
    (hz : CollisionFree z) (i : Fin d) :
    ∀ᶠ w in nhds (z i), CollisionFree (Function.update z i w) := by
  have hall : ∀ a b : Fin d, ∀ᶠ w in nhds (z i),
      Function.update z i w a = Function.update z i w b → a = b := by
    intro a b
    by_cases hab : a = b
    · exact Filter.Eventually.of_forall (fun _ _ => hab)
    · have hcont := ((hasDerivAt_update_coord z i a).sub
        (hasDerivAt_update_coord z i b)).continuousAt
      have hevent := hcont.eventually_ne (by simpa using hz.sub_ne_zero hab)
      filter_upwards [hevent] with w hw heq
      exact False.elim (hw (sub_eq_zero.mpr heq))
  filter_upwards [Filter.eventually_all.mpr (fun a => Filter.eventually_all.mpr (hall a))]
    with w hw
  exact hw

/-- The second genuine coordinate derivative formula preceding (D.10). -/
theorem secondPartial_explicitSolution {d : ℕ} (σ : Fin d → Sign) {z : Point d}
    (hz : CollisionFree z) (i : Fin d) :
    secondPartial i (explicitSolution σ) z =
      ((Complex.I * signValue (σ i) + psi σ i z) ^ 2 + psiDerivative σ i z) *
        explicitSolution σ z := by
  have hg := hasDerivAt_explicitSolution σ hz i
  have hp := (hasDerivAt_psi σ hz i).const_add (Complex.I * signValue (σ i))
  have hd := hp.mul hg
  have heq : (fun w => coordDeriv i (explicitSolution σ) (Function.update z i w)) =ᶠ[nhds (z i)]
      (fun w => (Complex.I * signValue (σ i) + psi σ i (Function.update z i w)) *
        explicitSolution σ (Function.update z i w)) := by
    filter_upwards [eventually_collisionFree_update hz i] with w hw
    exact partial_explicitSolution σ hw i
  have hder := (hd.congr_of_eventuallyEq heq).deriv
  change deriv (fun w => coordDeriv i (explicitSolution σ) (Function.update z i w)) (z i) = _
  rw [hder]
  simp only [Function.update_eq_self]
  ring


/-- A zero-one indicator for opposite signs, used only in finite rational identities. -/
def oppositeIndicator {d : ℕ} (σ : Fin d → Sign) (i j : Fin d) : ℂ :=
  if σ i ≠ σ j then 1 else 0

/-- Auxiliary Cauchy array, with diagonal value zero. Every analytic inverse
factor and every genuine operator denominator is separately proved nonzero.
The diagonal is used only to extend already zero summands to unrestricted sums. -/
def cauchy {d : ℕ} (z : Point d) (i j : Fin d) : ℂ := (z i - z j)⁻¹

@[simp] theorem oppositeIndicator_self {d : ℕ} (σ : Fin d → Sign) (i : Fin d) :
    oppositeIndicator σ i i = 0 := by simp [oppositeIndicator]

@[simp] theorem cauchy_self {d : ℕ} (z : Point d) (i : Fin d) : cauchy z i i = 0 := by
  simp [cauchy]

theorem cauchy_swap {d : ℕ} (z : Point d) (i j : Fin d) :
    cauchy z j i = -cauchy z i j := by
  simp only [cauchy, show z j - z i = -(z i - z j) by ring, inv_neg]

theorem psi_eq_sum {d : ℕ} (σ : Fin d → Sign) (i : Fin d) (z : Point d) :
    psi σ i z = - ∑ j, oppositeIndicator σ i j * cauchy z i j := by
  unfold psi
  have hh : (∑ j ∈ Finset.univ.erase i,
      if σ j ≠ σ i then (z i - z j)⁻¹ else 0) =
      ∑ j, if σ j ≠ σ i then (z i - z j)⁻¹ else 0 := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
    simp
  rw [hh]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : σ j = σ i
  · simp [oppositeIndicator, cauchy, h]
  · simp [oppositeIndicator, cauchy, h, Ne.symm h]

theorem psiDerivative_eq_sum {d : ℕ} (σ : Fin d → Sign) (i : Fin d) (z : Point d) :
    psiDerivative σ i z = ∑ j, oppositeIndicator σ i j * cauchy z i j ^ 2 := by
  unfold psiDerivative
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  simp only [ne_eq, not_true_eq_false, if_false, sub_zero]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : σ j = σ i
  · simp [oppositeIndicator, cauchy, h]
  · simp [oppositeIndicator, cauchy, h, Ne.symm h]

/-- The entire rational cancellation reduces to this three-index identity.
The two Kronecker-delta terms account explicitly for coincident indices. -/
theorem rational_triple_identity {d : ℕ} (σ : Fin d → Sign) {z : Point d}
    (hz : CollisionFree z) (i j k : Fin d) :
    (2 * oppositeIndicator σ i j * oppositeIndicator σ i k -
      oppositeIndicator σ i j - oppositeIndicator σ i k) * cauchy z i j * cauchy z i k +
      oppositeIndicator σ j k *
        (cauchy z i j * cauchy z j k + cauchy z i k * cauchy z k j) =
      -(if j = i then oppositeIndicator σ i k * cauchy z i k ^ 2 else 0) -
      (if k = i then oppositeIndicator σ i j * cauchy z i j ^ 2 else 0) := by
  by_cases hji : j = i
  · subst j
    simp only [oppositeIndicator_self, cauchy_self, mul_zero, zero_mul, sub_self,
      sub_zero, zero_sub, zero_add, if_true]
    rw [cauchy_swap z i k]
    by_cases hki : k = i
    · subst k; simp
    · simp only [hki, if_false, sub_zero]; ring
  by_cases hki : k = i
  · subst k
    simp only [oppositeIndicator_self, cauchy_self, mul_zero, zero_mul, sub_zero,
      zero_sub, add_zero, hji, if_false, if_true, neg_zero]
    have hsym : oppositeIndicator σ j i = oppositeIndicator σ i j := by
      simp [oppositeIndicator, ne_comm]
    rw [hsym, cauchy_swap z i j]
    ring
  by_cases hkj : k = j
  · subst k
    have ha : oppositeIndicator σ i j ^ 2 = oppositeIndicator σ i j := by
      unfold oppositeIndicator
      split <;> norm_num
    simp only [oppositeIndicator_self, cauchy_self, mul_zero, zero_mul, add_zero,
      hji, if_false, neg_zero, sub_zero]
    calc
      _ = 2 * (oppositeIndicator σ i j ^ 2 - oppositeIndicator σ i j) *
        cauchy z i j ^ 2 := by ring
      _ = 0 := by rw [ha]; ring
  simp only [hji, hki, if_false, neg_zero, sub_zero]
  have hij := hz.sub_ne_zero (Ne.symm hji)
  have hik := hz.sub_ne_zero (Ne.symm hki)
  have hjk := hz.sub_ne_zero (Ne.symm hkj)
  have hkj' := hz.sub_ne_zero hkj
  unfold oppositeIndicator cauchy
  cases hsi : σ i <;> cases hsj : σ j <;> cases hsk : σ k <;>
    simp only [Bool.false_eq_true, Bool.true_eq_false, ne_eq, not_true_eq_false,
      not_false_eq_true, if_true, if_false] <;>
    field_simp <;> ring


/-- Rational cancellation in (D.10), uniformly in the dimension and sign pattern. -/
theorem rational_cancellation {d : ℕ} (σ : Fin d → Sign) {z : Point d}
    (hz : CollisionFree z) (i : Fin d) :
    psiDerivative σ i z + psi σ i z ^ 2 +
      ∑ j, (psi σ i z - psi σ j z) * cauchy z i j = 0 := by
  classical
  let A := oppositeIndicator σ
  let q := cauchy z
  let B : ℂ := ∑ j, A i j * q i j
  let C : ℂ := ∑ j, q i j
  let D : ℂ := ∑ j, ∑ k, A j k * (q i j * q j k)
  let E : ℂ := ∑ j, A i j * q i j ^ 2
  have hsym : ∀ j k, A j k = A k j := by
    intro j k
    simp [A, oppositeIndicator, ne_comm]
  have hswap : (∑ j, ∑ k, A j k * (q i k * q k j)) = D := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [hsym k j]
  have hsum : (∑ j, ∑ k,
      ((2 * A i j * A i k - A i j - A i k) * q i j * q i k +
        A j k * (q i j * q j k + q i k * q k j))) = -2 * E := by
    calc
      _ = ∑ j, ∑ k,
          (-(if j = i then A i k * q i k ^ 2 else 0) -
            (if k = i then A i j * q i j ^ 2 else 0)) := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        exact rational_triple_identity σ hz i j k
      _ = -2 * E := by
        simp [Finset.sum_sub_distrib, Finset.sum_neg_distrib, E]
        ring
  have hexpand : (∑ j, ∑ k,
      ((2 * A i j * A i k - A i j - A i k) * q i j * q i k +
        A j k * (q i j * q j k + q i k * q k j))) =
      2 * B * B - B * C - C * B + D + D := by
    nth_rw 2 [← hswap]
    dsimp only [B, C, D]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    repeat' first | rw [← Finset.sum_add_distrib] | rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    repeat' first | rw [← Finset.sum_add_distrib] | rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hexpand] at hsum
  have hinteract : (∑ j, (psi σ i z - psi σ j z) * q i j) = -B * C + D := by
    calc
      _ = ∑ j, ((-B) * q i j + ∑ k, A j k * (q i j * q j k)) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [psi_eq_sum, psi_eq_sum]
        change ((-B) - (-(∑ k, A j k * q j k))) * q i j = _
        rw [sub_neg_eq_add, add_mul, Finset.sum_mul]
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = -B * C + D := by
        dsimp only [C, D]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  change psiDerivative σ i z + psi σ i z ^ 2 +
      (∑ j, (psi σ i z - psi σ j z) * q i j) = 0
  rw [hinteract, psi_eq_sum, psiDerivative_eq_sum]
  change E + (-B) ^ 2 + (-B * C + D) = 0
  linear_combination hsum / 2

theorem signValue_sub {d : ℕ} (σ : Fin d → Sign) (i j : Fin d) :
    signValue (σ i) - signValue (σ j) =
      2 * signValue (σ i) * oppositeIndicator σ i j := by
  cases hi : σ i <;> cases hj : σ j <;> norm_num [signValue, oppositeIndicator, hi, hj]

/-- Cancellation of the exponential terms in (D.10). -/
theorem exponential_cancellation {d : ℕ} (σ : Fin d → Sign) (z : Point d) (i : Fin d) :
    2 * Complex.I * signValue (σ i) * psi σ i z +
      ∑ j, (Complex.I * (signValue (σ i) - signValue (σ j))) * cauchy z i j = 0 := by
  rw [psi_eq_sum, mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
  simp_rw [signValue_sub]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro j _
  ring

/-- Each of the 2^d branch-free explicit functions solves the genuine reduced CMS equations. -/
theorem explicitSolution_isReducedSolution {d : ℕ} (σ : Fin d → Sign) :
    IsReducedSolution (explicitSolution σ) := by
  intro z hz i
  unfold reducedOperator
  rw [secondPartial_explicitSolution σ hz i]
  simp_rw [partial_explicitSolution σ hz]
  have herase : (∑ j ∈ Finset.univ.erase i,
      ((Complex.I * signValue (σ i) + psi σ i z) * explicitSolution σ z -
        (Complex.I * signValue (σ j) + psi σ j z) * explicitSolution σ z) /
          (z i - z j)) =
      (∑ j, ((Complex.I * signValue (σ i) + psi σ i z) -
        (Complex.I * signValue (σ j) + psi σ j z)) * cauchy z i j) *
          explicitSolution σ z := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
    simp only [sub_self, zero_div, sub_zero]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    simp only [cauchy, div_eq_mul_inv]
    ring
  rw [herase]
  have hr := rational_cancellation σ hz i
  have he := exponential_cancellation σ z i
  have hs : (Complex.I * signValue (σ i)) ^ 2 + 1 = 0 := by
    rw [mul_pow, Complex.I_sq, signValue_sq]
    ring
  have hsum : (∑ j, (Complex.I * signValue (σ i) + psi σ i z -
      (Complex.I * signValue (σ j) + psi σ j z)) * cauchy z i j) =
      (∑ j, (Complex.I * (signValue (σ i) - signValue (σ j))) * cauchy z i j) +
        ∑ j, (psi σ i z - psi σ j z) * cauchy z i j := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum]
  linear_combination (hr + he + hs) * explicitSolution σ z

end BourgadeHuang.CMS
