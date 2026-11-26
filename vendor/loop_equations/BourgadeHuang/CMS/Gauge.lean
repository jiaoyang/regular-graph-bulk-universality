import BourgadeHuang.CMS.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Order.Filter.Finite
import Mathlib.Algebra.BigOperators.Field

/-! Appendix D.1: mixed Vandermonde gauge and exact rational cancellation.
All derivatives in this file are ordinary complex derivatives of actual functions.
No logarithm or branch of a complex power is used. -/
noncomputable section
open scoped BigOperators Topology
namespace BourgadeHuang.CMS

/-- The mixed Vandermonde in Appendix D.1. -/
def mixedVandermonde {n m : ℕ} (t : Point n) (s : Point m) : ℂ :=
  ∏ i, ∏ a, (t i - s a)

def CrossDistinct {n m : ℕ} (t : Point n) (s : Point m) : Prop :=
  ∀ i a, t i ≠ s a

/-- The two-block noncollision assumptions are exactly the combined-coordinate
collision-free domain used by the reduced CMS operator. -/
theorem collisionFree_append {n m : ℕ} (t : Point n) (s : Point m) :
    CollisionFree (Fin.append t s) ↔
      Function.Injective t ∧ Function.Injective s ∧ CrossDistinct t s := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro i j hij
      have he : Fin.castAdd m i = Fin.castAdd m j := h (by simpa using hij)
      exact Fin.ext (congrArg (fun q : Fin (n + m) => q.val) he)
    · intro i j hij
      have he : Fin.natAdd n i = Fin.natAdd n j := h (by simpa using hij)
      have hv := congrArg Fin.val he
      apply Fin.ext
      change n + i.val = n + j.val at hv
      omega
    · intro i a hia
      have hv := congrArg Fin.val (h (by simpa using hia :
        Fin.append t s (Fin.castAdd m i) = Fin.append t s (Fin.natAdd n a)))
      change i.val = n + a.val at hv
      omega
  · rintro ⟨ht, hs, hc⟩ i j
    refine Fin.addCases ?_ ?_ i
    · intro i
      refine Fin.addCases ?_ ?_ j
      · intro j hij
        simpa only [Fin.append_left] using congrArg (Fin.castAdd m) (ht (by simpa using hij))
      · intro a hia
        exact (hc i a (by simpa using hia)).elim
    · intro a
      refine Fin.addCases ?_ ?_ j
      · intro i hai
        exact (hc i a (by simpa using hai.symm)).elim
      · intro b hab
        exact congrArg (Fin.natAdd n) (hs (by simpa using hab))

/-- The quantities called `A_i` and `B_a` in Appendix D.1. -/
def rowLog {n m : ℕ} (t : Point n) (s : Point m) (i : Fin n) : ℂ :=
  ∑ a, (t i - s a)⁻¹

def colLog {n m : ℕ} (t : Point n) (s : Point m) (a : Fin m) : ℂ :=
  ∑ i, (s a - t i)⁻¹

theorem mixedVandermonde_ne_zero {n m : ℕ} {t : Point n} {s : Point m}
    (h : CrossDistinct t s) : mixedVandermonde t s ≠ 0 := by
  simp only [mixedVandermonde, Finset.prod_ne_zero_iff]
  exact fun i _ a _ => sub_ne_zero.mpr (h i a)

/-- First derivative in a numerator coordinate of the actual finite product. -/
theorem hasDerivAt_mixedVandermonde_left {n m : ℕ} (t : Point n) (s : Point m)
    (i : Fin n) (h : CrossDistinct t s) :
    HasDerivAt (fun u : ℂ => mixedVandermonde (Function.update t i u) s)
      (rowLog t s i * mixedVandermonde t s) (t i) := by
  have hrow : ∀ j : Fin n,
      HasDerivAt (fun u : ℂ => ∏ a, (Function.update t i u j - s a))
        ((if j = i then rowLog t s i else 0) * ∏ a, (t j - s a)) (t i) := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa [rowLog] using
        hasDerivAt_finset_prod_log Finset.univ (fun a u => u - s a)
          (fun a => (t i - s a)⁻¹) (t i) (by
            intro a _
            convert (hasDerivAt_id (t i)).sub_const (s a) using 1
            simp [sub_ne_zero.mpr (h i a)])
    · simpa [hji, Function.update_of_ne hji] using
        hasDerivAt_const (t i) (∏ a, (t j - s a))
  have hp := hasDerivAt_finset_prod_log Finset.univ
    (fun j u => ∏ a, (Function.update t i u j - s a))
    (fun j => if j = i then rowLog t s i else 0) (t i) (by
      intro j _
      simpa using hrow j)
  simpa [mixedVandermonde] using hp

/-- First derivative in a denominator coordinate, with the sign in (D.2). -/
theorem hasDerivAt_mixedVandermonde_right {n m : ℕ} (t : Point n) (s : Point m)
    (a : Fin m) (h : CrossDistinct t s) :
    HasDerivAt (fun u : ℂ => mixedVandermonde t (Function.update s a u))
      (colLog t s a * mixedVandermonde t s) (s a) := by
  have hcol : ∀ b : Fin m,
      HasDerivAt (fun u : ℂ => ∏ i, (t i - Function.update s a u b))
        ((if b = a then colLog t s a else 0) * ∏ i, (t i - s b)) (s a) := by
    intro b
    by_cases hba : b = a
    · subst b
      simpa [colLog] using
        hasDerivAt_finset_prod_log Finset.univ (fun i u => t i - u)
          (fun i => (s a - t i)⁻¹) (s a) (by
            intro i _
            convert (hasDerivAt_const (s a) (t i)).sub (hasDerivAt_id (s a)) using 1
            have hi : s a - t i ≠ 0 := sub_ne_zero.mpr (Ne.symm (h i a))
            field_simp [hi]
            <;> ring)
    · simpa [hba, Function.update_of_ne hba] using
        hasDerivAt_const (s a) (∏ i, (t i - s b))
  have hp := hasDerivAt_finset_prod_log Finset.univ
    (fun b u => ∏ i, (t i - Function.update s a u b))
    (fun b => if b = a then colLog t s a else 0) (s a) (by
      intro b _
      simpa using hcol b)
  have hp' : HasDerivAt
      (fun u : ℂ => ∏ b, ∏ i, (t i - Function.update s a u b))
      (colLog t s a * ∏ b, ∏ i, (t i - s b)) (s a) := by
    simpa using hp
  convert hp' using 1
  · funext u
    exact Finset.prod_comm
  · unfold mixedVandermonde
    rw [Finset.prod_comm]

/-- The matrix identity underlying the zero-order gauge cancellation, valid
for arbitrary finite block sizes, including empty blocks. -/
theorem matrix_potential_cancellation {n m : ℕ} (c : Fin n → Fin m → ℂ)
    (i : Fin n) :
    -(∑ a, c i a ^ 2) + (∑ a, c i a) ^ 2 -
        (∑ j ∈ Finset.univ.erase i, ∑ a, c i a * c j a) -
        (∑ a, c i a * ((∑ b, c i b) - ∑ j, c j a)) = 0 := by
  have hdiag :
      (∑ a, c i a * ∑ j, c j a) =
        (∑ a, c i a ^ 2) + ∑ j ∈ Finset.univ.erase i, ∑ a, c i a * c j a := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm, ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp only [pow_two]
    ring
  have hsq : (∑ a, c i a * ∑ b, c i b) = (∑ a, c i a) ^ 2 := by
    rw [← Finset.sum_mul]
    ring
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [hdiag, hsq]
  ring

theorem inverse_difference_quotient (x y u : ℂ)
    (hxu : x - u ≠ 0) (hyu : y - u ≠ 0) (hxy : x - y ≠ 0) :
    ((x - u)⁻¹ - (y - u)⁻¹) / (x - y) = -((x - u)⁻¹ * (y - u)⁻¹) := by
  field_simp [hxu, hyu, hxy]
  <;> ring

/-- Exact zero-order cancellation for the numerator equation in D.1. -/
theorem gauge_potential_left {n m : ℕ} (t : Point n) (s : Point m)
    (i : Fin n) (hcross : CrossDistinct t s) (ht : Function.Injective t) :
    -(∑ a, ((t i - s a)⁻¹) ^ 2) + (rowLog t s i) ^ 2 +
        (∑ j ∈ Finset.univ.erase i, (rowLog t s i - rowLog t s j) / (t i - t j)) -
        (∑ a, (rowLog t s i + colLog t s a) / (t i - s a)) = 0 := by
  have hsame (j : Fin n) (hj : j ∈ Finset.univ.erase i) :
      (rowLog t s i - rowLog t s j) / (t i - t j) =
        -(∑ a, (t i - s a)⁻¹ * (t j - s a)⁻¹) := by
    rw [rowLog, rowLog, ← Finset.sum_sub_distrib, Finset.sum_div]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a _
    exact inverse_difference_quotient _ _ _ (sub_ne_zero.mpr (hcross i a))
      (sub_ne_zero.mpr (hcross j a))
      (sub_ne_zero.mpr (fun hij => (Finset.mem_erase.mp hj).1 (ht hij).symm))
  have hcol (a : Fin m) : colLog t s a = -(∑ j, (t j - s a)⁻¹) := by
    unfold colLog
    calc
      _ = ∑ j, -((t j - s a)⁻¹) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [show s a - t j = -(t j - s a) by ring, inv_neg]
      _ = _ := Finset.sum_neg_distrib
  have hsameSum :
      (∑ j ∈ Finset.univ.erase i, (rowLog t s i - rowLog t s j) / (t i - t j)) =
      -(∑ j ∈ Finset.univ.erase i, ∑ a, (t i - s a)⁻¹ * (t j - s a)⁻¹) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl hsame
  rw [hsameSum]
  simp_rw [hcol, div_eq_mul_inv]
  simpa [rowLog, sub_eq_add_neg, mul_comm] using
    matrix_potential_cancellation (fun j a => (t j - s a)⁻¹) i

/-- The denominator potential is the same cancellation after exchanging blocks. -/
theorem gauge_potential_right {n m : ℕ} (t : Point n) (s : Point m)
    (a : Fin m) (hcross : CrossDistinct t s) (hs : Function.Injective s) :
    -(∑ i, ((s a - t i)⁻¹) ^ 2) + (colLog t s a) ^ 2 +
        (∑ b ∈ Finset.univ.erase a, (colLog t s a - colLog t s b) / (s a - s b)) -
        (∑ i, (colLog t s a + rowLog t s i) / (s a - t i)) = 0 := by
  simpa [rowLog, colLog] using
    gauge_potential_left s t a (fun a i => Ne.symm (hcross i a)) hs

/-- Coordinate derivatives in the two-block notation of Appendix D.1. -/
def leftPartial {n m : ℕ} (i : Fin n) (F : Point n → Point m → ℂ)
    (t : Point n) (s : Point m) : ℂ :=
  deriv (fun u : ℂ => F (Function.update t i u) s) (t i)

def rightPartial {n m : ℕ} (a : Fin m) (F : Point n → Point m → ℂ)
    (t : Point n) (s : Point m) : ℂ :=
  deriv (fun u : ℂ => F t (Function.update s a u)) (s a)

/-- Genuine first-order product rule in (D.1). -/
theorem leftPartial_gauge {n m : ℕ} (t : Point n) (s : Point m)
    (i : Fin n) (G : Point n → Point m → ℂ) (hc : CrossDistinct t s)
    (hg : DifferentiableAt ℂ (fun u => G (Function.update t i u) s) (t i)) :
    leftPartial i (fun t s => mixedVandermonde t s * G t s) t s =
      mixedVandermonde t s * (leftPartial i G t s + rowLog t s i * G t s) := by
  have h := ((hasDerivAt_mixedVandermonde_left t s i hc).mul hg.hasDerivAt).deriv
  simp only [Function.update_eq_self] at h
  rw [leftPartial, h]
  unfold leftPartial
  ring

/-- Genuine first-order product rule in (D.2). -/
theorem rightPartial_gauge {n m : ℕ} (t : Point n) (s : Point m)
    (a : Fin m) (G : Point n → Point m → ℂ) (hc : CrossDistinct t s)
    (hg : DifferentiableAt ℂ (fun u => G t (Function.update s a u)) (s a)) :
    rightPartial a (fun t s => mixedVandermonde t s * G t s) t s =
      mixedVandermonde t s * (rightPartial a G t s + colLog t s a * G t s) := by
  have h := ((hasDerivAt_mixedVandermonde_right t s a hc).mul hg.hasDerivAt).deriv
  simp only [Function.update_eq_self] at h
  rw [rightPartial, h]
  unfold rightPartial
  ring

/-- Derivative of the rational logarithmic derivative `A_i`. -/
theorem hasDerivAt_rowLog_left {n m : ℕ} (t : Point n) (s : Point m)
    (i : Fin n) (hc : CrossDistinct t s) :
    HasDerivAt (fun u : ℂ => rowLog (Function.update t i u) s i)
      (-(∑ a, ((t i - s a)⁻¹)^2)) (t i) := by
  have hh : ∀ a : Fin m,
      HasDerivAt (fun u : ℂ => (u - s a)⁻¹)
        (-((t i - s a)⁻¹)^2) (t i) := by
    intro a
    convert ((hasDerivAt_id (t i)).sub_const (s a)).inv
      (sub_ne_zero.mpr (hc i a)) using 1 <;> simp [div_eq_mul_inv, inv_pow]
  simpa [rowLog, Finset.sum_neg_distrib] using
    HasDerivAt.sum (u := Finset.univ) (fun a _ => hh a)

/-- Cross collisions remain absent in a neighborhood along a coordinate line. -/
theorem eventually_crossDistinct_left {n m : ℕ} (t : Point n) (s : Point m)
    (i : Fin n) (hc : CrossDistinct t s) :
    ∀ᶠ u in 𝓝 (t i), CrossDistinct (Function.update t i u) s := by
  have h : ∀ᶠ u in 𝓝 (t i), ∀ a : Fin m, u ≠ s a :=
    Filter.eventually_all.mpr (fun a => eventually_ne_nhds (hc i a))
  filter_upwards [h] with u hu
  intro j a
  by_cases hji : j = i
  · subst j
    simpa using hu a
  · simpa [Function.update_of_ne hji] using hc j a

/-- Second-order product rule (D.1). All regularity hypotheses are stated for
actual complex coordinate slices near the evaluation point. -/
theorem leftSecond_gauge {n m : ℕ} (t : Point n) (s : Point m)
    (i : Fin n) (G : Point n → Point m → ℂ) (hc : CrossDistinct t s)
    (hg : ∀ᶠ u in 𝓝 (t i),
      DifferentiableAt ℂ (fun v => G (Function.update t i v) s) u)
    (hg2 : DifferentiableAt ℂ
      (fun u => leftPartial i G (Function.update t i u) s) (t i)) :
    leftPartial i (leftPartial i (fun t s => mixedVandermonde t s * G t s)) t s =
      mixedVandermonde t s * (leftPartial i (leftPartial i G) t s +
        2 * rowLog t s i * leftPartial i G t s +
        (-(∑ a, ((t i - s a)⁻¹)^2) + (rowLog t s i)^2) * G t s) := by
  have heq : (fun u => leftPartial i (fun t s => mixedVandermonde t s * G t s)
      (Function.update t i u) s) =ᶠ[𝓝 (t i)]
      (fun u => mixedVandermonde (Function.update t i u) s *
        (leftPartial i G (Function.update t i u) s +
          rowLog (Function.update t i u) s i * G (Function.update t i u) s)) := by
    filter_upwards [eventually_crossDistinct_left t s i hc, hg] with u hu hgu
    apply leftPartial_gauge _ _ _ _ hu
    simpa [Function.update_idem] using hgu
  have hdiff := (hasDerivAt_mixedVandermonde_left t s i hc).mul
    (hg2.hasDerivAt.add ((hasDerivAt_rowLog_left t s i hc).mul
      hg.self_of_nhds.hasDerivAt))
  have h := (hdiff.congr_of_eventuallyEq heq).deriv
  simp only [Function.update_eq_self] at h
  change deriv _ (t i) = _
  rw [h]
  unfold leftPartial
  ring

/-- The denominator analogue of the rational derivative formula. -/
theorem hasDerivAt_colLog_right {n m : ℕ} (t : Point n) (s : Point m)
    (a : Fin m) (hc : CrossDistinct t s) :
    HasDerivAt (fun u : ℂ => colLog t (Function.update s a u) a)
      (-(∑ i, ((s a - t i)⁻¹)^2)) (s a) := by
  simpa [rowLog, colLog] using
    hasDerivAt_rowLog_left s t a (fun a i => Ne.symm (hc i a))

theorem eventually_crossDistinct_right {n m : ℕ} (t : Point n) (s : Point m)
    (a : Fin m) (hc : CrossDistinct t s) :
    ∀ᶠ u in 𝓝 (s a), CrossDistinct t (Function.update s a u) := by
  filter_upwards [eventually_crossDistinct_left s t a
    (fun a i => Ne.symm (hc i a))] with u hu
  exact fun i a => Ne.symm (hu a i)

/-- The genuine second-order product rule (D.2). -/
theorem rightSecond_gauge {n m : ℕ} (t : Point n) (s : Point m)
    (a : Fin m) (G : Point n → Point m → ℂ) (hc : CrossDistinct t s)
    (hg : ∀ᶠ u in 𝓝 (s a),
      DifferentiableAt ℂ (fun v => G t (Function.update s a v)) u)
    (hg2 : DifferentiableAt ℂ
      (fun u => rightPartial a G t (Function.update s a u)) (s a)) :
    rightPartial a (rightPartial a (fun t s => mixedVandermonde t s * G t s)) t s =
      mixedVandermonde t s * (rightPartial a (rightPartial a G) t s +
        2 * colLog t s a * rightPartial a G t s +
        (-(∑ i, ((s a - t i)⁻¹)^2) + (colLog t s a)^2) * G t s) := by
  have heq : (fun u => rightPartial a (fun t s => mixedVandermonde t s * G t s)
      t (Function.update s a u)) =ᶠ[𝓝 (s a)]
      (fun u => mixedVandermonde t (Function.update s a u) *
        (rightPartial a G t (Function.update s a u) +
          colLog t (Function.update s a u) a * G t (Function.update s a u))) := by
    filter_upwards [eventually_crossDistinct_right t s a hc, hg] with u hu hgu
    apply rightPartial_gauge _ _ _ _ hu
    simpa [Function.update_idem] using hgu
  have hdiff := (hasDerivAt_mixedVandermonde_right t s a hc).mul
    (hg2.hasDerivAt.add ((hasDerivAt_colLog_right t s a hc).mul
      hg.self_of_nhds.hasDerivAt))
  have h := (hdiff.congr_of_eventuallyEq heq).deriv
  simp only [Function.update_eq_self] at h
  change deriv _ (s a) = _
  rw [h]
  unfold rightPartial
  ring

/-- The two original operators at beta=2, with the mixed derivative sum sign. -/
def leftOriginal {n m : ℕ} (i : Fin n) (F : Point n → Point m → ℂ)
    (t : Point n) (s : Point m) : ℂ :=
  leftPartial i (leftPartial i F) t s + F t s +
    (∑ j ∈ Finset.univ.erase i, (leftPartial i F t s - leftPartial j F t s) / (t i - t j)) -
    (∑ a, (leftPartial i F t s + rightPartial a F t s) / (t i - s a))

def rightOriginal {n m : ℕ} (a : Fin m) (F : Point n → Point m → ℂ)
    (t : Point n) (s : Point m) : ℂ :=
  rightPartial a (rightPartial a F) t s + F t s +
    (∑ b ∈ Finset.univ.erase a, (rightPartial a F t s - rightPartial b F t s) / (s a - s b)) -
    (∑ i, (rightPartial a F t s + leftPartial i F t s) / (s a - t i))

/-- The reduced operators (D.3)-(D.4), in the two-block notation. -/
def leftReduced {n m : ℕ} (i : Fin n) (G : Point n → Point m → ℂ)
    (t : Point n) (s : Point m) : ℂ :=
  leftPartial i (leftPartial i G) t s + G t s +
    (∑ j ∈ Finset.univ.erase i, (leftPartial i G t s - leftPartial j G t s) / (t i - t j)) +
    (∑ a, (leftPartial i G t s - rightPartial a G t s) / (t i - s a))

def rightReduced {n m : ℕ} (a : Fin m) (G : Point n → Point m → ℂ)
    (t : Point n) (s : Point m) : ℂ :=
  rightPartial a (rightPartial a G) t s + G t s +
    (∑ b ∈ Finset.univ.erase a, (rightPartial a G t s - rightPartial b G t s) / (s a - s b)) +
    (∑ i, (rightPartial a G t s - leftPartial i G t s) / (s a - t i))

/-- First-order mixed-interaction cancellation. -/
theorem mixed_first_order_cancellation {m : ℕ} (c : Fin m → ℂ)
    (v : ℂ) (w : Fin m → ℂ) :
    2 * (∑ a, c a) * v - (∑ a, (v + w a) * c a) =
      ∑ a, (v - w a) * c a := by
  simp_rw [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum]
  ring


/-- Algebraic assembly helper. It is deliberately separate from the genuine
analytic conjugation theorem below. -/
theorem gauge_left_algebra {n m : ℕ} (t : Point n) (s : Point m)
    (i : Fin n) (P g q : ℂ) (v : Fin n → ℂ) (w : Fin m → ℂ)
    (hc : CrossDistinct t s) (ht : Function.Injective t) :
    P * (q + 2 * rowLog t s i * v i +
      (-(∑ a, ((t i - s a)⁻¹)^2) + (rowLog t s i)^2) * g) + P * g +
      (∑ j ∈ Finset.univ.erase i,
        (P * (v i + rowLog t s i * g) - P * (v j + rowLog t s j * g)) / (t i - t j)) -
      (∑ a, (P * (v i + rowLog t s i * g) + P * (w a + colLog t s a * g)) / (t i - s a)) =
    P * (q + g +
      (∑ j ∈ Finset.univ.erase i, (v i - v j) / (t i - t j)) +
      (∑ a, (v i - w a) / (t i - s a))) := by
  have hsame :
      (∑ j ∈ Finset.univ.erase i,
        (P * (v i + rowLog t s i * g) - P * (v j + rowLog t s j * g)) / (t i - t j)) =
      P * (∑ j ∈ Finset.univ.erase i, (v i - v j) / (t i - t j)) +
      P * g * (∑ j ∈ Finset.univ.erase i, (rowLog t s i - rowLog t s j) / (t i - t j)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [div_eq_mul_inv]
    ring
  have hmixed :
      (∑ a, (P * (v i + rowLog t s i * g) + P * (w a + colLog t s a * g)) / (t i - s a)) =
      P * (∑ a, (v i + w a) / (t i - s a)) +
      P * g * (∑ a, (rowLog t s i + colLog t s a) / (t i - s a)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    simp only [div_eq_mul_inv]
    ring
  have hfirst :
      2 * rowLog t s i * v i - (∑ a, (v i + w a) / (t i - s a)) =
        ∑ a, (v i - w a) / (t i - s a) := by
    simpa [rowLog, div_eq_mul_inv] using
      mixed_first_order_cancellation (fun a => (t i - s a)⁻¹) (v i) w
  have hzero := gauge_potential_left t s i hc ht
  rw [hsame, hmixed]
  calc
    _ = P * (q + g + (∑ j ∈ Finset.univ.erase i, (v i - v j) / (t i - t j)) +
        (2 * rowLog t s i * v i - (∑ a, (v i + w a) / (t i - s a)))) +
        P * g * (-(∑ a, ((t i - s a)⁻¹)^2) + (rowLog t s i)^2 +
          (∑ j ∈ Finset.univ.erase i, (rowLog t s i - rowLog t s j) / (t i - t j)) -
          (∑ a, (rowLog t s i + colLog t s a) / (t i - s a))) := by ring
    _ = _ := by rw [hfirst, hzero]; ring

/-- Exact analytic gauge identity for a numerator equation of Theorem D.1.
Only coordinate-wise differentiability needed for the displayed operator is
assumed; no PDE, cancellation, or uniqueness statement is an input. -/
theorem leftOriginal_gauge {n m : ℕ} (t : Point n) (s : Point m)
    (i : Fin n) (G : Point n → Point m → ℂ)
    (hc : CrossDistinct t s) (ht : Function.Injective t)
    (hgl : ∀ j, ∀ᶠ u in 𝓝 (t j),
      DifferentiableAt ℂ (fun v => G (Function.update t j v) s) u)
    (hgr : ∀ a, DifferentiableAt ℂ (fun u => G t (Function.update s a u)) (s a))
    (hgl2 : DifferentiableAt ℂ
      (fun u => leftPartial i G (Function.update t i u) s) (t i)) :
    leftOriginal i (fun t s => mixedVandermonde t s * G t s) t s =
      mixedVandermonde t s * leftReduced i G t s := by
  have hl (j : Fin n) := leftPartial_gauge t s j G hc (hgl j).self_of_nhds
  have hr (a : Fin m) := rightPartial_gauge t s a G hc (hgr a)
  unfold leftOriginal leftReduced
  rw [leftSecond_gauge t s i G hc (hgl i) hgl2]
  simp_rw [hl, hr]
  exact gauge_left_algebra t s i (mixedVandermonde t s) (G t s)
    (leftPartial i (leftPartial i G) t s)
    (fun j => leftPartial j G t s) (fun a => rightPartial a G t s) hc ht

/-- Exact analytic gauge identity for a denominator equation of Theorem D.1. -/
theorem rightOriginal_gauge {n m : ℕ} (t : Point n) (s : Point m)
    (a : Fin m) (G : Point n → Point m → ℂ)
    (hc : CrossDistinct t s) (hs : Function.Injective s)
    (hgl : ∀ i, DifferentiableAt ℂ (fun u => G (Function.update t i u) s) (t i))
    (hgr : ∀ b, ∀ᶠ u in 𝓝 (s b),
      DifferentiableAt ℂ (fun v => G t (Function.update s b v)) u)
    (hgr2 : DifferentiableAt ℂ
      (fun u => rightPartial a G t (Function.update s a u)) (s a)) :
    rightOriginal a (fun t s => mixedVandermonde t s * G t s) t s =
      mixedVandermonde t s * rightReduced a G t s := by
  have hl (i : Fin n) := leftPartial_gauge t s i G hc (hgl i)
  have hr (b : Fin m) := rightPartial_gauge t s b G hc (hgr b).self_of_nhds
  unfold rightOriginal rightReduced
  rw [rightSecond_gauge t s a G hc (hgr a) hgr2]
  simp_rw [hl, hr]
  simpa [rowLog, colLog] using
    gauge_left_algebra s t a (mixedVandermonde t s) (G t s)
      (rightPartial a (rightPartial a G) t s)
      (fun b => rightPartial b G t s) (fun i => leftPartial i G t s)
      (fun a i => Ne.symm (hc i a)) hs

/-- Theorem D.1 in the two-block notation (D.3)-(D.4), pointwise at a
collision-free point. Regularity assumptions are stated explicitly. -/
theorem gauge_system_iff {n m : ℕ} (t : Point n) (s : Point m)
    (G : Point n → Point m → ℂ)
    (hc : CrossDistinct t s) (ht : Function.Injective t) (hs : Function.Injective s)
    (hgl : ∀ i, ∀ᶠ u in 𝓝 (t i),
      DifferentiableAt ℂ (fun v => G (Function.update t i v) s) u)
    (hgr : ∀ a, ∀ᶠ u in 𝓝 (s a),
      DifferentiableAt ℂ (fun v => G t (Function.update s a v)) u)
    (hgl2 : ∀ i, DifferentiableAt ℂ
      (fun u => leftPartial i G (Function.update t i u) s) (t i))
    (hgr2 : ∀ a, DifferentiableAt ℂ
      (fun u => rightPartial a G t (Function.update s a u)) (s a)) :
    ((∀ i, leftOriginal i (fun t s => mixedVandermonde t s * G t s) t s = 0) ∧
     (∀ a, rightOriginal a (fun t s => mixedVandermonde t s * G t s) t s = 0)) ↔
    ((∀ i, leftReduced i G t s = 0) ∧ (∀ a, rightReduced a G t s = 0)) := by
  have hp := mixedVandermonde_ne_zero hc
  have hl (i : Fin n) := leftOriginal_gauge t s i G hc ht hgl
    (fun a => (hgr a).self_of_nhds) (hgl2 i)
  have hr (a : Fin m) := rightOriginal_gauge t s a G hc hs
    (fun i => (hgl i).self_of_nhds) hgr (hgr2 a)
  simp_rw [hl, hr]
  simp [hp]


end BourgadeHuang.CMS
