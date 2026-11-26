import BourgadeHuang.FactorialConvergence
import BourgadeHuang.CountingAtomicity
import Mathlib.Data.Fin.Tuple.Basic

/-!
# General-order factorial tensor observables

Inclusion-exclusion is performed on particle labels. The recursion thus remains
valid for configurations with repeated particle locations.
-/

noncomputable section
open scoped BigOperators Topology CompactlySupported
open MeasureTheory

namespace BourgadeHuang

/-- Merging a new tensor factor into one old tensor factor. -/
def mergeTensorFactor {q : ℕ} (f : Fin (q + 1) → ℝ →C_c ℝ) (j : Fin q) :
    Fin q → ℝ →C_c ℝ :=
  Function.update (fun k => f k.succ) j (f 0 * f j.succ)

/-- The factorial tensor polynomial is defined using only continuous linear statistics. -/
def tensorFactorialObservable : {q : ℕ} →
    (Fin q → ℝ →C_c ℝ) → LocalCountingMeasure → ℝ
  | 0, _, _ => 1
  | q + 1, f, ξ =>
      (∫ x, f 0 x ∂ξ.measure) * tensorFactorialObservable (fun j => f j.succ) ξ -
        ∑ j : Fin q, tensorFactorialObservable (mergeTensorFactor f j) ξ

/-- Every order of the factorial tensor polynomial is vague-continuous. -/
theorem continuous_tensorFactorialObservable {q : ℕ}
    (f : Fin q → ℝ →C_c ℝ) : Continuous (tensorFactorialObservable f) := by
  induction q with
  | zero => exact continuous_const
  | succ q ih =>
    exact ((continuous_linearStatistic (f 0)).mul (ih _)).sub
      (continuous_finset_sum _ fun j _ => ih (mergeTensorFactor f j))

private theorem prod_update_factor {q : ℕ} (f : ℝ → ℝ)
    (g : Fin q → ℝ → ℝ) (t : Fin q → ℝ) (j : Fin q) :
    (∏ k, Function.update g j (fun y => f y * g j y) k (t k)) =
      f (t j) * ∏ k, g k (t k) := by
  classical
  have heq : (fun k => Function.update g j (fun y => f y * g j y) k (t k)) =
      Function.update (fun k => g k (t k)) j (f (t j) * g j (t j)) := by
    funext k
    by_cases hk : k = j
    · subst k
      simp
    · simp [hk]
  rw [heq, Finset.prod_update_of_mem (Finset.mem_univ j)]
  rw [← Finset.mul_prod_erase Finset.univ (fun k => g k (t k)) (Finset.mem_univ j)]
  rw [Finset.sdiff_singleton_eq_erase]
  ring

private theorem sum_avoid_injective {α : Type*} [Fintype α] [DecidableEq α]
    {q : ℕ} (t : Fin q → α) (ht : Function.Injective t) (f : α → ℝ) :
    (∑ i, if i ∉ Set.range t then f i else 0) = (∑ i, f i) - ∑ j, f (t j) := by
  classical
  let s : Finset α := Finset.univ.image t
  have hs (i : α) : i ∈ s ↔ i ∈ Set.range t := by simp [s]
  have himage : (∑ i ∈ s, f i) = ∑ j, f (t j) := by
    exact Finset.sum_image (fun _ _ _ _ h => ht h)
  have hsplit := Finset.sum_sdiff (f := f) (Finset.subset_univ s)
  have hav : (∑ i, if i ∉ Set.range t then f i else 0) = ∑ i ∈ Finset.univ \ s, f i := by
    rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ s)]
    have hd : (∑ i, if i ∈ s then f i else 0) = ∑ i ∈ s, f i := by
      simp [Finset.sum_ite_mem]
    have hadd : (∑ i, if i ∉ Set.range t then f i else 0) + ∑ i ∈ s, f i = ∑ i, f i := by
      rw [← hd, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ s
      · simp [hi, (hs i).mp hi]
      · have hir : i ∉ Set.range t := mt (hs i).mpr hi
        simp [hi, hir]
    linarith
  rw [hav]
  linarith

/-- The exact recursive inclusion-exclusion formula for arbitrary tensor factors.
Its diagonal correction merges the first factor into each of the remaining factors. -/
theorem factorialStatistic_tensor_succ {N q : ℕ} (x : Fin N → ℝ)
    (f : Fin (q + 1) → ℝ → ℝ) :
    factorialStatistic x (fun y => ∏ j, f j (y j)) =
      (∑ i, f 0 (x i)) * factorialStatistic x (fun y : Fin q → ℝ =>
        ∏ j, f j.succ (y j)) -
      ∑ j : Fin q, factorialStatistic x (fun y : Fin q → ℝ =>
        ∏ k, Function.update (fun l => f l.succ) j
          (fun z => f 0 z * f j.succ z) k (y k)) := by
  classical
  unfold factorialStatistic
  let P (t : Fin q → Fin N) : ℝ := ∏ j, f j.succ (x (t j))
  have hstart :
      (∑ t : Fin (q + 1) → Fin N,
        if Function.Injective t then ∏ j, f j (x (t j)) else 0) =
      ∑ t : Fin q → Fin N, ∑ i : Fin N,
        if Function.Injective (Fin.cons i t) then f 0 (x i) * P t else 0 := by
    calc
      _ = ∑ it : Fin N × (Fin q → Fin N),
          if Function.Injective (Fin.cons it.1 it.2) then f 0 (x it.1) * P it.2 else 0 := by
        apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (q + 1) => Fin N)).symm
        intro t
        simp only [Equiv.symm_apply_apply, Fin.prod_univ_succ]
        simp [Fin.consEquiv, Fin.tail, P]
      _ = _ := by rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [hstart, Finset.mul_sum]
  rw [show (∑ j : Fin q, ∑ t : Fin q → Fin N,
      if Function.Injective t then
        ∏ k, Function.update (fun l => f l.succ) j
          (fun z => f 0 z * f j.succ z) k (x (t k)) else 0) =
      ∑ t : Fin q → Fin N, ∑ j : Fin q,
      if Function.Injective t then
        ∏ k, Function.update (fun l => f l.succ) j
          (fun z => f 0 z * f j.succ z) k (x (t k)) else 0 from Finset.sum_comm]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : Function.Injective t
  · simp only [Fin.cons_injective_iff, ht, and_true, if_true]
    calc
      _ = (∑ i, f 0 (x i) * P t) - ∑ j, f 0 (x (t j)) * P t :=
        sum_avoid_injective t ht (fun i => f 0 (x i) * P t)
      _ = _ := by
        rw [Finset.sum_mul]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        exact (prod_update_factor (f 0) (fun l => f l.succ) (fun k => x (t k)) j).symm

  · simp [Fin.cons_injective_iff, ht]

/-- Evaluation at a finite configuration agrees with the factorial statistic
at every order, including repeated particle locations. -/
theorem tensorFactorialObservable_finite {N q : ℕ} (x : Fin N → ℝ)
    (f : Fin q → ℝ →C_c ℝ) (ξ : LocalCountingMeasure)
    (hξ : ξ.measure = ∑ i, Measure.dirac (x i)) :
    tensorFactorialObservable f ξ =
      factorialStatistic x (fun y : Fin q → ℝ => ∏ j, f j (y j)) := by
  classical
  induction q with
  | zero => simp [tensorFactorialObservable, factorialStatistic, Function.injective_of_subsingleton]
  | succ q ih =>
    rw [tensorFactorialObservable, factorialStatistic_tensor_succ]
    rw [hξ, linearStatistic_finite_dirac, ih]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [ih]
    congr 1
    funext y
    apply Finset.prod_congr rfl
    intro k _
    by_cases hk : k = j
    · subst k
      simp [mergeTensorFactor]
    · simp [mergeTensorFactor, hk]

@[simp] theorem factorialStatistic_zero {N q : ℕ} (x : Fin N → ℝ) :
    factorialStatistic x (fun _ : Fin q → ℝ => 0) = 0 := by
  simp [factorialStatistic]

theorem factorialStatistic_add {N q : ℕ} (x : Fin N → ℝ)
    (φ ψ : (Fin q → ℝ) → ℝ) :
    factorialStatistic x (fun y => φ y + ψ y) =
      factorialStatistic x φ + factorialStatistic x ψ := by
  classical
  unfold factorialStatistic
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : Function.Injective t <;> simp [ht]

theorem factorialStatistic_sub {N q : ℕ} (x : Fin N → ℝ)
    (φ ψ : (Fin q → ℝ) → ℝ) :
    factorialStatistic x (fun y => φ y - ψ y) =
      factorialStatistic x φ - factorialStatistic x ψ := by
  classical
  unfold factorialStatistic
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : Function.Injective t <;> simp [ht]

theorem factorialStatistic_smul {N q : ℕ} (x : Fin N → ℝ)
    (c : ℝ) (φ : (Fin q → ℝ) → ℝ) :
    factorialStatistic x (fun y => c * φ y) = c * factorialStatistic x φ := by
  classical
  unfold factorialStatistic
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : Function.Injective t <;> simp [ht]

/-- Factorial statistics are linear in their test, at every particle number and order. -/
def factorialStatisticLinear {N q : ℕ} (x : Fin N → ℝ) :
    ((Fin q → ℝ) → ℝ) →ₗ[ℝ] ℝ where
  toFun := factorialStatistic x
  map_add' := factorialStatistic_add x
  map_smul' := factorialStatistic_smul x

private theorem mergeTensorFactor_support {q : ℕ} (f : Fin (q + 1) → ℝ →C_c ℝ)
    (K : Set ℝ) (hf : ∀ j, Function.support (f j) ⊆ K) (j k : Fin q) :
    Function.support (mergeTensorFactor f j k) ⊆ K := by
  intro x hx
  by_cases hk : k = j
  · subst k
    apply hf 0
    have hn : f 0 x * f j.succ x ≠ 0 := by simpa [mergeTensorFactor] using hx
    exact left_ne_zero_of_mul hn
  · apply hf k.succ
    simpa [mergeTensorFactor, hk] using hx

/-- The tensor observable depends only on the measure on the common support
of its tensor factors. -/
theorem tensorFactorialObservable_eq_of_restrict_eq {q : ℕ}
    (f : Fin q → ℝ →C_c ℝ) (K : Set ℝ) (hK : MeasurableSet K)
    (hf : ∀ j, Function.support (f j) ⊆ K)
    (ξ ζ : LocalCountingMeasure) (hmeasure : ξ.measure.restrict K = ζ.measure.restrict K) :
    tensorFactorialObservable f ξ = tensorFactorialObservable f ζ := by
  induction q with
  | zero => rfl
  | succ q ih =>
    have hlin : (∫ x, f 0 x ∂ξ.measure) = ∫ x, f 0 x ∂ζ.measure := by
      calc
        _ = ∫ x in K, f 0 x ∂ξ.measure := by
          rw [← integral_indicator hK, Set.indicator_eq_self.mpr (hf 0)]
        _ = ∫ x in K, f 0 x ∂ζ.measure := by rw [hmeasure]
        _ = _ := by rw [← integral_indicator hK, Set.indicator_eq_self.mpr (hf 0)]
    simp only [tensorFactorialObservable]
    rw [hlin, ih (fun j => f j.succ) (fun j => hf j.succ)]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    exact ih (mergeTensorFactor f j) (mergeTensorFactor_support f K hf j)

/-- A tensor of compactly supported tests has common support and size bounds. -/
theorem tensor_test_box_bound {q : ℕ} (f : Fin q → ℝ →C_c ℝ) :
    ∃ R C : ℝ, 0 < R ∧ 0 ≤ C ∧
      (∀ y : Fin q → ℝ, |∏ j, f j (y j)| ≤ C) ∧
      (∀ j, Function.support (f j) ⊆ Set.Icc (-R) R) := by
  classical
  choose R C hR hC hb hs using fun j => linear_test_box_bound (f j)
  let T : ℝ := 1 + ∑ j, R j
  have hT : 0 < T := by
    have : 0 ≤ ∑ j, R j := Finset.sum_nonneg fun j _ => (hR j).le
    dsimp [T]
    linarith
  refine ⟨T, ∏ j, C j, hT, Finset.prod_nonneg (fun j _ => hC j), ?_, ?_⟩
  · intro y
    rw [Finset.abs_prod]
    exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun j _ => hb j (y j))
  · intro j x hx
    have hj : R j ≤ T := by
      have h := Finset.single_le_sum (fun j _ => (hR j).le) (Finset.mem_univ j)
      dsimp [T]
      linarith
    have h := hs j hx
    exact ⟨by linarith [h.1], h.2.trans hj⟩

theorem tensor_test_support {q : ℕ} (f : Fin q → ℝ →C_c ℝ)
    (K : Set ℝ) (hf : ∀ j, Function.support (f j) ⊆ K)
    (y : Fin q → ℝ) (hy : ¬ ∀ j, y j ∈ K) :
    (∏ j, f j (y j)) = 0 := by
  classical
  obtain ⟨j, hj⟩ := not_forall.mp hy
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  by_contra hn
  exact hj (hf j (Function.mem_support.mpr hn))

/-- On a simple counting measure, the continuous tensor polynomial is exactly
its factorial integral over distinct locations. -/
theorem tensorFactorialObservable_eq_factorial_integral {q : ℕ}
    (f : Fin q → ℝ →C_c ℝ) (ξ : LocalCountingMeasure)
    (hξ : ∀ x, ξ.measure {x} ≤ 1) :
    tensorFactorialObservable f ξ =
      ∫ y : Fin q → ℝ, if Function.Injective y then ∏ j, f j (y j) else 0
        ∂Measure.pi (fun _ : Fin q => ξ.measure) := by
  obtain ⟨R, _, _, _, _, hs⟩ := tensor_test_box_bound f
  obtain ⟨N, x, _, _, hμ, hint⟩ :=
    ξ.factorial_integral_eq_particle_list hξ (K := Set.Icc (-R) R) isCompact_Icc
  rw [hint q _ (tensor_test_support f _ hs)]
  let ζ := ξ.restrictCompact (Set.Icc (-R) R) isCompact_Icc
  rw [tensorFactorialObservable_eq_of_restrict_eq f _ measurableSet_Icc hs ξ ζ (by
    simp [ζ, Measure.restrict_restrict]), tensorFactorialObservable_finite x f ζ hμ]

/-- The target factorial expectation of any tensor test is the expectation of a
continuous polynomial in compactly supported linear statistics. -/
theorem target_factorialExpectation_tensor (target : TargetProcess) {q : ℕ}
    (f : Fin q → ℝ →C_c ℝ) :
    target.factorialExpectation q (fun y => ∏ j, f j (y j)) =
      ∫ ξ, tensorFactorialObservable f ξ ∂target.law := by
  apply integral_congr_ae
  filter_upwards [target.simple] with ξ hξ
  exact (tensorFactorialObservable_eq_factorial_integral f ξ hξ).symm

end BourgadeHuang
