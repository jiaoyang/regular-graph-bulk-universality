import Mathlib

/-! Measurable concatenation of finite cell occurrence lists. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GeneralizedBulk.Counting

def countPrefix (c : ℕ → ℕ) (m : ℕ) : ℕ := ∑ j ∈ Finset.range m, c j

@[simp] theorem countPrefix_zero (c : ℕ → ℕ) : countPrefix c 0 = 0 := by simp [countPrefix]
@[simp] theorem countPrefix_succ (c : ℕ → ℕ) (m : ℕ) :
    countPrefix c (m + 1) = countPrefix c m + c m := by simp [countPrefix,Finset.sum_range_succ]

theorem countPrefix_monotone (c : ℕ → ℕ) : Monotone (countPrefix c) := by
  intro a b hab
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hab)

def prefixCell (c : ℕ → ℕ) (h : ∀ n, ∃ m, n < countPrefix c (m + 1)) (n : ℕ) : ℕ :=
  Nat.find (h n)

theorem prefixCell_upper (c : ℕ → ℕ) (h : ∀ n, ∃ m, n < countPrefix c (m + 1)) (n : ℕ) :
    n < countPrefix c (prefixCell c h n + 1) := Nat.find_spec (h n)

theorem prefixCell_lower (c : ℕ → ℕ) (h : ∀ n, ∃ m, n < countPrefix c (m + 1)) (n : ℕ) :
    countPrefix c (prefixCell c h n) ≤ n := by
  by_cases hz : prefixCell c h n = 0
  · simp [hz]
  · have hprev : prefixCell c h n - 1 < prefixCell c h n := by omega
    have hp : ¬n < countPrefix c ((prefixCell c h n - 1) + 1) := Nat.find_min (h n) hprev
    have heq : (prefixCell c h n - 1) + 1 = prefixCell c h n := by omega
    rw [heq] at hp
    exact le_of_not_gt hp

theorem prefixCell_rank_lt (c : ℕ → ℕ) (h : ∀ n, ∃ m, n < countPrefix c (m + 1)) (n : ℕ) :
    n - countPrefix c (prefixCell c h n) < c (prefixCell c h n) := by
  have hlo := prefixCell_lower c h n
  have hhi := prefixCell_upper c h n
  rw [countPrefix_succ] at hhi
  omega

theorem prefixCell_at_encode (c : ℕ → ℕ) (h : ∀ n, ∃ m, n < countPrefix c (m + 1))
    (m : ℕ) (k : Fin (c m)) : prefixCell c h (countPrefix c m + k.val) = m := by
  let n := countPrefix c m + k.val
  have hvalid : n < countPrefix c (m + 1) := by rw [countPrefix_succ]; dsimp [n]; omega
  have hle : prefixCell c h n ≤ m := Nat.find_min' (h n) hvalid
  have hge : m ≤ prefixCell c h n := by
    by_contra hn
    have hlt : prefixCell c h n < m := lt_of_not_ge hn
    have hh := countPrefix_monotone c (Nat.succ_le_of_lt hlt)
    have hu := prefixCell_upper c h n
    have hmn : countPrefix c m ≤ n := by dsimp [n]; omega
    exact (not_lt_of_ge (hh.trans hmn)) hu
  exact le_antisymm hle hge

/-- Concatenating the finite cell lists gives a genuine occurrence bijection. -/
def prefixOccurrenceEquiv (c : ℕ → ℕ) (h : ∀ n, ∃ m, n < countPrefix c (m + 1)) :
    ℕ ≃ ((m : ℕ) × Fin (c m)) where
  toFun n := ⟨prefixCell c h n,⟨n - countPrefix c (prefixCell c h n),prefixCell_rank_lt c h n⟩⟩
  invFun p := countPrefix c p.1 + p.2.val
  left_inv n := by
    exact Nat.add_sub_of_le (prefixCell_lower c h n)
  right_inv p := by
    rcases p with ⟨m,k⟩
    have hm := prefixCell_at_encode c h m k
    apply Sigma.ext hm
    dsimp only
    apply (Fin.heq_ext_iff (congrArg c hm)).2
    simp only [Fin.val_mk]
    rw [hm]
    omega

theorem measurable_countPrefix {S : Type*} [MeasurableSpace S]
    (c : S → ℕ → ℕ) (hc : ∀ m, Measurable (fun s => c s m)) (m : ℕ) :
    Measurable (fun s => countPrefix (c s) m) :=
  Finset.measurable_sum _ (fun j hj => hc j)

/-- The least cell containing the nth occurrence is measurable because its
level sets use only finitely many integer prefix comparisons. -/
theorem measurable_prefixCell {S : Type*} [MeasurableSpace S]
    (c : S → ℕ → ℕ) (hc : ∀ m, Measurable (fun s => c s m))
    (h : ∀ s n, ∃ m, n < countPrefix (c s) (m + 1)) (n : ℕ) :
    Measurable (fun s => prefixCell (c s) (h s) n) := by
  classical
  apply measurable_to_countable'
  intro m
  have heq : (fun s => prefixCell (c s) (h s) n) ⁻¹' {m} =
      {s | n < countPrefix (c s) (m + 1)} ∩
      {s | ∀ j < m, ¬n < countPrefix (c s) (j + 1)} := by
    ext s
    exact Nat.find_eq_iff (h s n)
  rw [heq]
  apply (measurableSet_lt measurable_const (measurable_countPrefix c hc (m + 1))).inter
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro hj
  exact (measurableSet_lt measurable_const (measurable_countPrefix c hc (j + 1))).compl

theorem measurable_prefixRank {S : Type*} [MeasurableSpace S]
    (c : S → ℕ → ℕ) (hc : ∀ m, Measurable (fun s => c s m))
    (h : ∀ s n, ∃ m, n < countPrefix (c s) (m + 1)) (n : ℕ) :
    Measurable (fun s => n - countPrefix (c s) (prefixCell (c s) (h s) n)) := by
  have hm : Measurable (fun p : S × ℕ => countPrefix (c p.1) p.2) :=
    measurable_from_prod_countable (fun m => measurable_countPrefix c hc m)
  exact measurable_const.sub (hm.comp (measurable_id.prodMk (measurable_prefixCell c hc h n)))

end GeneralizedBulk.Counting
