import GeneralizedBulk.Graph.UniformMarginals

/-! A uniform `O_d(1/N)` rejection bound for the actual joint switching model. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace GeneralizedBulk.Graph

def edgePairTotalEquiv (N d : ℕ) :
    (Σ G : RegularGraph N d, G.val.Dart × G.val.Dart) ≃ EdgePairState N d where
  toFun t := ⟨(t.1.val, ![t.2.1.fst, t.2.1.snd, t.2.2.fst, t.2.2.snd]),
    t.1.property, t.2.1.adj, t.2.2.adj⟩
  invFun s := ⟨edgePairGraph s,
    ⟨⟨(s.val.2 0, s.val.2 1), s.property.2.1⟩,
      ⟨(s.val.2 2, s.val.2 3), s.property.2.2⟩⟩⟩
  left_inv t := by
    rcases t with ⟨⟨G, hG⟩, ⟨⟨⟨v, w⟩, ha⟩, ⟨⟨x, y⟩, hb⟩⟩⟩
    rfl
  right_inv s := by
    rcases s with ⟨⟨G, e⟩, hreg, h01, h23⟩
    apply Subtype.ext
    change (G, ![e 0, e 1, e 2, e 3]) = (G, e)
    apply Prod.ext
    · rfl
    · funext i
      fin_cases i <;> rfl

def rejectedStates (N d : ℕ) : Finset (EdgePairState N d) :=
  Finset.univ.filter (fun s => ¬Accepted s)

private theorem accept_indicator_eq (A B C : Prop)
    {d1 : Decidable (A ∧ ¬B ∧ ¬C)} {d2 : Decidable (¬A ∨ B ∨ C)} :
    (@ite ℕ (A ∧ ¬B ∧ ¬C) d1 0 1) = (@ite ℕ (¬A ∨ B ∨ C) d2 1 0) := by
  by_cases hA : A <;> by_cases hB : B <;> by_cases hC : C <;> simp [hA, hB, hC]

set_option maxHeartbeats 2000000 in
theorem rejectedStates_card_sum (N d : ℕ) :
    (rejectedStates N d).card =
      ∑ G : RegularGraph N d, ∑ a : G.val.Dart, (badSecond G.val a).card := by
  have hrejected : (rejectedStates N d).card =
      ∑ s : EdgePairState N d, if Accepted s then 0 else 1 := by
    rw [rejectedStates, Finset.card_eq_sum_ones, Finset.sum_filter]
    simp only [ite_not]
  rw [hrejected, ← Equiv.sum_comp (edgePairTotalEquiv N d), Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro G hG
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  rw [badSecond, Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b hb
  have hacc : Accepted ((edgePairTotalEquiv N d) ⟨G, (a, b)⟩) ↔
      Function.Injective (dartEndpoints G.val a b) ∧ ¬G.val.Adj a.fst b.snd ∧
        ¬G.val.Adj b.fst a.snd := Iff.rfl
  have h := congrArg (fun p : Prop => @ite ℕ p (Classical.propDecidable p) 0 1) (propext hacc)
  exact h.trans (accept_indicator_eq (Function.Injective (dartEndpoints G.val a b))
    (G.val.Adj a.fst b.snd) (G.val.Adj b.fst a.snd))

theorem edgePairState_card (N d : ℕ) :
    Fintype.card (EdgePairState N d) = Fintype.card (RegularGraph N d) * (N * d) ^ 2 := by
  have hc (G : RegularGraph N d) : Fintype.card G.val.Dart = N * d := by
    rw [regular_dart_card G.val G.property, Fintype.card_fin]
  rw [← Fintype.card_congr (edgePairTotalEquiv N d), Fintype.card_sigma]
  simp only [Fintype.card_prod, hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id,
    pow_two]

theorem rejectedStates_card_le (N d : ℕ) :
    (rejectedStates N d).card ≤
      Fintype.card (RegularGraph N d) * (N * d) * (4 * d + 2 * d ^ 2) := by
  rw [rejectedStates_card_sum]
  calc
    _ ≤ ∑ G : RegularGraph N d, ∑ a : G.val.Dart, (4 * d + 2 * d ^ 2) := by
      apply Finset.sum_le_sum
      intro G hG
      exact Finset.sum_le_sum (fun a ha => badSecond_card_le G.val G.property a)
    _ = _ := by
      have hc (G : RegularGraph N d) : Fintype.card G.val.Dart = N * d := by
        rw [regular_dart_card G.val G.property, Fintype.card_fin]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id, hc]
      ring

/-- The rejected proportion is uniformly at most `(4+2d)/N` under the actual
uniform labeled-regular-graph and two-oriented-edge law. -/
theorem edgePairLaw_rejection_probability_bound {N d : ℕ}
    [Nonempty (RegularGraph N d)] (hN : 0 < N) (hd : 0 < d) :
    (edgePairLaw N d {s | ¬Accepted s}).toReal ≤ (4 + 2 * (d : ℝ)) / N := by
  have hs : ({s | ¬Accepted s} : Set (EdgePairState N d)) = (rejectedStates N d : Set _) := by
    ext s
    simp only [rejectedStates, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
      true_and, Set.mem_setOf_eq]
  rw [edgePairLaw, hs, finiteUniform_finset_toReal, edgePairState_card, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_mul]
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hGR : (0 : ℝ) < Fintype.card (RegularGraph N d) := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ (mul_pos hGR (pow_pos (mul_pos hNR hdR) 2))).mpr
  have hc : ((rejectedStates N d).card : ℝ) ≤
      (Fintype.card (RegularGraph N d) : ℝ) * ((N : ℝ) * d) * (4 * (d : ℝ) + 2 * (d : ℝ) ^ 2) := by
    exact_mod_cast rejectedStates_card_le N d
  have he : (4 + 2 * (d : ℝ)) / N * ((Fintype.card (RegularGraph N d) : ℝ) * ((N : ℝ) * d) ^ 2) =
      (Fintype.card (RegularGraph N d) : ℝ) * ((N : ℝ) * d) * (4 * (d : ℝ) + 2 * (d : ℝ) ^ 2) := by
    field_simp
    ring
  rw [he]
  exact hc

end GeneralizedBulk.Graph
