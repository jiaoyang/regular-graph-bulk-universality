import Mathlib

/-! A closed finite nonbacktracking chain contains a genuine injectively
embedded cycle. The construction matches the cycle-copy event counted in
`LocalCycleMass`, and avoids assuming a separate girth/tree theorem. -/
noncomputable section
open scoped BigOperators Classical
set_option maxHeartbeats 1200000

namespace GaussianWave.BS.Lower

variable {V : Type*} (G : SimpleGraph V)

/-- Consecutive cyclic adjacency is enough to embed the literal cycle graph. -/
theorem cycleGraph_map_le_of_successors {l : ℕ} [NeZero l] (hl : 2 ≤ l)
    (f : Fin l ↪ V) (hsucc : ∀ j : Fin l,G.Adj (f j) (f (j+1))) :
    (SimpleGraph.cycleGraph l).map f ≤ G := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le' hl
  intro u v huv
  obtain ⟨a,b,hab,rfl,rfl⟩ := (SimpleGraph.map_adj f _ u v).mp huv
  rcases (SimpleGraph.cycleGraph_adj).mp hab with hab | hab
  · have he : a = b+1 := sub_eq_iff_eq_add'.mp hab
    rw [he]
    exact G.symm (hsucc b)
  · have he : b = a+1 := sub_eq_iff_eq_add'.mp hab
    rw [he]
    exact hsucc a

/-- A finite closed chain with no immediate backtracking contains an actual
cycle copy of length at most its original length. Every cycle vertex belongs
to the original chain. -/
theorem closed_nonbacktracking_chain_contains_cycle
    (x : ℕ → V) (L : ℕ) (hL : 0 < L) (hclosed : x 0 = x L)
    (hadj : ∀ i,i < L → G.Adj (x i) (x (i+1)))
    (hback : ∀ i,i+2 ≤ L → x i ≠ x (i+2)) :
    ∃ l : ℕ,3 ≤ l ∧ l ≤ L ∧ ∃ f : Fin l ↪ V,
      (SimpleGraph.cycleGraph l).map f ≤ G ∧ ∀ a : Fin l,∃ j ≤ L,f a = x j := by
  let P (l : ℕ) : Prop := 0 < l ∧ ∃ i,i+l ≤ L ∧ x i = x (i+l)
  have hex : ∃ l,P l := ⟨L,hL,0,by simpa using le_refl L,by simpa using hclosed⟩
  let l := Nat.find hex
  have hspec : P l := Nat.find_spec hex
  obtain ⟨hlpos,i,hi,heq⟩ := hspec
  have hl1 : l ≠ 1 := by
    intro h
    have he : x i = x (i+1) := by simpa only [h] using heq
    have hedge := hadj i (by omega)
    rw [← he] at hedge
    exact G.loopless _ hedge
  have hl2 : l ≠ 2 := by
    intro h
    have he : x i = x (i+2) := by simpa only [h] using heq
    exact hback i (by omega) he
  have hl3 : 3 ≤ l := by omega
  have hnorepeat (a b : ℕ) (hab : a < b) (hb : b < l) : x (i+a) ≠ x (i+b) := by
    intro he
    have hindex : (i+a)+(b-a) = i+b := by omega
    have hp : P (b-a) := ⟨by omega,i+a,by omega,by simpa only [hindex] using he⟩
    have hmin := Nat.find_min' hex hp
    change l ≤ b-a at hmin
    omega
  let f : Fin l ↪ V :=
    ⟨fun a => x (i+a.val),by
      intro a b he
      apply Fin.ext
      by_contra hne
      rcases lt_or_gt_of_ne hne with hab | hab
      · exact hnorepeat a.val b.val hab b.is_lt he
      · exact hnorepeat b.val a.val hab a.is_lt he.symm⟩
  letI : NeZero l := ⟨by omega⟩
  have hone : ((1 : Fin l) : ℕ) = 1 := by
    rw [Fin.val_one',Nat.mod_eq_of_lt (by omega : 1 < l)]
  have hsucc (a : Fin l) : G.Adj (f a) (f (a+1)) := by
    have haval : (a+1).val = (a.val+1)%l := by rw [Fin.val_add,hone]
    have hedge := hadj (i+a.val) (by omega)
    by_cases hlast : a.val+1 < l
    · have hn : (a+1).val = a.val+1 := by rw [haval,Nat.mod_eq_of_lt hlast]
      change G.Adj (x (i+a.val)) (x (i+(a+1).val))
      simpa only [hn,Nat.add_assoc] using hedge
    · have ha : a.val+1 = l := by omega
      have hn : (a+1).val = 0 := by rw [haval,ha,Nat.mod_self]
      have hend : i+a.val+1 = i+l := by omega
      rw [hend,← heq] at hedge
      change G.Adj (x (i+a.val)) (x (i+(a+1).val))
      simpa only [hn,Nat.add_zero] using hedge
  refine ⟨l,hl3,by omega,f,cycleGraph_map_le_of_successors G (by omega) f hsucc,?_⟩
  intro a
  exact ⟨i+a.val,by omega,rfl⟩

end GaussianWave.BS.Lower
