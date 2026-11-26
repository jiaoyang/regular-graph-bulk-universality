import GaussianWave.BS.TreeRerooting

/-! The constructed rooted tree automorphisms act transitively on every
level, with an actual finite-prefix permutation witnessing each map. -/
noncomputable section
open scoped Classical
namespace GaussianWave.BS

theorem exists_branchWordAutomorphism_map (q : ℕ) (w z : List (Fin q))
    (h : w.length = z.length) :
    ∃ g : BranchCoverOrdering q w.length, branchWordAutomorphism q w.length g w = z := by
  induction w generalizing z with
  | nil =>
    have hz : z = [] := List.length_eq_zero_iff.mp h.symm
    subst z
    exact ⟨(),rfl⟩
  | cons a w ih =>
    cases z with
    | nil => simp at h
    | cons b z =>
      have hh : w.length = z.length := by simpa only [List.length_cons, Nat.add_right_cancel_iff] using h
      obtain ⟨g,hg⟩ := ih z hh
      let G : BranchCoverOrdering q (w.length+1) :=
        (Equiv.swap a b, fun j => if j = a then g else 1)
      refine ⟨G, ?_⟩
      change Equiv.swap a b a :: branchWordAutomorphism q w.length
        (if a = a then g else 1) w = b :: z
      rw [Equiv.swap_apply_left, if_pos rfl, hg]

theorem exists_regularTreeLevelAutomorphism (d : ℕ) (v w : RegularTreeVertex d)
    (h : regularTreeDepth v = regularTreeDepth w) :
    ∃ e : regularWordTree d ≃g regularWordTree d, e none = none ∧ e v = w := by
  cases v with
  | none =>
    cases w with
    | none => exact ⟨SimpleGraph.Iso.refl,rfl,rfl⟩
    | some aw => simp [regularTreeDepth] at h
  | some av =>
    cases w with
    | none => simp [regularTreeDepth] at h
    | some bw =>
      rcases av with ⟨a,x⟩
      rcases bw with ⟨b,y⟩
      have hlen : x.reverse.length = y.reverse.length := by
        simpa only [regularTreeDepth, Nat.add_right_cancel_iff, List.length_reverse] using h
      obtain ⟨g,hg⟩ := exists_branchWordAutomorphism_map (d-1) x.reverse y.reverse hlen
      let e := (regularTreeBranchAutomorphism d x.reverse.length (fun _ => g)).trans
        (regularTreeRootPermutation d (Equiv.swap a b))
      refine ⟨e, rfl, ?_⟩
      change regularTreeRootPermutation d (Equiv.swap a b)
        (some (a,(branchWordAutomorphism (d-1) x.reverse.length g x.reverse).reverse)) = some (b,y)
      rw [hg, List.reverse_reverse, regularTreeRootPermutation_some, Equiv.swap_apply_left]

end GaussianWave.BS
