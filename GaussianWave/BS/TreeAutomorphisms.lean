import GaussianWave.BS.BranchAutomorphisms
import GaussianWave.BS.TreeBallEmbedding

/-! Finite branch permutations extend to actual automorphisms of the
countable regular tree, with proved compatibility of finite coordinates. -/
noncomputable section
open scoped Classical
namespace GaussianWave.BS

def branchWordAutomorphism (q : ℕ) : (k : ℕ) → BranchCoverOrdering q k → Equiv.Perm (List (Fin q))
  | 0, _ => Equiv.refl _
  | k + 1, g =>
    { toFun := fun w => match w with
        | [] => []
        | a :: v => g.1 a :: branchWordAutomorphism q k (g.2 a) v
      invFun := fun w => match w with
        | [] => []
        | a :: v => g.1.symm a :: (branchWordAutomorphism q k (g.2 (g.1.symm a))).symm v
      left_inv := by
        intro w
        cases w with
        | nil => rfl
        | cons a v => simp only [Equiv.symm_apply_apply]
      right_inv := by
        intro w
        cases w with
        | nil => rfl
        | cons a v => simp only [Equiv.apply_symm_apply] }

@[simp] theorem branchWordAutomorphism_nil (q k : ℕ) (g : BranchCoverOrdering q k) :
    branchWordAutomorphism q k g [] = [] := by cases k <;> rfl

theorem branchWordAutomorphism_length (q k : ℕ) (g : BranchCoverOrdering q k) (w : List (Fin q)) :
    (branchWordAutomorphism q k g w).length = w.length := by
  induction k generalizing w with
  | zero => rfl
  | succ k ih =>
      cases w with
      | nil => rfl
      | cons a w => simpa only [branchWordAutomorphism, List.length_cons] using congrArg Nat.succ (ih (g.2 a) w)

theorem branchWordAutomorphism_dropLast (q k : ℕ) (g : BranchCoverOrdering q k) (w : List (Fin q)) :
    branchWordAutomorphism q k g w.dropLast = (branchWordAutomorphism q k g w).dropLast := by
  induction k generalizing w with
  | zero => rfl
  | succ k ih =>
      cases w with
      | nil => rfl
      | cons a w =>
          cases w with
          | nil => simp [branchWordAutomorphism]
          | cons b w =>
              change g.1 a :: branchWordAutomorphism q k (g.2 a) (b :: w).dropLast =
                (g.1 a :: branchWordAutomorphism q k (g.2 a) (b :: w)).dropLast
              have hn : branchWordAutomorphism q k (g.2 a) (b :: w) ≠ [] := by
                intro he
                have hh := branchWordAutomorphism_length q k (g.2 a) (b :: w)
                rw [he] at hh
                simp at hh
              rw [List.dropLast_cons_of_ne_nil hn, ih]

theorem branchPath_automorphism (q k : ℕ) (g : BranchCoverOrdering q k) (v : BranchVertex q k) :
    branchPath q k (branchAutomorphism q k g v) = branchWordAutomorphism q k g (branchPath q k v) := by
  induction k with
  | zero => cases v; rfl
  | succ k ih =>
      cases v with
      | inl u => rfl
      | inr av => exact congrArg (List.cons (g.1 av.1)) (ih (g.2 av.1) av.2)

def regularTreeBranchEquiv (d k : ℕ) (g : Fin d → BranchCoverOrdering (d - 1) k) :
    Equiv.Perm (RegularTreeVertex d) where
  toFun
    | none => none
    | some (a, w) => some (a, (branchWordAutomorphism (d - 1) k (g a) w.reverse).reverse)
  invFun
    | none => none
    | some (a, w) => some (a, ((branchWordAutomorphism (d - 1) k (g a)).symm w.reverse).reverse)
  left_inv v := by
    cases v with
    | none => rfl
    | some aw => simp only [List.reverse_reverse, Equiv.symm_apply_apply, Prod.mk.eta]
  right_inv v := by
    cases v with
    | none => rfl
    | some aw => simp only [List.reverse_reverse, Equiv.apply_symm_apply, Prod.mk.eta]

theorem regularTreeParent_forward {d : ℕ} (a : Fin d) (w : List (Fin (d - 1))) :
    regularTreeParent (some (a, w.reverse)) =
      if w = [] then none else some (a, w.dropLast.reverse) := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w b ih => simp [regularTreeParent]

theorem regularTreeBranchEquiv_parent (d k : ℕ) (g : Fin d → BranchCoverOrdering (d - 1) k)
    (v : RegularTreeVertex d) :
    regularTreeBranchEquiv d k g (regularTreeParent v) =
      regularTreeParent (regularTreeBranchEquiv d k g v) := by
  cases v with
  | none => rfl
  | some aw =>
      rcases aw with ⟨a, w⟩
      have hforward := regularTreeParent_forward a w.reverse
      simp only [List.reverse_reverse] at hforward
      rw [hforward]
      change _ = regularTreeParent (some (a, (branchWordAutomorphism (d - 1) k (g a) w.reverse).reverse))
      rw [regularTreeParent_forward]
      by_cases hw : w.reverse = []
      · have he : w = [] := List.reverse_eq_nil_iff.mp hw
        subst w
        simp [regularTreeBranchEquiv]
      · have hn : branchWordAutomorphism (d - 1) k (g a) w.reverse ≠ [] := by
          intro he
          apply hw
          exact (branchWordAutomorphism (d - 1) k (g a)).injective
            (he.trans (branchWordAutomorphism_nil (d - 1) k (g a)).symm)
        rw [if_neg hw, if_neg hn]
        change some (a, (branchWordAutomorphism (d - 1) k (g a)
          w.reverse.dropLast.reverse.reverse).reverse) = _
        simp only [List.reverse_reverse]
        rw [branchWordAutomorphism_dropLast]

def regularTreeIsoOfParentEquiv (d : ℕ) (e : Equiv.Perm (RegularTreeVertex d))
    (hroot : e none = none) (hparent : ∀ v, e (regularTreeParent v) = regularTreeParent (e v)) :
    regularWordTree d ≃g regularWordTree d where
  toEquiv := e
  map_rel_iff' := by
    intro v w
    constructor
    · intro h
      rcases h with ⟨hv, hp⟩ | ⟨hw, hp⟩
      · left
        exact ⟨fun he => hv ((congrArg e he).trans hroot), e.injective ((hparent v).trans hp)⟩
      · right
        exact ⟨fun he => hw ((congrArg e he).trans hroot), e.injective ((hparent w).trans hp)⟩
    · intro h
      rcases h with ⟨hv, hp⟩ | ⟨hw, hp⟩
      · left
        exact ⟨fun he => hv (e.injective (he.trans hroot.symm)), (hparent v).symm.trans (congrArg e hp)⟩
      · right
        exact ⟨fun he => hw (e.injective (he.trans hroot.symm)), (hparent w).symm.trans (congrArg e hp)⟩

def regularTreeBranchAutomorphism (d k : ℕ) (g : Fin d → BranchCoverOrdering (d - 1) k) :
    regularWordTree d ≃g regularWordTree d :=
  regularTreeIsoOfParentEquiv d (regularTreeBranchEquiv d k g) rfl
    (regularTreeBranchEquiv_parent d k g)

theorem vertexBallEmbedding_branchAutomorphism (d k : ℕ)
    (g : Fin d → BranchCoverOrdering (d - 1) k) (a : Fin d) (v : BranchVertex (d - 1) k) :
    regularTreeBranchAutomorphism d k g (vertexBallEmbedding d k (Sum.inr (a, v))) =
      vertexBallEmbedding d k (Sum.inr (a, branchAutomorphism (d - 1) k (g a) v)) := by
  change some (a, (branchWordAutomorphism (d - 1) k (g a)
    (branchPath (d - 1) k v).reverse.reverse).reverse) = _
  simp only [List.reverse_reverse]
  rw [← branchPath_automorphism]
  rfl

end GaussianWave.BS
