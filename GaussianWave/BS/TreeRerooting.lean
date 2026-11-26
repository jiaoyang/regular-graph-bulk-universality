import GaussianWave.BS.TreeAutomorphisms

/-! An actual edge-reversing automorphism of the word tree.  The two
components obtained by deleting the distinguished edge are encoded by a
Boolean and a finite word, and the Boolean is interchanged. -/
noncomputable section
open scoped Classical
set_option maxHeartbeats 400000
namespace GaussianWave.BS

def treeHalfEncode (q : ℕ) : RegularTreeVertex (q+1) → Bool × List (Fin q)
  | none => (false, [])
  | some (a,w) => Fin.cases (motive := fun _ => Bool × List (Fin q))
      (true,w) (fun b => (false,@List.append (Fin q) w [b])) a

def treeHalfDecode (q : ℕ) : Bool × List (Fin q) → RegularTreeVertex (q+1)
  | (true,w) => some (0,w)
  | (false,w) => match w.reverse with
    | [] => none
    | b :: u => some (b.succ,u.reverse)

@[simp] theorem treeHalfEncode_root (q : ℕ) : treeHalfEncode q none = (false,[]) := rfl
@[simp] theorem treeHalfEncode_zero (q : ℕ) (w : List (Fin q)) :
    treeHalfEncode q (some (0,w)) = (true,w) := rfl
@[simp] theorem treeHalfEncode_succ (q : ℕ) (a : Fin q) (w : List (Fin q)) :
    treeHalfEncode q (some (a.succ,w)) = (false,w ++ [a]) := rfl
@[simp] theorem treeHalfDecode_true (q : ℕ) (w : List (Fin q)) :
    treeHalfDecode q (true,w) = some (0,w) := rfl
@[simp] theorem treeHalfDecode_false_nil (q : ℕ) : treeHalfDecode q (false,[]) = none := rfl
@[simp] theorem treeHalfDecode_false_append (q : ℕ) (w : List (Fin q)) (a : Fin q) :
    treeHalfDecode q (false,w ++ [a]) = some (a.succ,w) := by
  simp [treeHalfDecode]

def treeHalfEquiv (q : ℕ) : RegularTreeVertex (q+1) ≃ Bool × List (Fin q) where
  toFun := treeHalfEncode q
  invFun := treeHalfDecode q
  left_inv := by
    intro v
    cases v with
    | none => rfl
    | some aw =>
      rcases aw with ⟨a,w⟩
      induction a using Fin.cases with
      | zero => rfl
      | succ b =>
        change treeHalfDecode q (false,@List.append (Fin q) w [b]) = _
        exact treeHalfDecode_false_append q w b
  right_inv := by
    rintro ⟨a,w⟩
    cases a with
    | true => rfl
    | false =>
      induction w using List.reverseRecOn with
      | nil => rfl
      | append_singleton w b ih =>
        rw [treeHalfDecode_false_append]
        exact treeHalfEncode_succ q b w

def boolFlipEquiv : Equiv.Perm Bool where
  toFun := Bool.not
  invFun := Bool.not
  left_inv := Bool.not_not
  right_inv := Bool.not_not

def regularTreeEdgeFlipEquiv (q : ℕ) : Equiv.Perm (RegularTreeVertex (q+1)) :=
  (treeHalfEquiv q).trans ((boolFlipEquiv.prodCongr (Equiv.refl _)).trans (treeHalfEquiv q).symm)

@[simp] theorem regularTreeEdgeFlip_root (q : ℕ) :
    regularTreeEdgeFlipEquiv q none = some (0,[]) := rfl
@[simp] theorem regularTreeEdgeFlip_zero_nil (q : ℕ) :
    regularTreeEdgeFlipEquiv q (some (0,[])) = none := rfl
@[simp] theorem regularTreeEdgeFlip_zero_append (q : ℕ) (w : List (Fin q)) (a : Fin q) :
    regularTreeEdgeFlipEquiv q (some (0,w ++ [a])) = some (a.succ,w) := by
  change treeHalfDecode q (false,w ++ [a]) = _
  exact treeHalfDecode_false_append q w a
@[simp] theorem regularTreeEdgeFlip_succ (q : ℕ) (a : Fin q) (w : List (Fin q)) :
    regularTreeEdgeFlipEquiv q (some (a.succ,w)) = some (0,w ++ [a]) := rfl

@[simp] theorem regularTreeEdgeFlip_involutive (q : ℕ) (v : RegularTreeVertex (q+1)) :
    regularTreeEdgeFlipEquiv q (regularTreeEdgeFlipEquiv q v) = v := by
  let e := treeHalfEquiv q
  let f := boolFlipEquiv.prodCongr (Equiv.refl (List (Fin q)))
  change e.symm (f (e (e.symm (f (e v))))) = v
  rw [e.apply_symm_apply]
  have hf (x) : f (f x) = x := by
    rcases x with ⟨b,w⟩
    cases b <;> rfl
  rw [hf, e.symm_apply_apply]

theorem regularTreeEdgeFlip_parent_adj (q : ℕ) (v : RegularTreeVertex (q+1)) (hv : v ≠ none) :
    (regularWordTree (q+1)).Adj (regularTreeEdgeFlipEquiv q v)
      (regularTreeEdgeFlipEquiv q (regularTreeParent v)) := by
  cases v with
  | none => exact (hv rfl).elim
  | some aw =>
    rcases aw with ⟨a,w⟩
    induction a using Fin.cases with
    | zero =>
      induction w using List.reverseRecOn with
      | nil =>
        change (regularWordTree (q+1)).Adj none (some (0,[]))
        exact Or.inr ⟨by simp, rfl⟩
      | append_singleton w b ih =>
        cases w with
        | nil =>
          change (regularWordTree (q+1)).Adj
            (regularTreeEdgeFlipEquiv q (some (0,[] ++ [b]))) none
          rw [regularTreeEdgeFlip_zero_append q [] b]
          exact Or.inl ⟨by simp, rfl⟩
        | cons c w =>
          change (regularWordTree (q+1)).Adj
            (regularTreeEdgeFlipEquiv q (some (0,(c::w) ++ [b])))
            (regularTreeEdgeFlipEquiv q (some (0,w ++ [b])))
          rw [regularTreeEdgeFlip_zero_append q (c::w) b, regularTreeEdgeFlip_zero_append q w b]
          exact Or.inl ⟨by simp, rfl⟩
    | succ b =>
      cases w with
      | nil =>
        simp only [regularTreeParent, regularTreeEdgeFlip_succ, regularTreeEdgeFlip_root,
          List.nil_append]
        exact Or.inl ⟨by simp, rfl⟩
      | cons c w =>
        simp only [regularTreeParent, regularTreeEdgeFlip_succ, List.cons_append]
        exact Or.inl ⟨by simp, rfl⟩

theorem regularTreeEdgeFlip_adj (q : ℕ) {v w : RegularTreeVertex (q+1)}
    (h : (regularWordTree (q+1)).Adj v w) :
    (regularWordTree (q+1)).Adj (regularTreeEdgeFlipEquiv q v) (regularTreeEdgeFlipEquiv q w) := by
  rcases h with ⟨hv,hp⟩ | ⟨hw,hp⟩
  · rw [← hp]
    exact regularTreeEdgeFlip_parent_adj q v hv
  · rw [← hp]
    exact (regularTreeEdgeFlip_parent_adj q w hw).symm

def regularTreeEdgeFlip (q : ℕ) : regularWordTree (q+1) ≃g regularWordTree (q+1) where
  toEquiv := regularTreeEdgeFlipEquiv q
  map_rel_iff' := by
    intro v w
    constructor
    · intro h
      simpa only [regularTreeEdgeFlip_involutive] using regularTreeEdgeFlip_adj q h
    · exact regularTreeEdgeFlip_adj q

def regularTreeRootPermutationEquiv (d : ℕ) (σ : Equiv.Perm (Fin d)) :
    Equiv.Perm (RegularTreeVertex d) where
  toFun := fun v => v.map (fun aw => (σ aw.1,aw.2))
  invFun := fun v => v.map (fun aw => (σ.symm aw.1,aw.2))
  left_inv := by rintro (_ | ⟨a,w⟩) <;> simp
  right_inv := by rintro (_ | ⟨a,w⟩) <;> simp

def regularTreeRootPermutation (d : ℕ) (σ : Equiv.Perm (Fin d)) :
    regularWordTree d ≃g regularWordTree d :=
  regularTreeIsoOfParentEquiv d (regularTreeRootPermutationEquiv d σ) rfl (by
    rintro (_ | ⟨a,w⟩)
    · rfl
    · cases w <;> rfl)

@[simp] theorem regularTreeRootPermutation_root (d : ℕ) (σ : Equiv.Perm (Fin d)) :
    regularTreeRootPermutation d σ none = none := rfl
@[simp] theorem regularTreeRootPermutation_some (d : ℕ) (σ : Equiv.Perm (Fin d))
    (a : Fin d) (w : List (Fin (d-1))) :
    regularTreeRootPermutation d σ (some (a,w)) = some (σ a,w) := rfl

def regularTreeRerootNeighbor (q : ℕ) (a : Fin (q+1)) :
    regularWordTree (q+1) ≃g regularWordTree (q+1) :=
  (regularTreeEdgeFlip q).trans (regularTreeRootPermutation (q+1) (Equiv.swap 0 a))

@[simp] theorem regularTreeRerootNeighbor_root (q : ℕ) (a : Fin (q+1)) :
    regularTreeRerootNeighbor q a none = some (a,[]) := by
  change regularTreeRootPermutation (q+1) (Equiv.swap 0 a) (some (0,[])) = _
  rw [regularTreeRootPermutation_some, Equiv.swap_apply_left]

theorem exists_regularTreeRootAutomorphism_step (q : ℕ) {v w : RegularTreeVertex (q+1)}
    (h : (regularWordTree (q+1)).Adj v w)
    (hv : ∃ e : regularWordTree (q+1) ≃g regularWordTree (q+1), e none = v) :
    ∃ e : regularWordTree (q+1) ≃g regularWordTree (q+1), e none = w := by
  obtain ⟨e,he⟩ := hv
  have h' : (regularWordTree (q+1)).Adj none (e.symm w) := by
    have hh := e.symm.map_rel_iff.mpr h
    rw [← he] at hh
    simpa using hh
  obtain ⟨a,ha⟩ := exists_regularTreeNeighbor_of_adj none (e.symm w) h'
  refine ⟨(regularTreeRerootNeighbor q a).trans e, ?_⟩
  change e (regularTreeRerootNeighbor q a none) = w
  rw [regularTreeRerootNeighbor_root]
  change e (regularTreeNeighbor none a) = w
  rw [ha]
  exact e.apply_symm_apply w

/-- Every vertex is the image of the distinguished root under a literal
graph automorphism; no homogeneity assumption is required. -/
theorem exists_regularTreeRootAutomorphism (q : ℕ) (v : RegularTreeVertex (q+1)) :
    ∃ e : regularWordTree (q+1) ≃g regularWordTree (q+1), e none = v := by
  cases v with
  | none => exact ⟨SimpleGraph.Iso.refl, rfl⟩
  | some aw =>
    rcases aw with ⟨a,w⟩
    induction w with
    | nil => exact ⟨regularTreeRerootNeighbor q a, regularTreeRerootNeighbor_root q a⟩
    | cons b w ih =>
      exact exists_regularTreeRootAutomorphism_step q
        (regularTreeNeighbor_adj (some (a,w)) (some b)) ih

def regularTreeReroot (q : ℕ) (v : RegularTreeVertex (q+1)) :
    regularWordTree (q+1) ≃g regularWordTree (q+1) :=
  (exists_regularTreeRootAutomorphism q v).choose

@[simp] theorem regularTreeReroot_root (q : ℕ) (v : RegularTreeVertex (q+1)) :
    regularTreeReroot q v none = v := (exists_regularTreeRootAutomorphism q v).choose_spec

end GaussianWave.BS
