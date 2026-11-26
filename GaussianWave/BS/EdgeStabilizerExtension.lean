import GaussianWave.BS.FiniteEdgeStabilizer

/-! Every finite edge-center stabilizer extends to a literal automorphism
of the entire regular tree. -/
noncomputable section
open scoped Classical
namespace GaussianWave.BS

theorem branchWordAutomorphism_one (q k : ℕ) (w : List (Fin q)) :
    branchWordAutomorphism q k 1 w=w := by
  induction k generalizing w with
  | zero => rfl
  | succ k ih =>
    cases w with
    | nil => rfl
    | cons a w =>
      change a :: branchWordAutomorphism q k 1 w=a::w
      rw [ih]

theorem regularTreeBranchAutomorphism_one_arm (d k : ℕ)
    (g : Fin d → BranchCoverOrdering (d-1) k) (a : Fin d) (w : List (Fin (d-1)))
    (ha : g a=1) : regularTreeBranchAutomorphism d k g (some (a,w))=some (a,w) := by
  change some (a,(branchWordAutomorphism (d-1) k (g a) w.reverse).reverse)=_
  rw [ha,branchWordAutomorphism_one,List.reverse_reverse]

def finFixZeroPermutation (q : ℕ) (σ : Equiv.Perm (Fin q)) : Equiv.Perm (Fin (q+1)) where
  toFun := Fin.cases 0 (fun a => (σ a).succ)
  invFun := Fin.cases 0 (fun a => (σ.symm a).succ)
  left_inv := by
    intro a
    induction a using Fin.cases with
    | zero => rfl
    | succ a => simp
  right_inv := by
    intro a
    induction a using Fin.cases with
    | zero => rfl
    | succ a => simp

@[simp] theorem finFixZeroPermutation_zero (q : ℕ) (σ : Equiv.Perm (Fin q)) :
    finFixZeroPermutation q σ 0=0 := rfl
@[simp] theorem finFixZeroPermutation_succ (q : ℕ) (σ : Equiv.Perm (Fin q)) (a : Fin q) :
    finFixZeroPermutation q σ a.succ=(σ a).succ := rfl

def edgeBallStabilizerExtension (m : ℕ) : (k : ℕ) → EdgeBallStabilizer (m+2) k →
    (regularWordTree (m+2) ≃g regularWordTree (m+2))
  | 0,_ => SimpleGraph.Iso.refl
  | k+1,g =>
    let gt : Fin (m+2) → BranchCoverOrdering (m+1) (k+1) := fun a => if a=0 then g true else 1
    let gf : Fin (m+2) → BranchCoverOrdering (m+1) k := Fin.cases 1 (fun a => (g false).2 a)
    ((regularTreeBranchAutomorphism (m+2) (k+1) gt).trans
      (regularTreeBranchAutomorphism (m+2) k gf)).trans
      (regularTreeRootPermutation (m+2) (finFixZeroPermutation (m+1) (g false).1))

theorem edgeBallEmbedding_stabilizerExtension (m k : ℕ) (g : EdgeBallStabilizer (m+2) k)
    (v : EdgeBallVertex (m+2) k) :
    edgeBallStabilizerExtension m k g (edgeBallEmbedding m k v)=edgeBallEmbedding m k (g • v) := by
  cases k with
  | zero =>
    rcases v with ⟨b,v⟩
    cases v
    rfl
  | succ k =>
    let gt : Fin (m+2) → BranchCoverOrdering (m+1) (k+1) := fun a => if a=0 then g true else 1
    let gf : Fin (m+2) → BranchCoverOrdering (m+1) k := Fin.cases 1 (fun a => (g false).2 a)
    let et := regularTreeBranchAutomorphism (m+2) (k+1) gt
    let ef := regularTreeBranchAutomorphism (m+2) k gf
    let er := regularTreeRootPermutation (m+2) (finFixZeroPermutation (m+1) (g false).1)
    rcases v with ⟨b,v⟩
    cases b with
    | true =>
      change er (ef (et (some (0,(branchPath (m+1) (k+1) v).reverse)))) =
        some (0,(branchPath (m+1) (k+1) (branchAutomorphism (m+1) (k+1) (g true) v)).reverse)
      have ht := vertexBallEmbedding_branchAutomorphism (m+2) (k+1) gt 0 v
      change et (some (0,(branchPath (m+1) (k+1) v).reverse))=
        some (0,(branchPath (m+1) (k+1) (branchAutomorphism (m+1) (k+1) (gt 0) v)).reverse) at ht
      have hgt : gt 0=g true := if_pos rfl
      rw [hgt] at ht
      rw [ht,regularTreeBranchAutomorphism_one_arm (m+2) k gf 0 _ rfl,
        regularTreeRootPermutation_some,finFixZeroPermutation_zero]
    | false =>
      cases v with
      | inl u =>
        change er (ef (et none))=edgeBallEmbedding m (k+1) (false,branchAutomorphism (m+1) (k+1) (g false) (Sum.inl u))
        rfl
      | inr av =>
        rcases av with ⟨a,v⟩
        have hemb : edgeBallEmbedding m (k+1) (false,Sum.inr (a,v))=
            some (a.succ,(branchPath (m+1) k v).reverse) := by
          simp only [edgeBallEmbedding,branchPath,List.reverse_cons,treeHalfDecode_false_append]
        rw [hemb]
        change er (ef (et (some (a.succ,(branchPath (m+1) k v).reverse)))) = _
        have hgt : gt a.succ=1 := if_neg (Fin.succ_ne_zero a)
        rw [regularTreeBranchAutomorphism_one_arm (m+2) (k+1) gt a.succ _ hgt]
        have hf := vertexBallEmbedding_branchAutomorphism (m+2) k gf a.succ v
        change ef (some (a.succ,(branchPath (m+1) k v).reverse))=
          some (a.succ,(branchPath (m+1) k (branchAutomorphism (m+1) k (gf a.succ) v)).reverse) at hf
        rw [hf,regularTreeRootPermutation_some,finFixZeroPermutation_succ]
        change some (((g false).1 a).succ,
          (branchPath (m+1) k (branchAutomorphism (m+1) k ((g false).2 a) v)).reverse)=
          edgeBallEmbedding m (k+1) (false,Sum.inr ((g false).1 a,
            branchAutomorphism (m+1) k ((g false).2 a) v))
        simp only [edgeBallEmbedding,branchAutomorphism,Sum.elim_inr,branchPath,List.reverse_cons,
          treeHalfDecode_false_append]

end GaussianWave.BS
