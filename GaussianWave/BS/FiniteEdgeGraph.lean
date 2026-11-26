import GaussianWave.BS.ParentClosedTree
import GaussianWave.BS.EdgeBallDistances

/-! Literal induced edge balls form parent-closed subtrees. -/
noncomputable section
open scoped Classical
namespace GaussianWave.BS

theorem regularTreeEdgeDepth_parent_le (m : ℕ) (v : RegularTreeVertex (m+2)) :
    regularTreeEdgeDepth m (regularTreeParent v) ≤ regularTreeEdgeDepth m v := by
  cases v with
  | none => exact le_refl _
  | some av =>
    rcases av with ⟨a,w⟩
    induction a using Fin.cases with
    | zero => cases w <;> simp [regularTreeEdgeDepth,regularTreeParent,treeHalfEncode]
    | succ b => cases w <;> simp [regularTreeEdgeDepth,regularTreeParent,treeHalfEncode]

def edgeBallRoot (m k : ℕ) (b : Bool) : EdgeBallVertex (m+2) k :=
  (b,branchRoot (m+1) k)

@[simp] theorem edgeBallEmbedding_left_root (m k : ℕ) :
    edgeBallEmbedding m k (edgeBallRoot m k false)=none := by cases k <;> rfl

@[simp] theorem edgeBallEmbedding_right_root (m k : ℕ) :
    edgeBallEmbedding m k (edgeBallRoot m k true)=some (0,[]) := by cases k <;> rfl

def edgeBallParent (m k : ℕ) (v : EdgeBallVertex (m+2) k) : EdgeBallVertex (m+2) k :=
  edgeBallIndexOfDepth m k (regularTreeParent (edgeBallEmbedding m k v))
    ((regularTreeEdgeDepth_parent_le m _).trans (edgeBallEmbedding_edgeDepth m k v))

@[simp] theorem edgeBallParent_embedding (m k : ℕ) (v : EdgeBallVertex (m+2) k) :
    edgeBallEmbedding m k (edgeBallParent m k v)=regularTreeParent (edgeBallEmbedding m k v) :=
  edgeBallIndexOfDepth_spec _ _ _ _

def edgeBallParentClosedTree (m k : ℕ) : ParentClosedTree (m+2) (EdgeBallVertex (m+2) k) where
  embedding := ⟨edgeBallEmbedding m k,edgeBallEmbedding_injective m k⟩
  root := edgeBallRoot m k false
  root_embedding := edgeBallEmbedding_left_root m k
  parent := edgeBallParent m k
  parent_embedding := edgeBallParent_embedding m k

def edgeBallGraph (m k : ℕ) : SimpleGraph (EdgeBallVertex (m+2) k) :=
  (edgeBallParentClosedTree m k).graph

theorem branchWordEmbedding_ancestor (q : ℕ) (w z : List (Fin q)) :
    RegularTreeAncestor (branchWordEmbedding q w) (branchWordEmbedding q z) ↔ w.IsPrefix z := by
  cases w with
  | nil =>
    simp only [branchWordEmbedding_nil,List.nil_prefix,iff_true]
    exact regularTreeAncestor_root (q+1) _
  | cons a w =>
    cases z with
    | nil =>
      rw [branchWordEmbedding_cons,branchWordEmbedding_nil]
      constructor
      · rintro ⟨n,hn⟩
        have hh : (regularTreeParent^[n]) (none : RegularTreeVertex (q+1))=none := Function.iterate_fixed rfl n
        rw [hh] at hn
        exact False.elim (Option.noConfusion hn)
      · simp
    | cons b z =>
      rw [branchWordEmbedding_cons,branchWordEmbedding_cons,regularTreeAncestor_word_iff]
      simp only [Fin.succ_inj,List.cons_prefix_cons]

theorem edgeBallEmbedding_half_ancestor (m k : ℕ) (b : Bool)
    (v w : BranchVertex (m+1) k) :
    RegularTreeAncestor (edgeBallEmbedding m k (b,v)) (edgeBallEmbedding m k (b,w)) ↔
      (branchPath (m+1) k v).IsPrefix (branchPath (m+1) k w) := by
  cases b with
  | false => exact branchWordEmbedding_ancestor (m+1) _ _
  | true =>
    exact (regularTreeAncestor_word_iff (0 : Fin (m+2)) 0
      (branchPath (m+1) k v) (branchPath (m+1) k w)).trans (by simp)

theorem edgeBallEmbedding_right_ancestor (m k : ℕ) (v : EdgeBallVertex (m+2) k) :
    RegularTreeAncestor (edgeBallEmbedding m k (edgeBallRoot m k true)) (edgeBallEmbedding m k v) ↔
      v.1=true := by
  rcases v with ⟨b,v⟩
  rw [edgeBallEmbedding_right_root]
  cases b with
  | true =>
    change RegularTreeAncestor (some ((0 : Fin (m+2)),[]))
      (some ((0 : Fin (m+2)),(branchPath (m+1) k v).reverse)) ↔ (true : Bool)=true
    simpa using regularTreeAncestor_word_iff (0 : Fin (m+2)) 0 [] (branchPath (m+1) k v)
  | false =>
    have hn : ¬RegularTreeAncestor (some ((0 : Fin (m+2)),[]))
        (branchWordEmbedding (m+1) (branchPath (m+1) k v)) := by
      cases hw : branchPath (m+1) k v with
      | nil =>
        rw [branchWordEmbedding_nil]
        rintro ⟨n,hn⟩
        have hh : (regularTreeParent^[n]) (none : RegularTreeVertex (m+2))=none := Function.iterate_fixed rfl n
        rw [hh] at hn
        exact Option.noConfusion hn
      | cons a w =>
        rw [branchWordEmbedding_cons]
        simpa [Ne.symm (Fin.succ_ne_zero a)] using
          regularTreeAncestor_word_iff (0 : Fin (m+2)) a.succ [] w
    exact ⟨fun h => (hn h).elim,fun h => Bool.noConfusion h⟩

end GaussianWave.BS
