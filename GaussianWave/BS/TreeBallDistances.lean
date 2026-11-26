import GaussianWave.BS.TreeHomogeneity
import GaussianWave.BS.GaussianForestGram

/-! The recursive distances used in the computed Gaussian factors agree
with actual graph distances under the literal finite-ball embedding. -/
noncomputable section
open scoped Classical
namespace GaussianWave.BS

def regularTreeFirstBranch {d : ℕ} (v : RegularTreeVertex d) : Option (Fin d) :=
  v.map Prod.fst

theorem regularTreeFirstBranch_adj {d : ℕ} {v w : RegularTreeVertex d}
    (h : (regularWordTree d).Adj v w) (hv : v ≠ none) (hw : w ≠ none) :
    regularTreeFirstBranch v = regularTreeFirstBranch w := by
  cases v with
  | none => exact (hv rfl).elim
  | some av =>
    cases w with
    | none => exact (hw rfl).elim
    | some bw =>
      rcases av with ⟨a,x⟩
      rcases bw with ⟨b,y⟩
      rcases h with ⟨_,hp⟩ | ⟨_,hp⟩
      · cases x with
        | nil => exact (Option.noConfusion hp)
        | cons c x =>
          have hh := congrArg (fun v : RegularTreeVertex d => regularTreeFirstBranch v) hp
          exact hh
      · cases y with
        | nil => exact (Option.noConfusion hp)
        | cons c y =>
          have hh := congrArg (fun v : RegularTreeVertex d => regularTreeFirstBranch v) hp
          exact hh.symm

theorem regularTreeFirstBranch_walk {d : ℕ} {v w : RegularTreeVertex d}
    (p : (regularWordTree d).Walk v w) (hp : none ∉ p.support) :
    regularTreeFirstBranch v = regularTreeFirstBranch w := by
  induction p with
  | nil => rfl
  | @cons v u w h p ih =>
    have hv : v ≠ none := by
      intro he
      exact hp (he ▸ (SimpleGraph.Walk.cons h p).start_mem_support)
    have htail : none ∉ p.support := by
      intro hm
      exact hp (by simp only [SimpleGraph.Walk.support_cons, List.mem_cons]; exact Or.inr hm)
    have hu : u ≠ none := by
      intro he
      exact htail (he ▸ p.start_mem_support)
    exact (regularTreeFirstBranch_adj h hv hu).trans (ih htail)

theorem regularTree_dist_distinct_branches (d : ℕ) (a b : Fin d)
    (x y : List (Fin (d-1))) (hab : a ≠ b) :
    (regularWordTree d).dist (some (a,x)) (some (b,y)) = x.length+y.length+2 := by
  have hc := regularWordTree_connected d
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist (some (a,x)) (some (b,y))
  have hroot : none ∈ p.support := by
    by_contra hn
    have hh := regularTreeFirstBranch_walk p hn
    exact hab (Option.some.inj hh)
  have hleft := (regularWordTree d).dist_le (p.takeUntil none hroot)
  have hright := (regularWordTree d).dist_le (p.dropUntil none hroot)
  have hsum := congrArg SimpleGraph.Walk.length (p.take_spec hroot)
  simp only [SimpleGraph.Walk.length_append,hp] at hsum
  have hupper := hc.dist_triangle (u := some (a,x)) (v := none) (w := some (b,y))
  rw [SimpleGraph.dist_comm (u := some (a,x)) (v := none)] at hleft hupper
  simp only [regularTree_dist_root,regularTreeDepth] at hleft hright hupper
  omega

def branchWordEmbedding (q : ℕ) (w : List (Fin q)) : RegularTreeVertex (q+1) :=
  treeHalfDecode q (false,w.reverse)

@[simp] theorem branchWordEmbedding_nil (q : ℕ) : branchWordEmbedding q [] = none := rfl
@[simp] theorem branchWordEmbedding_cons (q : ℕ) (a : Fin q) (w : List (Fin q)) :
    branchWordEmbedding q (a::w) = some (a.succ,w.reverse) := by
  unfold branchWordEmbedding
  rw [List.reverse_cons,treeHalfDecode_false_append]

theorem branchWordEmbedding_depth (q : ℕ) (w : List (Fin q)) :
    regularTreeDepth (branchWordEmbedding q w) = w.length := by
  cases w with
  | nil => rfl
  | cons a w => rw [branchWordEmbedding_cons]; simp [regularTreeDepth]

theorem branchWordEmbedding_flip (q : ℕ) (w : List (Fin q)) :
    regularTreeEdgeFlip q (some (0,w.reverse)) = branchWordEmbedding q w := rfl

theorem regularTree_dist_same_branch (q : ℕ) (a : Fin (q+1)) (w z : List (Fin q)) :
    (regularWordTree (q+1)).dist (some (a,w.reverse)) (some (a,z.reverse)) =
      (regularWordTree (q+1)).dist (branchWordEmbedding q w) (branchWordEmbedding q z) := by
  have hperm := regularTreeIso_dist (q+1)
    (regularTreeRootPermutation (q+1) (Equiv.swap a 0)) (some (a,w.reverse)) (some (a,z.reverse))
  rw [regularTreeRootPermutation_some, regularTreeRootPermutation_some, Equiv.swap_apply_left] at hperm
  have hflip := regularTreeIso_dist (q+1) (regularTreeEdgeFlip q)
    (some (0,w.reverse)) (some (0,z.reverse))
  rw [branchWordEmbedding_flip,branchWordEmbedding_flip] at hflip
  exact hperm.symm.trans hflip.symm

def wordTreeDistance {q : ℕ} : List (Fin q) → List (Fin q) → ℕ
  | [],z => z.length
  | a::w,[] => w.length+1
  | a::w,b::z => if a=b then wordTreeDistance w z else w.length+z.length+2

theorem branchWordEmbedding_dist (q : ℕ) (w z : List (Fin q)) :
    (regularWordTree (q+1)).dist (branchWordEmbedding q w) (branchWordEmbedding q z) =
      wordTreeDistance w z := by
  induction w generalizing z with
  | nil => rw [branchWordEmbedding_nil,regularTree_dist_root,branchWordEmbedding_depth]; rfl
  | cons a w ih =>
    cases z with
    | nil =>
      rw [branchWordEmbedding_nil,SimpleGraph.dist_comm,regularTree_dist_root,branchWordEmbedding_depth]
      rfl
    | cons b z =>
      rw [branchWordEmbedding_cons,branchWordEmbedding_cons]
      change _ = if a=b then wordTreeDistance w z else w.length+z.length+2
      by_cases hab : a=b
      · subst b
        rw [if_pos rfl,regularTree_dist_same_branch]
        exact ih z
      · rw [if_neg hab,regularTree_dist_distinct_branches (q+1) a.succ b.succ w.reverse z.reverse
          (fun h => hab (Fin.succ_injective _ h))]
        simp only [List.length_reverse]

theorem branchPath_length (q k : ℕ) (v : BranchVertex q k) :
    (branchPath q k v).length = branchDepth q k v := by
  induction k with
  | zero => cases v; rfl
  | succ k ih =>
    cases v with
    | inl u => rfl
    | inr av => exact congrArg Nat.succ (ih av.2)

theorem branchDistance_eq_word (q k : ℕ) (v w : BranchVertex q k) :
    branchDistance q k v w = wordTreeDistance (branchPath q k v) (branchPath q k w) := by
  induction k with
  | zero => cases v; cases w; rfl
  | succ k ih =>
    cases v with
    | inl u =>
      cases w with
      | inl t => rfl
      | inr av =>
        change branchDepth q k av.2+1 = (branchPath q k av.2).length+1
        rw [branchPath_length]
    | inr av =>
      cases w with
      | inl t =>
        change branchDepth q k av.2+1 = (branchPath q k av.2).length+1
        rw [branchPath_length]
      | inr bv =>
        change (if av.1=bv.1 then branchDistance q k av.2 bv.2
          else branchDepth q k av.2+branchDepth q k bv.2+2) =
          if av.1=bv.1 then wordTreeDistance (branchPath q k av.2) (branchPath q k bv.2)
          else (branchPath q k av.2).length+(branchPath q k bv.2).length+2
        rw [ih,branchPath_length,branchPath_length]

theorem vertexBallEmbedding_dist (m k : ℕ) (v w : VertexBallVertex (m+2) k) :
    (regularWordTree (m+2)).dist (vertexBallEmbedding (m+2) k v)
      (vertexBallEmbedding (m+2) k w) = vertexBallDistance m k v w := by
  cases v with
  | inl u =>
    cases w with
    | inl t => exact SimpleGraph.dist_self
    | inr av =>
      change (regularWordTree (m+2)).dist none
        (some (av.1,(branchPath (m+1) k av.2).reverse)) = branchDepth (m+1) k av.2+1
      rw [regularTree_dist_root]
      simp only [regularTreeDepth,List.length_reverse,branchPath_length]
  | inr av =>
    cases w with
    | inl t =>
      change (regularWordTree (m+2)).dist
        (some (av.1,(branchPath (m+1) k av.2).reverse)) none = branchDepth (m+1) k av.2+1
      rw [SimpleGraph.dist_comm,regularTree_dist_root]
      simp only [regularTreeDepth,List.length_reverse,branchPath_length]
    | inr bv =>
      change (regularWordTree (m+2)).dist
        (some (av.1,(branchPath (m+1) k av.2).reverse))
        (some (bv.1,(branchPath (m+1) k bv.2).reverse)) =
          if av.1=bv.1 then branchDistance (m+1) k av.2 bv.2
          else branchDepth (m+1) k av.2+branchDepth (m+1) k bv.2+2
      by_cases hab : av.1=bv.1
      · rw [if_pos hab,← hab,regularTree_dist_same_branch (m+1),branchWordEmbedding_dist,
          branchDistance_eq_word]
      · rw [if_neg hab,regularTree_dist_distinct_branches _ _ _ _ _ hab]
        simp only [List.length_reverse,branchPath_length]

end GaussianWave.BS
