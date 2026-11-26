import GaussianWave.BS.FiniteEdgeGraph
import GaussianWave.BS.BranchFamilyActions

/-! Completeness of the actual edge-center stabilizer action. -/
noncomputable section
open scoped Classical
set_option maxHeartbeats 1000000
namespace GaussianWave.BS

theorem branchAutomorphism_depth (q k : ℕ) (g : BranchCoverOrdering q k) (v : BranchVertex q k) :
    branchDepth q k (branchAutomorphism q k g v)=branchDepth q k v := by
  rw [← branchPath_length,branchPath_automorphism,branchWordAutomorphism_length,branchPath_length]

theorem branchAutomorphism_distance (q k : ℕ) (g : BranchCoverOrdering q k) (v w : BranchVertex q k) :
    branchDistance q k (branchAutomorphism q k g v) (branchAutomorphism q k g w)=branchDistance q k v w := by
  induction k with
  | zero => rfl
  | succ k ih =>
    cases v with
    | inl u =>
      cases w with
      | inl t => rfl
      | inr aw => exact congrArg (fun n => n+1) (branchAutomorphism_depth q k (g.2 aw.1) aw.2)
    | inr av =>
      cases w with
      | inl t => exact congrArg (fun n => n+1) (branchAutomorphism_depth q k (g.2 av.1) av.2)
      | inr bw =>
        change (if g.1 av.1=g.1 bw.1 then
          branchDistance q k (branchAutomorphism q k (g.2 av.1) av.2) (branchAutomorphism q k (g.2 bw.1) bw.2)
          else branchDepth q k (branchAutomorphism q k (g.2 av.1) av.2)+
            branchDepth q k (branchAutomorphism q k (g.2 bw.1) bw.2)+2) = _
        simp only [g.1.injective.eq_iff,branchAutomorphism_depth]
        by_cases hab : av.1=bw.1
        · rw [if_pos hab]
          simpa only [branchDistance,Sum.elim_inr,if_pos hab,← hab] using ih (g.2 av.1) av.2 bw.2
        · simp only [branchDistance,Sum.elim_inr,if_neg hab]

def edgeBallStabilizerGraphIso (m k : ℕ) (g : EdgeBallStabilizer (m+2) k) :
    edgeBallGraph m k ≃g edgeBallGraph m k where
  toEquiv := MulAction.toPerm g
  map_rel_iff' := by
    intro v w
    change (regularWordTree (m+2)).Adj (edgeBallEmbedding m k (g • v))
      (edgeBallEmbedding m k (g • w)) ↔
      (regularWordTree (m+2)).Adj (edgeBallEmbedding m k v) (edgeBallEmbedding m k w)
    rw [← SimpleGraph.dist_eq_one_iff_adj,← SimpleGraph.dist_eq_one_iff_adj,
      edgeBallEmbedding_dist,edgeBallEmbedding_dist]
    rcases v with ⟨b,v⟩
    rcases w with ⟨c,w⟩
    change (if b=c then branchDistance (m+1) k (branchAutomorphism (m+1) k (g b) v)
      (branchAutomorphism (m+1) k (g c) w) else
      branchDepth (m+1) k (branchAutomorphism (m+1) k (g b) v)+
        branchDepth (m+1) k (branchAutomorphism (m+1) k (g c) w)+1)=1 ↔ _
    by_cases hbc : b=c
    · subst c
      rw [if_pos rfl,branchAutomorphism_distance]
      simp only [edgeBallDistance,if_pos rfl,ite_true]
    · rw [if_neg hbc,branchAutomorphism_depth,branchAutomorphism_depth]
      simp only [edgeBallDistance,if_neg hbc,ite_false]

@[simp] theorem edgeBallStabilizerGraphIso_apply (m k : ℕ) (g : EdgeBallStabilizer (m+2) k)
    (v : EdgeBallVertex (m+2) k) : edgeBallStabilizerGraphIso m k g v=g • v := rfl

@[simp] theorem edgeBallStabilizerGraphIso_root (m k : ℕ) (g : EdgeBallStabilizer (m+2) k) (b : Bool) :
    edgeBallStabilizerGraphIso m k g (edgeBallRoot m k b)=edgeBallRoot m k b := by
  change (b,branchAutomorphism (m+1) k (g b) (branchRoot (m+1) k)) = _
  rw [branchAutomorphism_root]
  rfl

theorem edgeBallGraphIso_half (m k : ℕ) (e : edgeBallGraph m k ≃g edgeBallGraph m k)
    (he : ∀ b,e (edgeBallRoot m k b)=edgeBallRoot m k b) (v : EdgeBallVertex (m+2) k) :
    (e v).1=v.1 := by
  have h := (edgeBallParentClosedTree m k).iso_ancestor e (he false) (edgeBallRoot m k true) v
  change RegularTreeAncestor (edgeBallEmbedding m k (e (edgeBallRoot m k true))) (edgeBallEmbedding m k (e v)) ↔
    RegularTreeAncestor (edgeBallEmbedding m k (edgeBallRoot m k true)) (edgeBallEmbedding m k v) at h
  rw [he true,edgeBallEmbedding_right_ancestor,edgeBallEmbedding_right_ancestor] at h
  cases hv : v.1 <;> cases he' : (e v).1 <;> simp_all

def edgeBallGraphIso_branch (m k : ℕ) (e : edgeBallGraph m k ≃g edgeBallGraph m k)
    (he : ∀ b,e (edgeBallRoot m k b)=edgeBallRoot m k b) (b : Bool) :
    Equiv.Perm (BranchVertex (m+1) k) where
  toFun := fun v => (e (b,v)).2
  invFun := fun v => (e.symm (b,v)).2
  left_inv := by
    intro v
    have hp : (b,(e (b,v)).2)=e (b,v) := Prod.ext (edgeBallGraphIso_half m k e he (b,v)).symm rfl
    change (e.symm (b,(e (b,v)).2)).2=v
    rw [hp,e.symm_apply_apply]
  right_inv := by
    intro v
    have hei (a) : e.symm (edgeBallRoot m k a)=edgeBallRoot m k a := by
      have h := congrArg e.symm (he a)
      simpa only [e.symm_apply_apply] using h.symm
    have hp : (b,(e.symm (b,v)).2)=e.symm (b,v) := Prod.ext
      (edgeBallGraphIso_half m k e.symm hei (b,v)).symm rfl
    change (e (b,(e.symm (b,v)).2)).2=v
    rw [hp,e.apply_symm_apply]

theorem edgeBallGraphIso_branch_pair (m k : ℕ) (e : edgeBallGraph m k ≃g edgeBallGraph m k)
    (he : ∀ b,e (edgeBallRoot m k b)=edgeBallRoot m k b) (b : Bool) (v : BranchVertex (m+1) k) :
    (b,edgeBallGraphIso_branch m k e he b v)=e (b,v) :=
  Prod.ext (edgeBallGraphIso_half m k e he (b,v)).symm rfl

theorem edgeBallEmbedding_depth_exact (m k : ℕ) (b : Bool) (v : BranchVertex (m+1) k) :
    regularTreeDepth (edgeBallEmbedding m k (b,v))=(branchPath (m+1) k v).length+(if b then 1 else 0) := by
  cases b with
  | false => exact branchWordEmbedding_depth (m+1) _
  | true => simp [edgeBallEmbedding,treeHalfDecode,regularTreeDepth]

theorem exists_edgeBallStabilizer_of_graphIso (m k : ℕ)
    (e : edgeBallGraph m k ≃g edgeBallGraph m k)
    (he : ∀ b,e (edgeBallRoot m k b)=edgeBallRoot m k b) :
    ∃ g : EdgeBallStabilizer (m+2) k,∀ v,g • v=e v := by
  have hex (b : Bool) : ∃ g : BranchCoverOrdering (m+1) k,
      branchAutomorphism (m+1) k g=edgeBallGraphIso_branch m k e he b := by
    apply exists_branchAutomorphism_of_prefix
    · intro v
      have h := (edgeBallParentClosedTree m k).iso_depth e (he false) (b,v)
      change regularTreeDepth (edgeBallEmbedding m k (e (b,v)))=regularTreeDepth (edgeBallEmbedding m k (b,v)) at h
      rw [← edgeBallGraphIso_branch_pair m k e he b v,edgeBallEmbedding_depth_exact,
        edgeBallEmbedding_depth_exact] at h
      omega
    · intro v w
      have h := (edgeBallParentClosedTree m k).iso_ancestor e (he false) (b,v) (b,w)
      change RegularTreeAncestor (edgeBallEmbedding m k (e (b,v))) (edgeBallEmbedding m k (e (b,w))) ↔
        RegularTreeAncestor (edgeBallEmbedding m k (b,v)) (edgeBallEmbedding m k (b,w)) at h
      rw [← edgeBallGraphIso_branch_pair m k e he b v,← edgeBallGraphIso_branch_pair m k e he b w,
        edgeBallEmbedding_half_ancestor,edgeBallEmbedding_half_ancestor] at h
      exact h
  choose g hg using hex
  refine ⟨g,?_⟩
  rintro ⟨b,v⟩
  change (b,branchAutomorphism (m+1) k (g b) v)=e (b,v)
  rw [hg b]
  exact edgeBallGraphIso_branch_pair m k e he b v

end GaussianWave.BS
