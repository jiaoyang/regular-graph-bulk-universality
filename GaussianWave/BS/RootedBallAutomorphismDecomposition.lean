import GaussianWave.BS.BranchAutomorphismDecomposition
import GaussianWave.BS.TreeAncestor

/-! Heterogeneous top-root decomposition: the root can have `|A|` children
while every further branch is `q`-ary. This is the actual finite vertex-ball
geometry with `A=Fin d`, `q=d-1`. -/
noncomputable section
open scoped Classical
set_option maxHeartbeats 1400000
namespace GaussianWave.BS

def rootedBranchDepth {A : Type*} (q k : ℕ) : Unit ⊕ (A × BranchVertex q k) → ℕ
  | Sum.inl _ => 0
  | Sum.inr av => (branchPath q k av.2).length+1

def RootedBranchAncestor {A : Type*} (q k : ℕ) :
    (Unit ⊕ (A × BranchVertex q k)) → (Unit ⊕ (A × BranchVertex q k)) → Prop
  | Sum.inl _,_ => True
  | Sum.inr _,Sum.inl _ => False
  | Sum.inr av,Sum.inr bw => av.1=bw.1 ∧ (branchPath q k av.2).IsPrefix (branchPath q k bw.2)

def rootedBranchAutomorphism {A : Type*} (q k : ℕ) (σ : Equiv.Perm A)
    (g : A → BranchCoverOrdering q k) : Equiv.Perm (Unit ⊕ (A × BranchVertex q k)) where
  toFun := Sum.elim Sum.inl (fun av => Sum.inr (σ av.1,branchAutomorphism q k (g av.1) av.2))
  invFun := Sum.elim Sum.inl (fun av => Sum.inr (σ.symm av.1,
    (branchAutomorphism q k (g (σ.symm av.1))).symm av.2))
  left_inv := by
    intro v
    cases v with
    | inl u => rfl
    | inr av => simp only [Sum.elim_inr,Equiv.symm_apply_apply,Prod.mk.eta]
  right_inv := by
    intro v
    cases v with
    | inl u => rfl
    | inr av => simp only [Sum.elim_inr,Equiv.apply_symm_apply,Prod.mk.eta]

theorem exists_rootedBranchAutomorphism {A : Type*} [Fintype A] (q k : ℕ)
    (e : Equiv.Perm (Unit ⊕ (A × BranchVertex q k)))
    (hdepth : ∀ v,rootedBranchDepth q k (e v)=rootedBranchDepth q k v)
    (hancestor : ∀ v w,RootedBranchAncestor q k (e v) (e w) ↔ RootedBranchAncestor q k v w) :
    ∃ (σ : Equiv.Perm A) (g : A → BranchCoverOrdering q k),rootedBranchAutomorphism q k σ g=e := by
  have hroot : e (Sum.inl ())=Sum.inl () := by
    have hh := hdepth (Sum.inl ())
    cases he : e (Sum.inl ()) with
    | inl u => cases u; rfl
    | inr av => simp only [he,rootedBranchDepth] at hh; omega
  have htop (a : A) : ∃ b : A,e (Sum.inr (a,branchRoot q k))=Sum.inr (b,branchRoot q k) := by
    have hh := hdepth (Sum.inr (a,branchRoot q k))
    cases he : e (Sum.inr (a,branchRoot q k)) with
    | inl u => simp only [he,rootedBranchDepth,branchPath_root,List.length_nil] at hh; omega
    | inr bv =>
        refine ⟨bv.1,?_⟩
        have hb : bv.2=branchRoot q k := by
          apply (branchPath_eq_nil_iff q k _).mp
          apply List.length_eq_zero_iff.mp
          simp only [he,rootedBranchDepth,branchPath_root,List.length_nil] at hh
          omega
        exact congrArg Sum.inr (Prod.ext rfl hb)
  let σ (a : A) := (htop a).choose
  have hσ (a : A) : e (Sum.inr (a,branchRoot q k))=Sum.inr (σ a,branchRoot q k) := (htop a).choose_spec
  have hσinj : Function.Injective σ := by
    intro a b hab
    have he := e.injective ((hσ a).trans ((congrArg (fun j => Sum.inr (j,branchRoot q k)) hab).trans (hσ b).symm))
    exact congrArg Prod.fst (Sum.inr.inj he)
  let perm : Equiv.Perm A := Equiv.ofBijective σ ⟨hσinj,Finite.surjective_of_injective hσinj⟩
  have hchild (a : A) (v : BranchVertex q k) : ∃ w : BranchVertex q k,
      e (Sum.inr (a,v))=Sum.inr (σ a,w) := by
    have hp : RootedBranchAncestor q k (e (Sum.inr (a,branchRoot q k))) (e (Sum.inr (a,v))) :=
      (hancestor _ _).mpr ⟨rfl,by rw [branchPath_root]; exact List.nil_prefix⟩
    rw [hσ] at hp
    cases he : e (Sum.inr (a,v)) with
    | inl u => rw [he] at hp; exact False.elim hp
    | inr bw =>
        rw [he] at hp
        exact ⟨bw.2,congrArg Sum.inr (Prod.ext hp.1.symm rfl)⟩
  let τ (a : A) (v : BranchVertex q k) := (hchild a v).choose
  have hτ (a : A) (v : BranchVertex q k) : e (Sum.inr (a,v))=Sum.inr (σ a,τ a v) := (hchild a v).choose_spec
  have hτinj (a : A) : Function.Injective (τ a) := by
    intro v w hvw
    have he := e.injective ((hτ a v).trans ((congrArg (fun z => Sum.inr (σ a,z)) hvw).trans (hτ a w).symm))
    exact congrArg Prod.snd (Sum.inr.inj he)
  let subperm (a : A) : Equiv.Perm (BranchVertex q k) :=
    Equiv.ofBijective (τ a) ⟨hτinj a,Finite.surjective_of_injective (hτinj a)⟩
  have hsdepth (a : A) (v : BranchVertex q k) :
      (branchPath q k (subperm a v)).length=(branchPath q k v).length := by
    have hh := hdepth (Sum.inr (a,v))
    rw [hτ] at hh
    simpa only [rootedBranchDepth,Nat.add_right_cancel_iff] using hh
  have hsprefix (a : A) (v w : BranchVertex q k) :
      (branchPath q k (subperm a v)).IsPrefix (branchPath q k (subperm a w)) ↔
        (branchPath q k v).IsPrefix (branchPath q k w) := by
    have hh := hancestor (Sum.inr (a,v)) (Sum.inr (a,w))
    rw [hτ,hτ] at hh
    simpa only [RootedBranchAncestor,true_and] using hh
  choose g hg using fun a => exists_branchAutomorphism_of_prefix q k (subperm a) (hsdepth a) (hsprefix a)
  refine ⟨perm,g,?_⟩
  apply Equiv.ext
  intro v
  cases v with
  | inl u => cases u; exact hroot.symm
  | inr av =>
      change Sum.inr (σ av.1,branchAutomorphism q k (g av.1) av.2)=e (Sum.inr av)
      rw [hg,hτ]
      rfl

theorem regularTreeAncestor_root (d : ℕ) (v : RegularTreeVertex d) :
    RegularTreeAncestor none v := by
  cases v with
  | none => exact ⟨0,rfl⟩
  | some aw =>
      rcases aw with ⟨a,w⟩
      refine ⟨w.length+1,?_⟩
      rw [Function.iterate_succ_apply']
      have h := regularTreeParent_iterate_append a w []
      simp only [List.append_nil] at h
      rw [h]
      rfl

theorem vertexBallEmbedding_depth_eq (d k : ℕ) (v : VertexBallVertex d k) :
    regularTreeDepth (vertexBallEmbedding d k v)=rootedBranchDepth (d-1) k v := by
  cases v with
  | inl u => rfl
  | inr av => simp only [vertexBallEmbedding,regularTreeDepth,rootedBranchDepth,List.length_reverse]

theorem vertexBallEmbedding_ancestor_iff (d k : ℕ) (v w : VertexBallVertex d k) :
    RootedBranchAncestor (d-1) k v w ↔
      RegularTreeAncestor (vertexBallEmbedding d k v) (vertexBallEmbedding d k w) := by
  cases v with
  | inl u => exact ⟨fun _ => regularTreeAncestor_root d _,fun _ => trivial⟩
  | inr av =>
      cases w with
      | inl u =>
          constructor
          · exact False.elim
          · rintro ⟨n,hn⟩
            have hh : (regularTreeParent^[n]) (none : RegularTreeVertex d)=none := Function.iterate_fixed rfl n
            rw [show vertexBallEmbedding d k (Sum.inl u)=none from rfl,hh] at hn
            exact False.elim (Option.noConfusion hn)
      | inr bw =>
          exact (regularTreeAncestor_word_iff av.1 bw.1 (branchPath (d-1) k av.2) (branchPath (d-1) k bw.2)).symm

/-- Every actual rooted automorphism of the countable regular tree agrees
on the finite radius-`k+1` ball with a literal top permutation and recursive
independent branch permutations. -/
theorem exists_rootedRegularTreeRestriction (d k : ℕ)
    (e : regularWordTree d ≃g regularWordTree d) (hroot : e none=none) :
    ∃ (σ : Equiv.Perm (Fin d)) (g : Fin d → BranchCoverOrdering (d-1) k),
      ∀ v : VertexBallVertex d k,e (vertexBallEmbedding d k v)=
        vertexBallEmbedding d k (rootedBranchAutomorphism (d-1) k σ g v) := by
  have hex (v : VertexBallVertex d k) : ∃ w : VertexBallVertex d k,
      vertexBallEmbedding d k w=e (vertexBallEmbedding d k v) := by
    apply Set.mem_range.mp
    rw [vertexBallEmbedding_range]
    change regularTreeDepth (e (vertexBallEmbedding d k v)) ≤ k+1
    rw [regularTreeIso_depth d e hroot]
    exact vertexBallEmbedding_depth d k v
  let f (v : VertexBallVertex d k) := (hex v).choose
  have hf (v : VertexBallVertex d k) : vertexBallEmbedding d k (f v)=e (vertexBallEmbedding d k v) := (hex v).choose_spec
  have hfinj : Function.Injective f := by
    intro v w hvw
    apply vertexBallEmbedding_injective d k
    apply e.injective
    exact (hf v).symm.trans ((congrArg (vertexBallEmbedding d k) hvw).trans (hf w))
  let p : Equiv.Perm (VertexBallVertex d k) := Equiv.ofBijective f ⟨hfinj,Finite.surjective_of_injective hfinj⟩
  have hpdepth (v : VertexBallVertex d k) :
      rootedBranchDepth (d-1) k (p v)=rootedBranchDepth (d-1) k v := by
    rw [← vertexBallEmbedding_depth_eq,← vertexBallEmbedding_depth_eq]
    change regularTreeDepth (vertexBallEmbedding d k (f v))=_
    rw [hf,regularTreeIso_depth d e hroot]
  have hpancestor (v w : VertexBallVertex d k) :
      RootedBranchAncestor (d-1) k (p v) (p w) ↔ RootedBranchAncestor (d-1) k v w := by
    rw [vertexBallEmbedding_ancestor_iff,vertexBallEmbedding_ancestor_iff]
    change RegularTreeAncestor (vertexBallEmbedding d k (f v)) (vertexBallEmbedding d k (f w)) ↔ _
    rw [hf,hf]
    exact regularTreeIso_ancestor d e hroot _ _
  obtain ⟨σ,g,hp⟩ := exists_rootedBranchAutomorphism (d-1) k p hpdepth hpancestor
  refine ⟨σ,g,fun v => ?_⟩
  rw [hp]
  exact (hf v).symm

end GaussianWave.BS
