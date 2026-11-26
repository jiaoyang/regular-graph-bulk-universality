import GaussianWave.BS.TreeAutomorphisms

/-! The recursive branch permutation group contains every permutation of
the literal finite rooted tree preserving its rooted prefix order and depth.
These are the ordinary combinatorial data of a rooted tree isomorphism. -/
noncomputable section
open scoped Classical
set_option maxHeartbeats 1200000
namespace GaussianWave.BS

@[simp] theorem branchPath_root (q k : ℕ) : branchPath q k (branchRoot q k)=[] := by
  cases k <;> rfl

theorem branchPath_eq_nil_iff (q k : ℕ) (v : BranchVertex q k) :
    branchPath q k v=[] ↔ v=branchRoot q k := by
  constructor
  · intro h
    exact branchPath_injective q k (h.trans (branchPath_root q k).symm)
  · rintro rfl
    exact branchPath_root q k

/-- Exact wreath-product decomposition of every depth and prefix preserving
permutation; no group-size or automorphism classification premise occurs. -/
theorem exists_branchAutomorphism_of_prefix (q k : ℕ)
    (e : Equiv.Perm (BranchVertex q k))
    (hdepth : ∀ v,(branchPath q k (e v)).length=(branchPath q k v).length)
    (hprefix : ∀ v w,
      (branchPath q k (e v)).IsPrefix (branchPath q k (e w)) ↔
        (branchPath q k v).IsPrefix (branchPath q k w)) :
    ∃ g : BranchCoverOrdering q k,branchAutomorphism q k g=e := by
  induction k with
  | zero =>
      refine ⟨(),?_⟩
      apply Equiv.ext
      intro v
      exact @Subsingleton.elim Unit inferInstance _ _
  | succ k ih =>
      have hroot : e (branchRoot q (k+1))=branchRoot q (k+1) := by
        apply (branchPath_eq_nil_iff q (k+1) _).mp
        apply List.length_eq_zero_iff.mp
        simpa only [branchPath_root,List.length_nil] using hdepth (branchRoot q (k+1))
      have htop (a : Fin q) : ∃ b : Fin q,
          e (Sum.inr (a,branchRoot q k))=Sum.inr (b,branchRoot q k) := by
        have hh := hdepth (Sum.inr (a,branchRoot q k))
        cases he : e (Sum.inr (a,branchRoot q k)) with
        | inl u => simp only [he,branchPath,branchPath_root,List.length_nil,List.length_cons] at hh; omega
        | inr bv =>
            refine ⟨bv.1,?_⟩
            have hb : bv.2=branchRoot q k := by
              apply (branchPath_eq_nil_iff q k _).mp
              apply List.length_eq_zero_iff.mp
              simp only [he,branchPath,branchPath_root,List.length_nil,List.length_cons] at hh
              omega
            exact congrArg Sum.inr (Prod.ext rfl hb)
      let σ (a : Fin q) := (htop a).choose
      have hσ (a : Fin q) : e (Sum.inr (a,branchRoot q k))=Sum.inr (σ a,branchRoot q k) :=
        (htop a).choose_spec
      have hσinj : Function.Injective σ := by
        intro a b hab
        have he := e.injective ((hσ a).trans ((congrArg (fun j => Sum.inr (j,branchRoot q k)) hab).trans (hσ b).symm))
        exact congrArg Prod.fst (Sum.inr.inj he)
      let perm : Equiv.Perm (Fin q) := Equiv.ofBijective σ ⟨hσinj,Finite.surjective_of_injective hσinj⟩
      have hchild (a : Fin q) (v : BranchVertex q k) : ∃ w : BranchVertex q k,
          e (Sum.inr (a,v))=Sum.inr (σ a,w) := by
        have hp : (branchPath q (k+1) (e (Sum.inr (a,branchRoot q k)))).IsPrefix
            (branchPath q (k+1) (e (Sum.inr (a,v)))) :=
          (hprefix _ _).mpr (by simp only [branchPath,branchPath_root]; exact ⟨branchPath q k v,rfl⟩)
        rw [hσ] at hp
        cases he : e (Sum.inr (a,v)) with
        | inl u =>
            simp only [he,branchPath,branchPath_root,List.prefix_nil] at hp
            exact False.elim (List.noConfusion hp)
        | inr bw =>
            have hb : σ a=bw.1 := by
              simpa only [he,branchPath,branchPath_root,List.cons_prefix_cons,true_and,
                List.nil_prefix,and_true] using hp
            exact ⟨bw.2,by simpa only [hb] using he⟩
      let τ (a : Fin q) (v : BranchVertex q k) := (hchild a v).choose
      have hτ (a : Fin q) (v : BranchVertex q k) : e (Sum.inr (a,v))=Sum.inr (σ a,τ a v) :=
        (hchild a v).choose_spec
      have hτinj (a : Fin q) : Function.Injective (τ a) := by
        intro v w hvw
        have he := e.injective ((hτ a v).trans ((congrArg (fun z => Sum.inr (σ a,z)) hvw).trans (hτ a w).symm))
        exact congrArg Prod.snd (Sum.inr.inj he)
      let subperm (a : Fin q) : Equiv.Perm (BranchVertex q k) :=
        Equiv.ofBijective (τ a) ⟨hτinj a,Finite.surjective_of_injective (hτinj a)⟩
      have hsdepth (a : Fin q) (v : BranchVertex q k) :
          (branchPath q k (subperm a v)).length=(branchPath q k v).length := by
        have hh := hdepth (Sum.inr (a,v))
        rw [hτ] at hh
        simpa only [branchPath,List.length_cons,Nat.add_right_cancel_iff] using hh
      have hsprefix (a : Fin q) (v w : BranchVertex q k) :
          (branchPath q k (subperm a v)).IsPrefix (branchPath q k (subperm a w)) ↔
            (branchPath q k v).IsPrefix (branchPath q k w) := by
        have hh := hprefix (Sum.inr (a,v)) (Sum.inr (a,w))
        rw [hτ,hτ] at hh
        simpa only [branchPath,List.prefix_cons_inj] using hh
      choose g hg using fun a => ih (subperm a) (hsdepth a) (hsprefix a)
      refine ⟨(perm,g),?_⟩
      apply Equiv.ext
      intro v
      cases v with
      | inl u => cases u; exact hroot.symm
      | inr av =>
          change Sum.inr (σ av.1,branchAutomorphism q k (g av.1) av.2)=e (Sum.inr av)
          rw [hg,hτ]
          rfl

end GaussianWave.BS
