import GaussianWave.BS.FiniteCoverSampling

/-! The actual finite rooted-tree automorphism group is the recursive
wreath product of child permutations. Its faithful permutation action and
cardinality are constructed explicitly for marker entropy cancellation. -/
noncomputable section
open scoped BigOperators Classical
namespace GaussianWave.BS

def branchCoverOrderingGroupDef (q : ℕ) : (k : ℕ) → Group (BranchCoverOrdering q k)
  | 0 => inferInstanceAs (Group Unit)
  | k + 1 => by
      letI : Group (BranchCoverOrdering q k) := branchCoverOrderingGroupDef q k
      letI : Mul (BranchCoverOrdering q (k + 1)) :=
        ⟨fun x y => (x.1 * y.1, fun j => x.2 (y.1 j) * y.2 j)⟩
      letI : One (BranchCoverOrdering q (k + 1)) := ⟨(1, fun _ => 1)⟩
      letI : Inv (BranchCoverOrdering q (k + 1)) :=
        ⟨fun x => (x.1⁻¹, fun j => (x.2 (x.1⁻¹ j))⁻¹)⟩
      apply Group.ofLeftAxioms
      · intro x y z
        apply Prod.ext
        · exact mul_assoc x.1 y.1 z.1
        · funext j
          change (x.2 (y.1 (z.1 j)) * y.2 (z.1 j)) * z.2 j =
            x.2 (y.1 (z.1 j)) * (y.2 (z.1 j) * z.2 j)
          exact mul_assoc _ _ _
      · intro x
        apply Prod.ext
        · exact one_mul x.1
        · funext j
          exact one_mul _
      · intro x
        apply Prod.ext
        · exact inv_mul_cancel x.1
        · funext j
          change (x.2 (x.1⁻¹ (x.1 j)))⁻¹ * x.2 j = 1
          rw [Equiv.Perm.inv_apply_self, inv_mul_cancel]

instance branchCoverOrderingGroup (q k : ℕ) : Group (BranchCoverOrdering q k) :=
  branchCoverOrderingGroupDef q k

@[simp] theorem branchOrder_mul_first (q k : ℕ) (g h : BranchCoverOrdering q (k + 1)) :
    (g * h).1 = g.1 * h.1 := rfl

@[simp] theorem branchOrder_mul_child (q k : ℕ) (g h : BranchCoverOrdering q (k + 1)) (j : Fin q) :
    (g * h).2 j = g.2 (h.1 j) * h.2 j := rfl

@[simp] theorem branchOrder_one_first (q k : ℕ) : (1 : BranchCoverOrdering q (k + 1)).1 = 1 := rfl
@[simp] theorem branchOrder_one_child (q k : ℕ) (j : Fin q) : (1 : BranchCoverOrdering q (k + 1)).2 j = 1 := rfl

def branchAutomorphism (q : ℕ) : (k : ℕ) → BranchCoverOrdering q k → Equiv.Perm (BranchVertex q k)
  | 0, _ => Equiv.refl _
  | k + 1, g =>
    { toFun := Sum.elim Sum.inl (fun av => Sum.inr (g.1 av.1, branchAutomorphism q k (g.2 av.1) av.2))
      invFun := Sum.elim Sum.inl (fun av => Sum.inr (g.1.symm av.1,
        (branchAutomorphism q k (g.2 (g.1.symm av.1))).symm av.2))
      left_inv := by
        intro v
        cases v with
        | inl u => rfl
        | inr av => simp only [Sum.elim_inr, Equiv.symm_apply_apply, Prod.mk.eta]
      right_inv := by
        intro v
        cases v with
        | inl u => rfl
        | inr av => simp only [Sum.elim_inr, Equiv.apply_symm_apply, Prod.mk.eta] }

@[simp] theorem branchAutomorphism_root (q k : ℕ) (g : BranchCoverOrdering q k) :
    branchAutomorphism q k g (branchRoot q k) = branchRoot q k := by
  cases k <;> rfl

theorem branchAutomorphism_one (q k : ℕ) : branchAutomorphism q k 1 = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      apply Equiv.ext
      intro v
      cases v with
      | inl u => rfl
      | inr av =>
          change Sum.inr ((1 : Equiv.Perm (Fin q)) av.1, branchAutomorphism q k 1 av.2) = Sum.inr av
          rw [ih]
          rfl

theorem branchAutomorphism_mul (q k : ℕ) (g h : BranchCoverOrdering q k) :
    branchAutomorphism q k (g * h) = branchAutomorphism q k g * branchAutomorphism q k h := by
  induction k with
  | zero => rfl
  | succ k ih =>
      apply Equiv.ext
      intro v
      cases v with
      | inl u => rfl
      | inr av =>
          change Sum.inr ((g.1 * h.1) av.1, branchAutomorphism q k (g.2 (h.1 av.1) * h.2 av.1) av.2) =
            Sum.inr (g.1 (h.1 av.1), branchAutomorphism q k (g.2 (h.1 av.1))
              (branchAutomorphism q k (h.2 av.1) av.2))
          rw [ih]
          rfl

theorem branchAutomorphism_injective (q k : ℕ) : Function.Injective (branchAutomorphism q k) := by
  induction k with
  | zero => intro g h he; cases g; cases h; rfl
  | succ k ih =>
      intro g h he
      have hp : g.1 = h.1 := by
        apply Equiv.ext
        intro j
        have hh := congrArg (fun e : Equiv.Perm (BranchVertex q (k + 1)) =>
          e (Sum.inr (j, branchRoot q k))) he
        simp only [branchAutomorphism, Sum.elim_inr, branchAutomorphism_root] at hh
        exact congrArg Prod.fst (Sum.inr.inj hh)
      apply Prod.ext hp
      funext j
      apply ih
      apply Equiv.ext
      intro v
      have hh := congrArg (fun e : Equiv.Perm (BranchVertex q (k + 1)) => e (Sum.inr (j, v))) he
      exact congrArg Prod.snd (Sum.inr.inj hh)

def branchAutomorphismHom (q k : ℕ) : BranchCoverOrdering q k →* Equiv.Perm (BranchVertex q k) where
  toFun := branchAutomorphism q k
  map_one' := branchAutomorphism_one q k
  map_mul' := branchAutomorphism_mul q k

instance branchAutomorphismMulAction (q k : ℕ) : MulAction (BranchCoverOrdering q k) (BranchVertex q k) :=
  MulAction.compHom _ (branchAutomorphismHom q k)

instance branchAutomorphismFaithfulSMul (q k : ℕ) : FaithfulSMul (BranchCoverOrdering q k) (BranchVertex q k) := by
  constructor
  intro g h he
  apply branchAutomorphism_injective q k
  exact Equiv.ext he

theorem card_branchCoverOrdering (q : ℕ) : ∀ k,
    Fintype.card (BranchCoverOrdering q (k + 1)) =
      q.factorial * Fintype.card (BranchCoverOrdering q k) ^ q := by
  intro k
  simp only [BranchCoverOrdering, Fintype.card_prod, Fintype.card_perm, Fintype.card_fin, Fintype.card_fun]

end GaussianWave.BS
