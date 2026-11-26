import GaussianWave.BS.BranchAutomorphisms

/-! Faithful independent branch actions for the actual star and edge
stabilizer groups. Rooted centers and branch labels are fixed. -/
noncomputable section
open scoped BigOperators Classical

namespace GaussianWave.BS

instance branchFamilyMulAction (A : Type*) (q k : ℕ) :
    MulAction (A → BranchCoverOrdering q k) (A × BranchVertex q k) where
  smul g x := (x.1,g x.1 • x.2)
  one_smul x := by
    rcases x with ⟨a,v⟩
    change (a,((1 : A → BranchCoverOrdering q k) a) • v) = (a,v)
    simp only [Pi.one_apply,one_smul]
  mul_smul g h x := by
    rcases x with ⟨a,v⟩
    change (a,(g*h) a • v) = (a,g a • (h a • v))
    simp only [Pi.mul_apply,mul_smul]

instance branchFamilyFaithfulSMul (A : Type*) (q k : ℕ) :
    FaithfulSMul (A → BranchCoverOrdering q k) (A × BranchVertex q k) where
  eq_of_smul_eq_smul := by
    intro g h he
    funext a
    apply eq_of_smul_eq_smul (α := BranchVertex q k)
    intro v
    exact congrArg Prod.snd (he (a,v))

@[simp] theorem branchFamily_smul_apply {A : Type*} (q k : ℕ)
    (g : A → BranchCoverOrdering q k) (a : A) (v : BranchVertex q k) :
    g • (a,v) = (a,g a • v) := rfl

/-- The canonical center-fixing action is the standard sum action, with the
already constructed independent action on the branch components. -/
theorem branchFixedCenter_mulAction (A : Type*) (q k : ℕ) :
    Nonempty (MulAction (A → BranchCoverOrdering q k) (Unit ⊕ (A × BranchVertex q k))) :=
  ⟨inferInstance⟩

instance branchFixedCenterFaithfulSMul (A : Type*) (q k : ℕ) :
    FaithfulSMul (A → BranchCoverOrdering q k) (Unit ⊕ (A × BranchVertex q k)) := by
  infer_instance

@[simp] theorem branchFixedCenter_smul_root {A : Type*} (q k : ℕ)
    (g : A → BranchCoverOrdering q k) :
    g • (Sum.inl () : Unit ⊕ (A × BranchVertex q k)) = Sum.inl () := rfl

@[simp] theorem branchFixedCenter_smul_branch {A : Type*} (q k : ℕ)
    (g : A → BranchCoverOrdering q k) (a : A) (v : BranchVertex q k) :
    g • (Sum.inr (a,v) : Unit ⊕ (A × BranchVertex q k)) = Sum.inr (a,g a • v) := rfl

abbrev VertexBallStabilizer (d k : ℕ) := Fin d → BranchCoverOrdering (d-1) k
abbrev EdgeBallStabilizer (d k : ℕ) := Bool → BranchCoverOrdering (d-1) k

theorem card_vertexBallStabilizer (d k : ℕ) :
    Fintype.card (VertexBallStabilizer d k) = Fintype.card (BranchCoverOrdering (d-1) k)^d := by
  simp only [VertexBallStabilizer,Fintype.card_fun,Fintype.card_fin]

theorem card_edgeBallStabilizer (d k : ℕ) :
    Fintype.card (EdgeBallStabilizer d k) = Fintype.card (BranchCoverOrdering (d-1) k)^2 := by
  simp only [EdgeBallStabilizer,Fintype.card_fun,Fintype.card_bool]

example (d k : ℕ) : MulAction (VertexBallStabilizer d k) (VertexBallVertex d k) := inferInstance
example (d k : ℕ) : FaithfulSMul (VertexBallStabilizer d k) (VertexBallVertex d k) := inferInstance
example (d k : ℕ) : MulAction (EdgeBallStabilizer d k) (EdgeBallVertex d k) := inferInstance
example (d k : ℕ) : FaithfulSMul (EdgeBallStabilizer d k) (EdgeBallVertex d k) := inferInstance

end GaussianWave.BS
