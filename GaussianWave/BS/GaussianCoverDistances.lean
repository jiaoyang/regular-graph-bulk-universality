import GaussianWave.BS.EdgeCoverGeometry
import GaussianWave.BS.GaussianVertexBallKernel
import GaussianWave.BS.GaussianEdgeBallKernel

/-! Literal overlap embeddings preserve the reference kernel distance. -/
noncomputable section
namespace GaussianWave.BS

@[simp] theorem branchDepth_inclusion (q k : ℕ) (v : BranchVertex q k) :
    branchDepth q (k + 1) (branchVertexInclusion q k v) = branchDepth q k v := by
  induction k with
  | zero => rfl
  | succ k ih =>
    cases v with
    | inl u => rfl
    | inr av => exact congrArg (· + 1) (ih av.2)

@[simp] theorem branchDepth_inl (q k : ℕ) (u : Unit) :
    branchDepth q (k + 1) (Sum.inl u) = 0 := rfl

@[simp] theorem branchDepth_inr (q k : ℕ) (av : Fin q × BranchVertex q k) :
    branchDepth q (k + 1) (Sum.inr av) = branchDepth q k av.2 + 1 := rfl

@[simp] theorem branchDistance_inl_inl (q k : ℕ) (u v : Unit) :
    branchDistance q (k + 1) (Sum.inl u) (Sum.inl v) = 0 := rfl

@[simp] theorem branchDistance_inl_inr (q k : ℕ) (u : Unit) (av : Fin q × BranchVertex q k) :
    branchDistance q (k + 1) (Sum.inl u) (Sum.inr av) = branchDepth q k av.2 + 1 := rfl

@[simp] theorem branchDistance_inr_inl (q k : ℕ) (av : Fin q × BranchVertex q k) (u : Unit) :
    branchDistance q (k + 1) (Sum.inr av) (Sum.inl u) = branchDepth q k av.2 + 1 := rfl

@[simp] theorem branchDistance_inr_inr (q k : ℕ) (av bv : Fin q × BranchVertex q k) :
    branchDistance q (k + 1) (Sum.inr av) (Sum.inr bv) =
      if av.1 = bv.1 then branchDistance q k av.2 bv.2
        else branchDepth q k av.2 + branchDepth q k bv.2 + 2 := rfl

@[simp] theorem branchDistance_inclusion (q k : ℕ) (v w : BranchVertex q k) :
    branchDistance q (k + 1) (branchVertexInclusion q k v) (branchVertexInclusion q k w) =
      branchDistance q k v w := by
  induction k with
  | zero => rfl
  | succ k ih =>
    cases v <;> cases w <;>
      simp only [branchVertexInclusion, Sum.elim_inl, Sum.elim_inr,
        branchDistance_inl_inl, branchDistance_inl_inr, branchDistance_inr_inl,
        branchDistance_inr_inr, branchDepth_inclusion, ih]

@[simp] theorem branchDistance_root_left (q k : ℕ) (v : BranchVertex q k) :
    branchDistance q k (branchRoot q k) v = branchDepth q k v := by
  cases k with
  | zero => rfl
  | succ k => cases v <;> rfl

@[simp] theorem branchDistance_root_right (q k : ℕ) (v : BranchVertex q k) :
    branchDistance q k v (branchRoot q k) = branchDepth q k v := by
  cases k with
  | zero => rfl
  | succ k => cases v <;> rfl

theorem edgeInVertexCover_distance (m k : ℕ) (a : Fin (m + 2))
    (v w : EdgeBallVertex (m + 2) (k + 1)) :
    vertexBallDistance m (k + 1) (edgeInVertexCover m k a v) (edgeInVertexCover m k a w) =
      edgeBallDistance m (k + 1) v w := by
  rcases v with ⟨b, v⟩
  rcases w with ⟨c, w⟩
  cases b <;> cases c
  · cases v <;> cases w <;>
      simp [edgeInVertexCover, edgeBallDistance, vertexBallDistance,
        branchDepth_inclusion, branchDistance_inclusion,
        Fin.succAbove_right_inj]
  · cases v <;>
      simp [edgeInVertexCover, edgeBallDistance, vertexBallDistance,
        branchDepth_inclusion, Fin.succAbove_ne, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> omega
  · cases w <;>
      simp [edgeInVertexCover, edgeBallDistance, vertexBallDistance,
        branchDepth_inclusion, Fin.ne_succAbove, Nat.add_assoc]
  · simp [edgeInVertexCover, edgeBallDistance, vertexBallDistance]

theorem vertexInEdgeCover_distance (m k : ℕ) (b : Bool)
    (v w : VertexBallVertex (m + 2) k) :
    edgeBallDistance m (k + 1) (vertexInEdgeCover m k b v) (vertexInEdgeCover m k b w) =
      vertexBallDistance m k v w := by
  cases v with
  | inl u =>
    cases w with
    | inl u => simp [vertexInEdgeCover, edgeBallDistance, vertexBallDistance]
    | inr av =>
      rcases av with ⟨a, v⟩
      cases a using Fin.cases <;> cases b <;>
        simp [vertexInEdgeCover, edgeBallDistance,
          vertexBallDistance, branchDepth_inclusion]
  | inr av =>
    cases w with
    | inl u =>
      rcases av with ⟨a, v⟩
      cases a using Fin.cases <;> cases b <;>
        simp [vertexInEdgeCover, edgeBallDistance,
          vertexBallDistance, branchDepth_inclusion]
    | inr cv =>
      rcases av with ⟨a, v⟩
      rcases cv with ⟨a', w⟩
      cases a using Fin.cases <;> cases a' using Fin.cases <;> cases b <;>
        simp [vertexInEdgeCover, edgeBallDistance, vertexBallDistance,
          branchDepth_inclusion, branchDistance_inclusion, Nat.add_assoc, eq_comm] <;> omega

end GaussianWave.BS
