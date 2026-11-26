import GaussianWave.BS.EdgeCoverGeometry
import GaussianWave.BS.EdgeBallEmbedding
import GaussianWave.BS.InvariantProcessMoments

/-! Actual global automorphisms realizing every literal overlap window. -/
noncomputable section
open scoped Classical
namespace GaussianWave.BS

def rootNeighborPermutation {m : ℕ} (a : Fin (m + 2)) : Equiv.Perm (Fin (m + 2)) :=
  Equiv.ofBijective (Fin.cases a (fun j => a.succAbove j)) (by
    constructor
    · intro i j h
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => rfl
        | succ j => exact False.elim (Fin.succAbove_ne a j h.symm)
      | succ i =>
        cases j using Fin.cases with
        | zero => exact False.elim (Fin.succAbove_ne a i h)
        | succ j => exact congrArg Fin.succ (Fin.succAbove_right_injective h)
    · intro b
      by_cases h : b = a
      · exact ⟨0, h.symm⟩
      · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq h
        exact ⟨j.succ, hj⟩)

@[simp] theorem rootNeighborPermutation_zero {m : ℕ} (a : Fin (m + 2)) :
    rootNeighborPermutation a 0 = a := rfl

@[simp] theorem rootNeighborPermutation_succ {m : ℕ} (a : Fin (m + 2)) (j : Fin (m + 1)) :
    rootNeighborPermutation a j.succ = a.succAbove j := rfl

theorem edgeInVertexCover_embedding (m k : ℕ) (a : Fin (m + 2))
    (v : EdgeBallVertex (m + 2) (k + 1)) :
    vertexBallEmbedding (m + 2) (k + 1) (edgeInVertexCover m k a v) =
      regularTreeRootPermutation (m + 2) (rootNeighborPermutation a) (edgeBallEmbedding m (k + 1) v) := by
  rcases v with ⟨b, v⟩
  cases b
  · cases v with
    | inl u => rfl
    | inr jv =>
      simp only [edgeInVertexCover, Bool.false_eq_true, if_false, Sum.elim_inr,
        vertexBallEmbedding, edgeBallEmbedding, branchPath, List.reverse_cons,
        treeHalfDecode_false_append, regularTreeRootPermutation_some, rootNeighborPermutation_succ,
        branchPath_inclusion]
      erw [regularTreeRootPermutation_some, rootNeighborPermutation_succ, branchPath_inclusion]
      rfl
  · simp only [edgeInVertexCover, if_true, vertexBallEmbedding, edgeBallEmbedding,
      treeHalfDecode_true, regularTreeRootPermutation_some, rootNeighborPermutation_zero]
    erw [regularTreeRootPermutation_some, rootNeighborPermutation_zero]
    rfl

theorem vertexInEdgeCover_false_embedding (m k : ℕ) (v : VertexBallVertex (m + 2) k) :
    edgeBallEmbedding m (k + 1) (vertexInEdgeCover m k false v) =
      vertexBallEmbedding (m + 2) k v := by
  cases v with
  | inl u => rfl
  | inr av =>
    rcases av with ⟨a, v⟩
    cases a using Fin.cases <;>
      simp [vertexInEdgeCover, edgeBallEmbedding, vertexBallEmbedding, branchPath,
        List.reverse_cons, treeHalfDecode_false_append, branchPath_inclusion]

theorem vertexInEdgeCover_true_reverse (m k : ℕ) (v : VertexBallVertex (m + 2) k) :
    vertexInEdgeCover m k true v = edgeBallReverse m (k + 1) (vertexInEdgeCover m k false v) := by
  cases v with
  | inl u => rfl
  | inr av =>
    rcases av with ⟨a, v⟩
    cases a using Fin.cases <;> rfl

theorem vertexInEdgeCover_true_embedding (m k : ℕ) (v : VertexBallVertex (m + 2) k) :
    edgeBallEmbedding m (k + 1) (vertexInEdgeCover m k true v) =
      regularTreeEdgeFlip (m + 1) (vertexBallEmbedding (m + 2) k v) := by
  rw [vertexInEdgeCover_true_reverse, ← edgeBallEmbedding_reverse, vertexInEdgeCover_false_embedding]

theorem edgeBallEmbedding_inclusion (m k : ℕ) (v : EdgeBallVertex (m + 2) k) :
    edgeBallEmbedding m (k + 1) (edgeBallInclusion m k v) = edgeBallEmbedding m k v := by
  change treeHalfDecode (m + 1) (v.1, (branchPath (m + 1) (k + 1)
    (branchVertexInclusion (m + 1) k v.2)).reverse) = _
  rw [branchPath_inclusion]
  rfl

end GaussianWave.BS
