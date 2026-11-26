import GeneralizedBulk.Graph.ExteriorSwitching

/-! The actual accepted graph switch is a rank-at-most-two perturbation. -/
noncomputable section
open scoped BigOperators Classical
namespace GeneralizedBulk.Graph
open Exterior
attribute [local instance] outsideFintype

def switchRankLeft : Matrix (Fin 4) (Fin 2) ℂ := !![0, -1; -1, 0; 0, 1; 1, 0]
def switchRankRight : Matrix (Fin 2) (Fin 4) ℂ := !![1, 0, -1, 0; 0, 1, 0, -1]

theorem switchIncrement_rank_factor :
    (GeneralizedSwitching.switchIncrement : Mat) = switchRankLeft * switchRankRight := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [GeneralizedSwitching.switchIncrement, GeneralizedSwitching.endpointPermutation,
      GeneralizedSwitching.edgeMatrix, switchRankLeft, switchRankRight,
      Matrix.mul_apply, Fin.sum_univ_succ]

theorem switchIncrement_rank_le_two : (GeneralizedSwitching.switchIncrement : Mat).rank ≤ 2 := by
  rw [switchIncrement_rank_factor]
  exact (Matrix.rank_mul_le_left _ _).trans
    (by simpa using Matrix.rank_le_card_width switchRankLeft)

/-- The graph perturbation has only the literal switching increment in its
selected-boundary block; every coupling and outside block is zero. -/
theorem switchGraph_adjacency_difference_block
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (e : Fin 4 → V)
    (he : Function.Injective e) (h : Alternating G e) :
    (((switchGraph G e).adjMatrix ℂ) - G.adjMatrix ℂ).submatrix (boundaryEquiv e he) (boundaryEquiv e he) =
      Matrix.fromBlocks (GeneralizedSwitching.switchIncrement : Mat)
        (0 : Matrix (Fin 4) (Outside e) ℂ) (0 : Matrix (Outside e) (Fin 4) ℂ)
          (0 : Matrix (Outside e) (Outside e) ℂ) := by
  calc
    _ = (((switchGraph G e).adjMatrix ℂ).submatrix (boundaryEquiv e he) (boundaryEquiv e he)) -
        ((G.adjMatrix ℂ).submatrix (boundaryEquiv e he) (boundaryEquiv e he)) := rfl
    _ = _ := by
      rw [boundary_reindex, boundary_reindex, switchGraph_boundary_adjacency G e he h,
        switchGraph_coupling_boundary, switchGraph_coupling_outside, switchGraph_outsideMinor]
      ext a b
      cases a <;> cases b <;>
        simp [Matrix.sub_apply, Matrix.add_apply, Matrix.fromBlocks]

/-- Accepted finite switching is a genuine rank-two perturbation, regardless
of the graph size. -/
theorem switchGraph_adjacency_rank_le_two
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (e : Fin 4 → V)
    (he : Function.Injective e) (h : Alternating G e) :
    (((switchGraph G e).adjMatrix ℂ) - G.adjMatrix ℂ).rank ≤ 2 := by
  rw [← Matrix.rank_submatrix _ (boundaryEquiv e he) (boundaryEquiv e he),
    switchGraph_adjacency_difference_block G e he h]
  have hfactor : Matrix.fromBlocks (GeneralizedSwitching.switchIncrement : Mat)
      (0 : Matrix (Fin 4) (Outside e) ℂ) (0 : Matrix (Outside e) (Fin 4) ℂ)
      (0 : Matrix (Outside e) (Outside e) ℂ) =
    Matrix.fromRows switchRankLeft (0 : Matrix (Outside e) (Fin 2) ℂ) *
      Matrix.fromCols switchRankRight (0 : Matrix (Fin 2) (Outside e) ℂ) := by
    rw [Matrix.fromRows_mul_fromCols, ← switchIncrement_rank_factor]
    simp only [Matrix.mul_zero, Matrix.zero_mul]
  rw [hfactor]
  exact (Matrix.rank_mul_le_left _ _).trans
    (by simpa using (Matrix.rank_le_card_width
      (Matrix.fromRows switchRankLeft (0 : Matrix (Outside e) (Fin 2) ℂ))))

end GeneralizedBulk.Graph
