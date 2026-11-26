import GaussianWave.BS.InnovationEntropyCoordinates
import GaussianWave.BS.LocalEdgeChart
import GaussianWave.BS.LocalVertexChart
import GaussianWave.BS.InnovationRelativeSSA

/-! Actual whole-channel overlap chart maps.  The maps retain every channel
at each spatial site and impose no independence of source channels. -/
noncomputable section
namespace GaussianWave.BS

def channelSumEquiv (κ I J : Type*) : (κ × (I ⊕ J)) ≃ ((κ × I) ⊕ (κ × J)) where
  toFun p := Sum.elim (fun i => Sum.inl (p.1, i)) (fun j => Sum.inr (p.1, j)) p.2
  invFun := Sum.elim (fun p => (p.1, Sum.inl p.2)) (fun p => (p.1, Sum.inr p.2))
  left_inv p := by cases p with | mk a j => cases j <;> rfl
  right_inv p := by cases p <;> rfl

def coloredSumLinearEquiv (κ : Type*) {I J K : Type*}
    (e : ((I ⊕ J) → ℝ) ≃ₗ[ℝ] (K → ℝ)) :
    (((κ × I) ⊕ (κ × J)) → ℝ) ≃ₗ[ℝ] ((κ × K) → ℝ) :=
  (coordinateReindexLinearEquiv (channelSumEquiv κ I J).symm).trans (channelwiseLinearEquiv κ e)

theorem coloredSumLinearEquiv_apply (κ : Type*) {I J K : Type*}
    (e : ((I ⊕ J) → ℝ) ≃ₗ[ℝ] (K → ℝ))
    (z : ((κ × I) ⊕ (κ × J)) → ℝ) (a : κ) (j : K) :
    coloredSumLinearEquiv κ e z (a, j) =
      e (Sum.elim (fun i => z (Sum.inl (a, i))) (fun i => z (Sum.inr (a, i)))) j := by
  change e (fun i => z (channelSumEquiv κ I J (a, i))) j = _
  apply congrArg (fun f => e f j)
  funext i
  cases i <;> rfl

def localEdgeInnovationEquiv (m k : ℕ) (energy : ℝ) (hne : energy ≠ (m + 2 : ℝ))
    (a : Fin (m + 2)) :
    (LocalEdgeInnovation m k → ℝ) ≃ₗ[ℝ] (EdgeBallInnovation (m + 2) (k + 1) → ℝ) :=
  (localEdgeSolutionEquiv m k energy hne a).trans (edgeBallSolutionEquiv m (k + 1) energy).symm

def localVertexInnovationEquiv (m k : ℕ) (energy : ℝ) (hne : energy ≠ (m + 2 : ℝ))
    (b : Bool) :
    (LocalVertexInnovation m k → ℝ) ≃ₗ[ℝ] (VertexBallInnovation (m + 2) k → ℝ) :=
  (localVertexSolutionEquiv m k energy hne b).trans (vertexBallSolutionEquiv m k energy).symm

theorem edgeBallBuild_localEdgeInnovationEquiv (m k : ℕ) (energy : ℝ)
    (hne : energy ≠ (m + 2 : ℝ)) (a : Fin (m + 2)) (z : LocalEdgeInnovation m k → ℝ) :
    edgeBallBuild m (k + 1) energy (localEdgeInnovationEquiv m k energy hne a z) =
      localEdgeReconstruction m k energy a z :=
  congrArg Subtype.val ((edgeBallSolutionEquiv m (k + 1) energy).apply_symm_apply
    (localEdgeSolutionEquiv m k energy hne a z))

theorem vertexBallBuild_localVertexInnovationEquiv (m k : ℕ) (energy : ℝ)
    (hne : energy ≠ (m + 2 : ℝ)) (b : Bool) (z : LocalVertexInnovation m k → ℝ) :
    vertexBallBuild m k energy (localVertexInnovationEquiv m k energy hne b z) =
      localVertexReconstruction m k energy b z :=
  congrArg Subtype.val ((vertexBallSolutionEquiv m k energy).apply_symm_apply
    (localVertexSolutionEquiv m k energy hne b z))

def coloredLocalEdgeInnovationEquiv (κ : Type*) (m k : ℕ) (energy : ℝ)
    (hne : energy ≠ (m + 2 : ℝ)) (a : Fin (m + 2)) :=
  coloredSumLinearEquiv κ (localEdgeInnovationEquiv m k energy hne a)

def coloredLocalVertexInnovationEquiv (κ : Type*) (m k : ℕ) (energy : ℝ)
    (hne : energy ≠ (m + 2 : ℝ)) (b : Bool) :=
  coloredSumLinearEquiv κ (localVertexInnovationEquiv m k energy hne b)

theorem coloredLocalProjection_channel (κ A : Type*) (m k : ℕ) (a : A)
    (x : (κ × ForestInnovation A m (k + 1)) → ℝ) (c : κ) :
    Sum.elim (fun j => (coloredForestSplitCoordinates κ A m k x).1 (c, j))
      (fun j => (coloredForestSplitCoordinates κ A m k x).2 a (c, j)) =
      forestLocalProjection A m k a (fun j => x (c, j)) := by
  funext j
  cases j <;> rfl

theorem coloredLocalEdgeInnovationEquiv_projection (κ : Type*) (m k : ℕ) (energy : ℝ)
    (hne : energy ≠ (m + 2 : ℝ)) (a : Fin (m + 2))
    (x : (κ × VertexBallInnovation (m + 2) (k + 1)) → ℝ) (c : κ) :
    (fun j => coloredLocalEdgeInnovationEquiv κ m k energy hne a
      (innovationLocalProjection (coloredForestSplit κ (Fin (m + 2)) m k) a x) (c, j)) =
      localEdgeInnovationEquiv m k energy hne a
        (forestLocalProjection (Fin (m + 2)) m k a (fun j => x (c, j))) := by
  funext j
  rw [coloredLocalEdgeInnovationEquiv, coloredSumLinearEquiv_apply]
  change localEdgeInnovationEquiv m k energy hne a
    (Sum.elim (fun i => (coloredForestSplitCoordinates κ (Fin (m + 2)) m k x).1 (c, i))
      (fun i => (coloredForestSplitCoordinates κ (Fin (m + 2)) m k x).2 a (c, i))) j = _
  rw [coloredLocalProjection_channel]

theorem coloredLocalVertexInnovationEquiv_projection (κ : Type*) (m k : ℕ) (energy : ℝ)
    (hne : energy ≠ (m + 2 : ℝ)) (b : Bool)
    (x : (κ × EdgeBallInnovation (m + 2) (k + 1)) → ℝ) (c : κ) :
    (fun j => coloredLocalVertexInnovationEquiv κ m k energy hne b
      (innovationLocalProjection (coloredForestSplit κ Bool m k) b x) (c, j)) =
      localVertexInnovationEquiv m k energy hne b
        (forestLocalProjection Bool m k b (fun j => x (c, j))) := by
  funext j
  rw [coloredLocalVertexInnovationEquiv, coloredSumLinearEquiv_apply]
  change localVertexInnovationEquiv m k energy hne b
    (Sum.elim (fun i => (coloredForestSplitCoordinates κ Bool m k x).1 (c, i))
      (fun i => (coloredForestSplitCoordinates κ Bool m k x).2 b (c, i))) j = _
  rw [coloredLocalProjection_channel]

theorem colored_edge_window_reconstruction (κ : Type*) (m k : ℕ) (energy : ℝ)
    (hne : energy ≠ (m + 2 : ℝ)) (a : Fin (m + 2))
    (x : (κ × VertexBallInnovation (m + 2) (k + 1)) → ℝ) (c : κ) :
    edgeBallBuild m (k + 1) energy
      (fun j => coloredLocalEdgeInnovationEquiv κ m k energy hne a
        (innovationLocalProjection (coloredForestSplit κ (Fin (m + 2)) m k) a x) (c, j)) =
      fun v => vertexBallBuild m (k + 1) energy (fun j => x (c, j)) (edgeInVertexCover m k a v) := by
  rw [coloredLocalEdgeInnovationEquiv_projection, edgeBallBuild_localEdgeInnovationEquiv,
    localEdgeReconstruction_projection]
  rfl

theorem colored_vertex_window_reconstruction (κ : Type*) (m k : ℕ) (energy : ℝ)
    (hne : energy ≠ (m + 2 : ℝ)) (b : Bool)
    (x : (κ × EdgeBallInnovation (m + 2) (k + 1)) → ℝ) (c : κ) :
    vertexBallBuild m k energy
      (fun j => coloredLocalVertexInnovationEquiv κ m k energy hne b
        (innovationLocalProjection (coloredForestSplit κ Bool m k) b x) (c, j)) =
      fun v => edgeBallBuild m (k + 1) energy (fun j => x (c, j)) (vertexInEdgeCover m k b v) := by
  rw [coloredLocalVertexInnovationEquiv_projection, vertexBallBuild_localVertexInnovationEquiv,
    localVertexReconstruction_projection]
  rfl

end GaussianWave.BS
