import GaussianWave.BS.LocalInnovationCoordinates
import GaussianWave.BS.EdgeCoverGeometry

/-!
# Actual local edge-window chart inside vertex-ball innovation coordinates
-/
noncomputable section
open scoped BigOperators
namespace GaussianWave.BS

abbrev LocalEdgeInnovation (m k : ℕ) := ForestLocalInnovation (Fin (m + 2)) m k

theorem vertexBallBuild_agrees_core (m k : ℕ) (energy : ℝ)
    (x y : VertexBallInnovation (m + 2) (k + 1) → ℝ)
    (h : ∀ j, x (vertexInnovationInclusion m k j) = y (vertexInnovationInclusion m k j))
    (v : VertexBallVertex (m + 2) k) :
    vertexBallBuild m (k + 1) energy x (vertexBallInclusion m k v) =
      vertexBallBuild m (k + 1) energy y (vertexBallInclusion m k v) := by
  rw [congrFun (vertexBallBuild_restrict m k energy x) v,
    congrFun (vertexBallBuild_restrict m k energy y) v]
  rw [funext h]

theorem vertexBallBuild_edgeCover_agrees (m k : ℕ) (energy : ℝ) (a : Fin (m + 2))
    (x y : VertexBallInnovation (m + 2) (k + 1) → ℝ)
    (hold : ∀ j, x (vertexInnovationInclusion m k j) = y (vertexInnovationInclusion m k j))
    (hbranch : ∀ j, x (Sum.inr (a, j)) = y (Sum.inr (a, j)))
    (v : EdgeBallVertex (m + 2) (k + 1)) :
    vertexBallBuild m (k + 1) energy x (edgeInVertexCover m k a v) =
      vertexBallBuild m (k + 1) energy y (edgeInVertexCover m k a v) := by
  have hr : vertexInnovationRoot m (k + 1) energy x = vertexInnovationRoot m (k + 1) energy y := by
    unfold vertexInnovationRoot
    congr 1
    apply Finset.sum_congr rfl
    intro b _
    exact hold (Sum.inl b)
  rcases v with ⟨b, v⟩
  cases b
  · cases v with
    | inl u => exact hr
    | inr jv =>
        exact vertexBallBuild_agrees_core m k energy x y hold (Sum.inr (a.succAbove jv.1, jv.2))
  · change branchBuild m (k + 1) energy (vertexInnovationRoot m (k + 1) energy x)
      (vertexInnovationRoot m (k + 1) energy x + x (Sum.inl a)) (fun j => x (Sum.inr (a, j))) v = _
    have ha : x (Sum.inl a) = y (Sum.inl a) := hold (Sum.inl a)
    rw [hr, ha]
    erw [funext hbranch]
    rfl

def edgeCoverRestriction (m k : ℕ) (a : Fin (m + 2)) :
    (VertexBallVertex (m + 2) (k + 1) → ℝ) →ₗ[ℝ] (EdgeBallVertex (m + 2) (k + 1) → ℝ) where
  toFun x := fun v => x (edgeInVertexCover m k a v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def localEdgeReconstruction (m k : ℕ) (energy : ℝ) (a : Fin (m + 2)) :
    (LocalEdgeInnovation m k → ℝ) →ₗ[ℝ] (EdgeBallVertex (m + 2) (k + 1) → ℝ) :=
  (edgeCoverRestriction m k a).comp ((vertexBallBuildLinear m (k + 1) energy).comp
    (forestLocalFill (Fin (m + 2)) m k a))

theorem localEdgeReconstruction_projection (m k : ℕ) (energy : ℝ) (a : Fin (m + 2))
    (x : VertexBallInnovation (m + 2) (k + 1) → ℝ) :
    localEdgeReconstruction m k energy a (forestLocalProjection (Fin (m + 2)) m k a x) =
      edgeCoverRestriction m k a (vertexBallBuild m (k + 1) energy x) := by
  ext v
  exact vertexBallBuild_edgeCover_agrees m k energy a _ x
    (forestLocalFill_projection_old (Fin (m + 2)) m k a x)
    (forestLocalFill_projection_branch (Fin (m + 2)) m k a x) v

theorem localEdgeReconstruction_core (m k : ℕ) (energy : ℝ) (a : Fin (m + 2))
    (z : LocalEdgeInnovation m k → ℝ) :
    (fun v => localEdgeReconstruction m k energy a z (vertexCoreInEdgeCover m k a v)) =
      vertexBallBuild m k energy (fun j => z (Sum.inl j)) := by
  ext v
  change vertexBallBuild m (k + 1) energy (forestLocalFill (Fin (m + 2)) m k a z)
    (edgeInVertexCover m k a (vertexCoreInEdgeCover m k a v)) = _
  rw [edgeInVertexCover_core,
    congrFun (vertexBallBuild_restrict m k energy (forestLocalFill (Fin (m + 2)) m k a z)) v]
  congr 1
  ext j
  exact forestLocalFill_old (Fin (m + 2)) m k a z j

theorem localEdgeReconstruction_branch_extract (m k : ℕ) (energy : ℝ) (a : Fin (m + 2))
    (z : LocalEdgeInnovation m k → ℝ) :
    branchExtract m (k + 1) (fun v => localEdgeReconstruction m k energy a z (true, v)) =
      fun j => forestLocalFill (Fin (m + 2)) m k a z (Sum.inr (a, j)) := by
  let fill := forestLocalFill (Fin (m + 2)) m k a z
  exact branchExtract_build m (k + 1) energy (vertexInnovationRoot m (k + 1) energy fill)
    (vertexInnovationRoot m (k + 1) energy fill + fill (Sum.inl a)) (fun j => fill (Sum.inr (a, j)))

theorem localEdgeReconstruction_injective (m k : ℕ) (energy : ℝ) (a : Fin (m + 2)) :
    Function.Injective (localEdgeReconstruction m k energy a) := by
  intro z w h
  have hold := congrArg (fun f => fun v => f (vertexCoreInEdgeCover m k a v)) h
  change (fun v => localEdgeReconstruction m k energy a z (vertexCoreInEdgeCover m k a v)) =
    (fun v => localEdgeReconstruction m k energy a w (vertexCoreInEdgeCover m k a v)) at hold
  rw [localEdgeReconstruction_core, localEdgeReconstruction_core] at hold
  have hcoords := congrArg (vertexBallExtract m k) hold
  rw [vertexBallExtract_build, vertexBallExtract_build] at hcoords
  have hbranch := congrArg (fun f => branchExtract m (k + 1) (fun v => f (true, v))) h
  change branchExtract m (k + 1) (fun v => localEdgeReconstruction m k energy a z (true, v)) =
    branchExtract m (k + 1) (fun v => localEdgeReconstruction m k energy a w (true, v)) at hbranch
  rw [localEdgeReconstruction_branch_extract, localEdgeReconstruction_branch_extract] at hbranch
  ext j
  cases j with
  | inl old => exact congrFun hcoords old
  | inr new =>
      have hn := congrFun hbranch ((branchInnovationSplit m k).symm (Sum.inr new))
      have hlz := forestLocalFill_new (Fin (m + 2)) m k a z new
      have hlw := forestLocalFill_new (Fin (m + 2)) m k a w new
      change forestLocalFill (Fin (m + 2)) m k a z (Sum.inr (a, (branchInnovationSplit m k).symm (Sum.inr new))) = _ at hlz
      change forestLocalFill (Fin (m + 2)) m k a w (Sum.inr (a, (branchInnovationSplit m k).symm (Sum.inr new))) = _ at hlw
      exact hlz.symm.trans (hn.trans hlw)

theorem card_localEdgeInnovation (m k : ℕ) :
    Fintype.card (LocalEdgeInnovation m k) = 2 * (m + 1) ^ (k + 1) := by
  change Fintype.card (VertexBallInnovation (m + 2) k ⊕ NewBranchInnovation m k) = _
  rw [Fintype.card_sum, card_vertexBallInnovation (m + 2) k (by omega)]
  simp only [NewBranchInnovation, Fintype.card_prod, card_branchLeaf, Fintype.card_fin]
  rw [show m + 2 - 1 = m + 1 by omega, pow_succ]
  ring

def localEdgeSolutionLinear (m k : ℕ) (energy : ℝ) (hne : energy ≠ (m + 2 : ℝ)) (a : Fin (m + 2)) :
    (LocalEdgeInnovation m k → ℝ) →ₗ[ℝ] edgeBallEigenSpace m (k + 1) energy where
  toFun z := ⟨localEdgeReconstruction m k energy a z,
    (mem_edgeBallEigenSpace_iff m (k + 1) energy _).mpr
      (edgeInVertexCover_eigenrelation m k energy
        (vertexBallBuild m (k + 1) energy (forestLocalFill (Fin (m + 2)) m k a z))
        (vertexBallBuild_eigenrelation m (k + 1) energy hne _) a)⟩
  map_add' z w := Subtype.ext ((localEdgeReconstruction m k energy a).map_add z w)
  map_smul' r z := Subtype.ext ((localEdgeReconstruction m k energy a).map_smul r z)

/-- The common-core plus one extension block is an actual invertible linear
chart of the entire physical edge-window eigenrelation space. -/
def localEdgeSolutionEquiv (m k : ℕ) (energy : ℝ) (hne : energy ≠ (m + 2 : ℝ)) (a : Fin (m + 2)) :
    (LocalEdgeInnovation m k → ℝ) ≃ₗ[ℝ] edgeBallEigenSpace m (k + 1) energy := by
  let f := localEdgeSolutionLinear m k energy hne a
  have hinj : Function.Injective f := by
    intro z w h
    exact localEdgeReconstruction_injective m k energy a (congrArg Subtype.val h)
  have hdim : Module.finrank ℝ (LocalEdgeInnovation m k → ℝ) =
      Module.finrank ℝ (edgeBallEigenSpace m (k + 1) energy) := by
    rw [Module.finrank_fintype_fun_eq_card, card_localEdgeInnovation, finrank_edgeBallEigenSpace]
  exact LinearEquiv.ofBijective f ⟨hinj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩

@[simp] theorem localEdgeSolutionEquiv_coe (m k : ℕ) (energy : ℝ) (hne : energy ≠ (m + 2 : ℝ))
    (a : Fin (m + 2)) (z : LocalEdgeInnovation m k → ℝ) :
    (localEdgeSolutionEquiv m k energy hne a z : EdgeBallVertex (m + 2) (k + 1) → ℝ) =
      localEdgeReconstruction m k energy a z := rfl

end GaussianWave.BS
