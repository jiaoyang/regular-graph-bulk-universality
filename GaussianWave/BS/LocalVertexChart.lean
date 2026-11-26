import GaussianWave.BS.LocalEdgeChart

/-!
# Actual local vertex-window chart inside edge-ball innovation coordinates
-/
noncomputable section
open scoped BigOperators
namespace GaussianWave.BS

abbrev LocalVertexInnovation (m k : ℕ) := ForestLocalInnovation Bool m k

def edgeHalfInVertexCover (m k : ℕ) :
    BranchVertex (m + 1) (k + 1) → VertexBallVertex (m + 2) k :=
  Sum.elim (fun _ => Sum.inl ()) (fun jv => Sum.inr (jv.1.succ, jv.2))

theorem vertexInEdgeCover_half (m k : ℕ) (b : Bool) (v : BranchVertex (m + 1) (k + 1)) :
    vertexInEdgeCover m k b (edgeHalfInVertexCover m k v) = (b, v) := by
  cases v with
  | inl u => cases u; rfl
  | inr jv => rfl

def edgeCoreInVertexCover (m k : ℕ) (b : Bool) :
    EdgeBallVertex (m + 2) k → VertexBallVertex (m + 2) k :=
  fun cv => if cv.1 = b then edgeHalfInVertexCover m k (branchVertexInclusion (m + 1) k cv.2)
    else Sum.inr (0, cv.2)

theorem vertexInEdgeCover_core (m k : ℕ) (b : Bool) (v : EdgeBallVertex (m + 2) k) :
    vertexInEdgeCover m k b (edgeCoreInVertexCover m k b v) = edgeBallInclusion m k v := by
  rcases v with ⟨c, v⟩
  by_cases h : c = b
  · simp only [edgeCoreInVertexCover, h, if_true, vertexInEdgeCover_half, edgeBallInclusion]
  · have hc : (!b) = c := by cases b <;> cases c <;> simp_all
    simp only [edgeCoreInVertexCover, h, if_false, vertexInEdgeCover, Sum.elim_inr,
      Fin.cases_zero, edgeBallInclusion, hc]

theorem edgeBallBuild_agrees_core (m k : ℕ) (energy : ℝ)
    (x y : EdgeBallInnovation (m + 2) (k + 1) → ℝ)
    (h : ∀ j, x (edgeInnovationInclusion m k j) = y (edgeInnovationInclusion m k j))
    (v : EdgeBallVertex (m + 2) k) :
    edgeBallBuild m (k + 1) energy x (edgeBallInclusion m k v) =
      edgeBallBuild m (k + 1) energy y (edgeBallInclusion m k v) := by
  rw [congrFun (edgeBallBuild_restrict m k energy x) v,
    congrFun (edgeBallBuild_restrict m k energy y) v]
  rw [funext h]

theorem edgeBallBuild_agrees_half (m k : ℕ) (energy : ℝ) (b : Bool)
    (x y : EdgeBallInnovation (m + 2) (k + 1) → ℝ)
    (hold : ∀ j, x (edgeInnovationInclusion m k j) = y (edgeInnovationInclusion m k j))
    (hbranch : ∀ j, x (Sum.inr (b, j)) = y (Sum.inr (b, j))) (v : BranchVertex (m + 1) (k + 1)) :
    edgeBallBuild m (k + 1) energy x (b, v) = edgeBallBuild m (k + 1) energy y (b, v) := by
  have hp : x (Sum.inl (!b)) = y (Sum.inl (!b)) := hold (Sum.inl (!b))
  have hr : x (Sum.inl b) = y (Sum.inl b) := hold (Sum.inl b)
  change branchBuild m (k + 1) energy (x (Sum.inl (!b))) (x (Sum.inl b))
    (fun j => x (Sum.inr (b, j))) v = _
  rw [hp, hr]
  erw [funext hbranch]
  rfl

theorem edgeBallBuild_vertexCover_agrees (m k : ℕ) (energy : ℝ) (b : Bool)
    (x y : EdgeBallInnovation (m + 2) (k + 1) → ℝ)
    (hold : ∀ j, x (edgeInnovationInclusion m k j) = y (edgeInnovationInclusion m k j))
    (hbranch : ∀ j, x (Sum.inr (b, j)) = y (Sum.inr (b, j)))
    (v : VertexBallVertex (m + 2) k) :
    edgeBallBuild m (k + 1) energy x (vertexInEdgeCover m k b v) =
      edgeBallBuild m (k + 1) energy y (vertexInEdgeCover m k b v) := by
  cases v with
  | inl u => exact edgeBallBuild_agrees_half m k energy b x y hold hbranch (Sum.inl ())
  | inr av =>
      rcases av with ⟨a, v⟩
      refine Fin.cases ?_ (fun j => ?_) a
      · exact edgeBallBuild_agrees_core m k energy x y hold ((!b), v)
      · exact edgeBallBuild_agrees_half m k energy b x y hold hbranch (Sum.inr (j, v))

def vertexCoverRestriction (m k : ℕ) (b : Bool) :
    (EdgeBallVertex (m + 2) (k + 1) → ℝ) →ₗ[ℝ] (VertexBallVertex (m + 2) k → ℝ) where
  toFun x := fun v => x (vertexInEdgeCover m k b v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def localVertexReconstruction (m k : ℕ) (energy : ℝ) (b : Bool) :
    (LocalVertexInnovation m k → ℝ) →ₗ[ℝ] (VertexBallVertex (m + 2) k → ℝ) :=
  (vertexCoverRestriction m k b).comp ((edgeBallBuildLinear m (k + 1) energy).comp
    (forestLocalFill Bool m k b))

theorem localVertexReconstruction_projection (m k : ℕ) (energy : ℝ) (b : Bool)
    (x : EdgeBallInnovation (m + 2) (k + 1) → ℝ) :
    localVertexReconstruction m k energy b (forestLocalProjection Bool m k b x) =
      vertexCoverRestriction m k b (edgeBallBuild m (k + 1) energy x) := by
  ext v
  exact edgeBallBuild_vertexCover_agrees m k energy b _ x
    (forestLocalFill_projection_old Bool m k b x) (forestLocalFill_projection_branch Bool m k b x) v

theorem localVertexReconstruction_core (m k : ℕ) (energy : ℝ) (b : Bool)
    (z : LocalVertexInnovation m k → ℝ) :
    (fun v => localVertexReconstruction m k energy b z (edgeCoreInVertexCover m k b v)) =
      edgeBallBuild m k energy (fun j => z (Sum.inl j)) := by
  ext v
  change edgeBallBuild m (k + 1) energy (forestLocalFill Bool m k b z)
    (vertexInEdgeCover m k b (edgeCoreInVertexCover m k b v)) = _
  rw [vertexInEdgeCover_core,
    congrFun (edgeBallBuild_restrict m k energy (forestLocalFill Bool m k b z)) v]
  congr 1
  ext j
  exact forestLocalFill_old Bool m k b z j

theorem localVertexReconstruction_branch_extract (m k : ℕ) (energy : ℝ) (b : Bool)
    (z : LocalVertexInnovation m k → ℝ) :
    branchExtract m (k + 1) (fun v => localVertexReconstruction m k energy b z (edgeHalfInVertexCover m k v)) =
      fun j => forestLocalFill Bool m k b z (Sum.inr (b, j)) := by
  let fill := forestLocalFill Bool m k b z
  change branchExtract m (k + 1)
    (fun v => edgeBallBuild m (k + 1) energy fill (vertexInEdgeCover m k b (edgeHalfInVertexCover m k v))) = _
  simp_rw [vertexInEdgeCover_half]
  exact branchExtract_build m (k + 1) energy (fill (Sum.inl (!b))) (fill (Sum.inl b))
    (fun j => fill (Sum.inr (b, j)))

theorem localVertexReconstruction_injective (m k : ℕ) (energy : ℝ) (b : Bool) :
    Function.Injective (localVertexReconstruction m k energy b) := by
  intro z w h
  have hold := congrArg (fun f => fun v => f (edgeCoreInVertexCover m k b v)) h
  change (fun v => localVertexReconstruction m k energy b z (edgeCoreInVertexCover m k b v)) =
    (fun v => localVertexReconstruction m k energy b w (edgeCoreInVertexCover m k b v)) at hold
  rw [localVertexReconstruction_core, localVertexReconstruction_core] at hold
  have hcoords := congrArg (edgeBallExtract m k) hold
  rw [edgeBallExtract_build, edgeBallExtract_build] at hcoords
  have hbranch := congrArg (fun f => branchExtract m (k + 1) (fun v => f (edgeHalfInVertexCover m k v))) h
  change branchExtract m (k + 1) (fun v => localVertexReconstruction m k energy b z (edgeHalfInVertexCover m k v)) =
    branchExtract m (k + 1) (fun v => localVertexReconstruction m k energy b w (edgeHalfInVertexCover m k v)) at hbranch
  rw [localVertexReconstruction_branch_extract, localVertexReconstruction_branch_extract] at hbranch
  ext j
  cases j with
  | inl old => exact congrFun hcoords old
  | inr new =>
      have hn := congrFun hbranch ((branchInnovationSplit m k).symm (Sum.inr new))
      have hlz := forestLocalFill_new Bool m k b z new
      have hlw := forestLocalFill_new Bool m k b w new
      change forestLocalFill Bool m k b z (Sum.inr (b, (branchInnovationSplit m k).symm (Sum.inr new))) = _ at hlz
      change forestLocalFill Bool m k b w (Sum.inr (b, (branchInnovationSplit m k).symm (Sum.inr new))) = _ at hlw
      exact hlz.symm.trans (hn.trans hlw)

theorem card_localVertexInnovation (m k : ℕ) :
    Fintype.card (LocalVertexInnovation m k) = (m + 2) * (m + 1) ^ k := by
  change Fintype.card (EdgeBallInnovation (m + 2) k ⊕ NewBranchInnovation m k) = _
  rw [Fintype.card_sum, card_edgeBallInnovation (m + 2) k (by omega)]
  simp only [NewBranchInnovation, Fintype.card_prod, card_branchLeaf, Fintype.card_fin]
  rw [show m + 2 - 1 = m + 1 by omega]
  ring

def localVertexSolutionLinear (m k : ℕ) (energy : ℝ) (hne : energy ≠ (m + 2 : ℝ)) (b : Bool) :
    (LocalVertexInnovation m k → ℝ) →ₗ[ℝ] vertexBallEigenSpace m k energy where
  toFun z := ⟨localVertexReconstruction m k energy b z,
    (mem_vertexBallEigenSpace_iff m k energy hne _).mpr
      (vertexInEdgeCover_eigenrelation m k energy
        (edgeBallBuild m (k + 1) energy (forestLocalFill Bool m k b z))
        (edgeBallBuild_eigenrelation m (k + 1) energy _) b)⟩
  map_add' z w := Subtype.ext ((localVertexReconstruction m k energy b).map_add z w)
  map_smul' r z := Subtype.ext ((localVertexReconstruction m k energy b).map_smul r z)

def localVertexSolutionEquiv (m k : ℕ) (energy : ℝ) (hne : energy ≠ (m + 2 : ℝ)) (b : Bool) :
    (LocalVertexInnovation m k → ℝ) ≃ₗ[ℝ] vertexBallEigenSpace m k energy := by
  let f := localVertexSolutionLinear m k energy hne b
  have hinj : Function.Injective f := by
    intro z w h
    exact localVertexReconstruction_injective m k energy b (congrArg Subtype.val h)
  have hdim : Module.finrank ℝ (LocalVertexInnovation m k → ℝ) =
      Module.finrank ℝ (vertexBallEigenSpace m k energy) := by
    rw [Module.finrank_fintype_fun_eq_card, card_localVertexInnovation, finrank_vertexBallEigenSpace]
  exact LinearEquiv.ofBijective f ⟨hinj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩

@[simp] theorem localVertexSolutionEquiv_coe (m k : ℕ) (energy : ℝ) (hne : energy ≠ (m + 2 : ℝ))
    (b : Bool) (z : LocalVertexInnovation m k → ℝ) :
    (localVertexSolutionEquiv m k energy hne b z : VertexBallVertex (m + 2) k → ℝ) =
      localVertexReconstruction m k energy b z := rfl

end GaussianWave.BS
