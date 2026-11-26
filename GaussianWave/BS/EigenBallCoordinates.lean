import GaussianWave.BS.BranchCoordinates

/-!
# Actual eigen-solution charts on finite balls

The vertex chart consists of the root-neighbor differences followed by the
sibling differences in each branch.  The edge chart starts with the two
endpoint values.  The maps below are actual inverses on the explicitly
written eigenrelations, not dimension or covariance assumptions.
-/
noncomputable section
open scoped BigOperators
namespace GaussianWave.BS

def vertexInnovationRoot (m k : ℕ) (energy : ℝ)
    (z : VertexBallInnovation (m + 2) k → ℝ) : ℝ :=
  (∑ a : Fin (m + 2), z (Sum.inl a)) / (energy - (m + 2))

def vertexBallBuild (m k : ℕ) (energy : ℝ)
    (z : VertexBallInnovation (m + 2) k → ℝ) : VertexBallVertex (m + 2) k → ℝ :=
  Sum.elim (fun _ => vertexInnovationRoot m k energy z) (fun av =>
    branchBuild m k energy (vertexInnovationRoot m k energy z)
      (vertexInnovationRoot m k energy z + z (Sum.inl av.1))
      (fun j => z (Sum.inr (av.1, j))) av.2)

def vertexBallExtract (m k : ℕ) (x : VertexBallVertex (m + 2) k → ℝ) :
    VertexBallInnovation (m + 2) k → ℝ :=
  Sum.elim (fun a => x (vertexBallNeighbor (m + 2) k a) - x (vertexBallRoot (m + 2) k))
    (fun aj => branchExtract m k (fun v => x (Sum.inr (aj.1, v))) aj.2)

def VertexBallEigenrelation (m k : ℕ) (energy : ℝ)
    (x : VertexBallVertex (m + 2) k → ℝ) : Prop :=
  (∑ a : Fin (m + 2), x (vertexBallNeighbor (m + 2) k a)) =
      energy * x (vertexBallRoot (m + 2) k) ∧
  ∀ a, BranchEigenrelation m k energy (x (vertexBallRoot (m + 2) k))
    (fun v => x (Sum.inr (a, v)))

@[simp] theorem vertexBallBuild_root (m k : ℕ) (energy : ℝ)
    (z : VertexBallInnovation (m + 2) k → ℝ) :
    vertexBallBuild m k energy z (vertexBallRoot (m + 2) k) =
      vertexInnovationRoot m k energy z := rfl

@[simp] theorem vertexBallBuild_neighbor (m k : ℕ) (energy : ℝ)
    (z : VertexBallInnovation (m + 2) k → ℝ) (a : Fin (m + 2)) :
    vertexBallBuild m k energy z (vertexBallNeighbor (m + 2) k a) =
      vertexInnovationRoot m k energy z + z (Sum.inl a) :=
  branchBuild_root _ _ _ _ _ _

theorem vertexBallBuild_eigenrelation (m k : ℕ) (energy : ℝ)
    (he : energy ≠ (m + 2 : ℝ)) (z : VertexBallInnovation (m + 2) k → ℝ) :
    VertexBallEigenrelation m k energy (vertexBallBuild m k energy z) := by
  constructor
  · simp only [vertexBallBuild_neighbor, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, vertexBallBuild_root]
    unfold vertexInnovationRoot
    have hne : energy - (m + 2 : ℝ) ≠ 0 := sub_ne_zero.mpr he
    push_cast
    field_simp
    <;> ring
  · intro a
    exact branchBuild_eigenrelation m k energy (vertexInnovationRoot m k energy z)
      (vertexInnovationRoot m k energy z + z (Sum.inl a))
      (fun j => z (Sum.inr (a, j)))

theorem vertexBallExtract_build (m k : ℕ) (energy : ℝ)
    (z : VertexBallInnovation (m + 2) k → ℝ) :
    vertexBallExtract m k (vertexBallBuild m k energy z) = z := by
  ext j
  cases j with
  | inl a =>
      change vertexBallBuild _ _ _ _ (vertexBallNeighbor _ _ _) -
        vertexBallBuild _ _ _ _ (vertexBallRoot _ _) = _
      rw [vertexBallBuild_neighbor, vertexBallBuild_root]
      ring
  | inr aj =>
      exact congrFun (branchExtract_build m k energy (vertexInnovationRoot m k energy z)
        (vertexInnovationRoot m k energy z + z (Sum.inl aj.1))
        (fun j => z (Sum.inr (aj.1, j)))) aj.2

theorem vertexInnovationRoot_extract (m k : ℕ) (energy : ℝ)
    (he : energy ≠ (m + 2 : ℝ)) (x : VertexBallVertex (m + 2) k → ℝ)
    (hx : VertexBallEigenrelation m k energy x) :
    vertexInnovationRoot m k energy (vertexBallExtract m k x) = x (vertexBallRoot (m + 2) k) := by
  unfold vertexInnovationRoot
  change (∑ a : Fin (m + 2),
    (x (vertexBallNeighbor (m + 2) k a) - x (vertexBallRoot (m + 2) k))) /
      (energy - (m + 2)) = _
  rw [Finset.sum_sub_distrib, hx.1]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hne : energy - (m + 2 : ℝ) ≠ 0 := sub_ne_zero.mpr he
  push_cast
  field_simp
  <;> ring

theorem vertexBallBuild_extract (m k : ℕ) (energy : ℝ)
    (he : energy ≠ (m + 2 : ℝ)) (x : VertexBallVertex (m + 2) k → ℝ)
    (hx : VertexBallEigenrelation m k energy x) :
    vertexBallBuild m k energy (vertexBallExtract m k x) = x := by
  have hr := vertexInnovationRoot_extract m k energy he x hx
  ext v
  cases v with
  | inl u => cases u; exact hr
  | inr av =>
      change branchBuild m k energy (vertexInnovationRoot _ _ _ _)
        (vertexInnovationRoot _ _ _ _ +
          (x (vertexBallNeighbor _ _ av.1) - x (vertexBallRoot _ _)))
        (branchExtract m k (fun v => x (Sum.inr (av.1, v)))) av.2 = _
      rw [hr]
      have hh : x (vertexBallRoot (m + 2) k) +
          (x (vertexBallNeighbor (m + 2) k av.1) - x (vertexBallRoot (m + 2) k)) =
          x (vertexBallNeighbor (m + 2) k av.1) := by ring
      rw [hh]
      exact congrFun (branchBuild_extract m k energy _ _ (hx.2 av.1)) av.2

def edgeBallBuild (m k : ℕ) (energy : ℝ)
    (z : EdgeBallInnovation (m + 2) k → ℝ) : EdgeBallVertex (m + 2) k → ℝ :=
  fun bv => branchBuild m k energy (z (Sum.inl (!bv.1))) (z (Sum.inl bv.1))
    (fun j => z (Sum.inr (bv.1, j))) bv.2

def edgeBallExtract (m k : ℕ) (x : EdgeBallVertex (m + 2) k → ℝ) :
    EdgeBallInnovation (m + 2) k → ℝ :=
  Sum.elim (fun b => x (edgeBallEndpoint (m + 2) k b))
    (fun bj => branchExtract m k (fun v => x (bj.1, v)) bj.2)

def EdgeBallEigenrelation (m k : ℕ) (energy : ℝ)
    (x : EdgeBallVertex (m + 2) k → ℝ) : Prop :=
  ∀ b, BranchEigenrelation m k energy (x (edgeBallEndpoint (m + 2) k (!b)))
    (fun v => x (b, v))

@[simp] theorem edgeBallBuild_endpoint (m k : ℕ) (energy : ℝ)
    (z : EdgeBallInnovation (m + 2) k → ℝ) (b : Bool) :
    edgeBallBuild m k energy z (edgeBallEndpoint (m + 2) k b) = z (Sum.inl b) :=
  branchBuild_root _ _ _ _ _ _

theorem edgeBallBuild_eigenrelation (m k : ℕ) (energy : ℝ)
    (z : EdgeBallInnovation (m + 2) k → ℝ) :
    EdgeBallEigenrelation m k energy (edgeBallBuild m k energy z) := by
  intro b
  rw [edgeBallBuild_endpoint]
  exact branchBuild_eigenrelation m k energy (z (Sum.inl (!b))) (z (Sum.inl b))
    (fun j => z (Sum.inr (b, j)))

theorem edgeBallExtract_build (m k : ℕ) (energy : ℝ)
    (z : EdgeBallInnovation (m + 2) k → ℝ) :
    edgeBallExtract m k (edgeBallBuild m k energy z) = z := by
  ext j
  cases j with
  | inl b => exact edgeBallBuild_endpoint _ _ _ _ _
  | inr bj =>
      exact congrFun (branchExtract_build m k energy (z (Sum.inl (!bj.1)))
        (z (Sum.inl bj.1)) (fun j => z (Sum.inr (bj.1, j)))) bj.2

theorem edgeBallBuild_extract (m k : ℕ) (energy : ℝ)
    (x : EdgeBallVertex (m + 2) k → ℝ) (hx : EdgeBallEigenrelation m k energy x) :
    edgeBallBuild m k energy (edgeBallExtract m k x) = x := by
  ext bv
  exact congrFun (branchBuild_extract m k energy _ _ (hx bv.1)) bv.2

theorem vertexInnovationRoot_add (m k : ℕ) (energy : ℝ)
    (z w : VertexBallInnovation (m + 2) k → ℝ) :
    vertexInnovationRoot m k energy (z + w) =
      vertexInnovationRoot m k energy z + vertexInnovationRoot m k energy w := by
  simp only [vertexInnovationRoot, Pi.add_apply, Finset.sum_add_distrib, add_div]

theorem vertexInnovationRoot_smul (m k : ℕ) (energy a : ℝ)
    (z : VertexBallInnovation (m + 2) k → ℝ) :
    vertexInnovationRoot m k energy (a • z) = a * vertexInnovationRoot m k energy z := by
  simp only [vertexInnovationRoot, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

def vertexBallBuildLinear (m k : ℕ) (energy : ℝ) :
    (VertexBallInnovation (m + 2) k → ℝ) →ₗ[ℝ] (VertexBallVertex (m + 2) k → ℝ) where
  toFun := vertexBallBuild m k energy
  map_add' z w := by
    ext v
    cases v with
    | inl u => exact vertexInnovationRoot_add _ _ _ _ _
    | inr av =>
        change branchBuild m k energy (vertexInnovationRoot m k energy (z + w))
          (vertexInnovationRoot m k energy (z + w) + (z (Sum.inl av.1) + w (Sum.inl av.1)))
          (fun j => z (Sum.inr (av.1, j)) + w (Sum.inr (av.1, j))) av.2 = _
        rw [vertexInnovationRoot_add]
        have hh : vertexInnovationRoot m k energy z + vertexInnovationRoot m k energy w +
            (z (Sum.inl av.1) + w (Sum.inl av.1)) =
            (vertexInnovationRoot m k energy z + z (Sum.inl av.1)) +
              (vertexInnovationRoot m k energy w + w (Sum.inl av.1)) := by ring
        rw [hh]
        exact congrFun (branchBuild_add m k energy _ _ _ _ _ _) av.2
  map_smul' a z := by
    ext v
    cases v with
    | inl u => exact vertexInnovationRoot_smul _ _ _ _ _
    | inr av =>
        change branchBuild m k energy (vertexInnovationRoot m k energy (a • z))
          (vertexInnovationRoot m k energy (a • z) + a * z (Sum.inl av.1))
          (fun j => a * z (Sum.inr (av.1, j))) av.2 = _
        rw [vertexInnovationRoot_smul, ← mul_add]
        exact congrFun (branchBuild_smul m k energy _ _ _ _) av.2

def edgeBallBuildLinear (m k : ℕ) (energy : ℝ) :
    (EdgeBallInnovation (m + 2) k → ℝ) →ₗ[ℝ] (EdgeBallVertex (m + 2) k → ℝ) where
  toFun := edgeBallBuild m k energy
  map_add' z w := by
    ext bv
    exact congrFun (branchBuild_add m k energy (z (Sum.inl (!bv.1)))
      (w (Sum.inl (!bv.1))) (z (Sum.inl bv.1)) (w (Sum.inl bv.1))
      (fun j => z (Sum.inr (bv.1, j))) (fun j => w (Sum.inr (bv.1, j)))) bv.2
  map_smul' a z := by
    ext bv
    exact congrFun (branchBuild_smul m k energy a (z (Sum.inl (!bv.1)))
      (z (Sum.inl bv.1)) (fun j => z (Sum.inr (bv.1, j)))) bv.2

/-- The solution subspaces are actual ranges of the explicit parametrizations.
The next two equivalences identify them with the literal eigenrelations. -/
def vertexBallEigenSpace (m k : ℕ) (energy : ℝ) :
    Submodule ℝ (VertexBallVertex (m + 2) k → ℝ) := LinearMap.range (vertexBallBuildLinear m k energy)

def edgeBallEigenSpace (m k : ℕ) (energy : ℝ) :
    Submodule ℝ (EdgeBallVertex (m + 2) k → ℝ) := LinearMap.range (edgeBallBuildLinear m k energy)

theorem mem_vertexBallEigenSpace_iff (m k : ℕ) (energy : ℝ)
    (he : energy ≠ (m + 2 : ℝ)) (x : VertexBallVertex (m + 2) k → ℝ) :
    x ∈ vertexBallEigenSpace m k energy ↔ VertexBallEigenrelation m k energy x := by
  constructor
  · rintro ⟨z, rfl⟩
    exact vertexBallBuild_eigenrelation m k energy he z
  · intro hx
    exact ⟨vertexBallExtract m k x, vertexBallBuild_extract m k energy he x hx⟩

theorem mem_edgeBallEigenSpace_iff (m k : ℕ) (energy : ℝ)
    (x : EdgeBallVertex (m + 2) k → ℝ) :
    x ∈ edgeBallEigenSpace m k energy ↔ EdgeBallEigenrelation m k energy x := by
  constructor
  · rintro ⟨z, rfl⟩
    exact edgeBallBuild_eigenrelation m k energy z
  · intro hx
    exact ⟨edgeBallExtract m k x, edgeBallBuild_extract m k energy x hx⟩

def vertexBallSolutionEquiv (m k : ℕ) (energy : ℝ) :
    (VertexBallInnovation (m + 2) k → ℝ) ≃ₗ[ℝ] vertexBallEigenSpace m k energy :=
  LinearEquiv.ofLeftInverse (f := vertexBallBuildLinear m k energy)
    (vertexBallExtract_build m k energy)

def edgeBallSolutionEquiv (m k : ℕ) (energy : ℝ) :
    (EdgeBallInnovation (m + 2) k → ℝ) ≃ₗ[ℝ] edgeBallEigenSpace m k energy :=
  LinearEquiv.ofLeftInverse (f := edgeBallBuildLinear m k energy)
    (edgeBallExtract_build m k energy)

theorem finrank_vertexBallEigenSpace (m k : ℕ) (energy : ℝ) :
    Module.finrank ℝ (vertexBallEigenSpace m k energy) = (m + 2) * (m + 1) ^ k := by
  rw [← (vertexBallSolutionEquiv m k energy).finrank_eq]
  simpa only [Module.finrank_fintype_fun_eq_card, Nat.add_sub_cancel] using
    card_vertexBallInnovation (m + 2) k (by omega)

theorem finrank_edgeBallEigenSpace (m k : ℕ) (energy : ℝ) :
    Module.finrank ℝ (edgeBallEigenSpace m k energy) = 2 * (m + 1) ^ k := by
  rw [← (edgeBallSolutionEquiv m k energy).finrank_eq]
  simpa only [Module.finrank_fintype_fun_eq_card, Nat.add_sub_cancel] using
    card_edgeBallInnovation (m + 2) k (by omega)

end GaussianWave.BS
