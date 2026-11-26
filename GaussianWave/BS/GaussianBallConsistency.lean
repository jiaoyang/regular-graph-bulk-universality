import GaussianWave.BS.GaussianBallConstruction

/-!
# Consistency of the actual finite Gaussian family

The marginal maps below literally delete the last level.  Gaussian source
coordinates are restricted along injections; orthogonal Gaussian invariance
then proves consistency of the resulting finite probability laws.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianWave.BS

def branchVertexInclusion (q : ℕ) : (k : ℕ) → BranchVertex q k → BranchVertex q (k + 1)
  | 0, _ => Sum.inl ()
  | k + 1, v => Sum.elim Sum.inl (fun av => Sum.inr (av.1, branchVertexInclusion q k av.2)) v

@[simp] theorem branchVertexInclusion_root (q k : ℕ) :
    branchVertexInclusion q k (branchRoot q k) = branchRoot q (k + 1) := by
  cases k <;> rfl

def branchInnovationInclusion (q : ℕ) : (k : ℕ) → BranchInnovation q k → BranchInnovation q (k + 1)
  | 0, j => Empty.elim j
  | k + 1, j => Sum.elim Sum.inl
      (fun aj => Sum.inr (aj.1, branchInnovationInclusion q k aj.2)) j

def branchNoiseInclusion (q : ℕ) : (k : ℕ) → BranchNoise q k → BranchNoise q (k + 1)
  | 0, j => Empty.elim j
  | k + 1, j => Sum.elim Sum.inl
      (fun aj => Sum.inr (aj.1, branchNoiseInclusion q k aj.2)) j

theorem branchNoiseInclusion_injective (q k : ℕ) :
    Function.Injective (branchNoiseInclusion q k) := by
  induction k with
  | zero => intro i; exact Empty.elim i
  | succ k ih =>
      intro i j h
      cases i with
      | inl a =>
          cases j with
          | inl b => exact congrArg Sum.inl (Sum.inl.inj h)
          | inr bj => exact Sum.noConfusion h
      | inr ai =>
          cases j with
          | inl b => exact Sum.noConfusion h
          | inr bj =>
              have hp := Sum.inr.inj h
              have ha : ai.1 = bj.1 := congrArg
                (fun p : Fin q × BranchNoise q (k + 1) => p.1) hp
              have hb : ai.2 = bj.2 := ih (congrArg
                (fun p : Fin q × BranchNoise q (k + 1) => p.2) hp)
              cases ai; cases bj
              simp_all

theorem branchBuild_restrict (m k : ℕ) (energy parent root : ℝ)
    (z : BranchInnovation (m + 1) (k + 1) → ℝ) :
    (fun v => branchBuild m (k + 1) energy parent root z (branchVertexInclusion (m + 1) k v)) =
      branchBuild m k energy parent root (fun j => z (branchInnovationInclusion (m + 1) k j)) := by
  induction k generalizing parent root with
  | zero => ext v; cases v; rfl
  | succ k ih =>
      ext v
      cases v with
      | inl u => rfl
      | inr av =>
          exact congrFun (ih root
            (siblingFill m (energy * root - parent) (fun i => z (Sum.inl i)) av.1)
            (fun j => z (Sum.inr (av.1, j)))) av.2

theorem branchNoiseInnovation_restrict (m k : ℕ) (scale : ℝ)
    (z : BranchNoise (m + 1) (k + 1) → ℝ) :
    (fun j => branchNoiseInnovation m (k + 1) scale z (branchInnovationInclusion (m + 1) k j)) =
      branchNoiseInnovation m k scale (fun j => z (branchNoiseInclusion (m + 1) k j)) := by
  induction k with
  | zero => ext j; exact Empty.elim j
  | succ k ih =>
      ext j
      cases j with
      | inl i => rfl
      | inr aj => exact congrFun (ih (fun j => z (Sum.inr (aj.1, j)))) aj.2

def vertexBallInclusion (m k : ℕ) : VertexBallVertex (m + 2) k → VertexBallVertex (m + 2) (k + 1) :=
  Sum.elim Sum.inl (fun av => Sum.inr (av.1, branchVertexInclusion (m + 1) k av.2))

def edgeBallInclusion (m k : ℕ) : EdgeBallVertex (m + 2) k → EdgeBallVertex (m + 2) (k + 1) :=
  fun bv => (bv.1, branchVertexInclusion (m + 1) k bv.2)

def vertexInnovationInclusion (m k : ℕ) :
    VertexBallInnovation (m + 2) k → VertexBallInnovation (m + 2) (k + 1) :=
  Sum.elim Sum.inl (fun aj => Sum.inr (aj.1, branchInnovationInclusion (m + 1) k aj.2))

def edgeInnovationInclusion (m k : ℕ) :
    EdgeBallInnovation (m + 2) k → EdgeBallInnovation (m + 2) (k + 1) :=
  Sum.elim Sum.inl (fun bj => Sum.inr (bj.1, branchInnovationInclusion (m + 1) k bj.2))

def vertexGaussianInputInclusion (m k : ℕ) : VertexGaussianInput m k → VertexGaussianInput m (k + 1) :=
  Sum.elim Sum.inl (fun aj => Sum.inr (aj.1, branchNoiseInclusion (m + 1) k aj.2))

def edgeGaussianInputInclusion (m k : ℕ) : EdgeGaussianInput m k → EdgeGaussianInput m (k + 1) :=
  Sum.elim Sum.inl (fun bj => Sum.inr (bj.1, branchNoiseInclusion (m + 1) k bj.2))

theorem vertexGaussianInputInclusion_injective (m k : ℕ) :
    Function.Injective (vertexGaussianInputInclusion m k) := by
  apply Function.Injective.sumMap Function.injective_id
  exact Function.Injective.prodMap Function.injective_id (branchNoiseInclusion_injective _ _)

theorem edgeGaussianInputInclusion_injective (m k : ℕ) :
    Function.Injective (edgeGaussianInputInclusion m k) := by
  apply Function.Injective.sumMap Function.injective_id
  exact Function.Injective.prodMap Function.injective_id (branchNoiseInclusion_injective _ _)

theorem vertexBallBuild_restrict (m k : ℕ) (energy : ℝ)
    (z : VertexBallInnovation (m + 2) (k + 1) → ℝ) :
    (fun v => vertexBallBuild m (k + 1) energy z (vertexBallInclusion m k v)) =
      vertexBallBuild m k energy (fun j => z (vertexInnovationInclusion m k j)) := by
  ext v
  cases v with
  | inl u => rfl
  | inr av =>
      exact congrFun (branchBuild_restrict m k energy (vertexInnovationRoot m (k + 1) energy z)
        (vertexInnovationRoot m (k + 1) energy z + z (Sum.inl av.1))
        (fun j => z (Sum.inr (av.1, j)))) av.2

theorem edgeBallBuild_restrict (m k : ℕ) (energy : ℝ)
    (z : EdgeBallInnovation (m + 2) (k + 1) → ℝ) :
    (fun v => edgeBallBuild m (k + 1) energy z (edgeBallInclusion m k v)) =
      edgeBallBuild m k energy (fun j => z (edgeInnovationInclusion m k j)) := by
  ext bv
  exact congrFun (branchBuild_restrict m k energy (z (Sum.inl (!bv.1))) (z (Sum.inl bv.1))
    (fun j => z (Sum.inr (bv.1, j)))) bv.2

theorem vertexGaussianInnovation_restrict (m k : ℕ) (energy : ℝ)
    (z : VertexGaussianInput m (k + 1) → ℝ) :
    (fun j => vertexGaussianInnovation m (k + 1) energy z (vertexInnovationInclusion m k j)) =
      vertexGaussianInnovation m k energy (fun j => z (vertexGaussianInputInclusion m k j)) := by
  ext j
  cases j with
  | inl a => rfl
  | inr aj => exact congrFun (branchNoiseInnovation_restrict m k _
      (fun j => z (Sum.inr (aj.1, j)))) aj.2

theorem edgeGaussianInnovation_restrict (m k : ℕ) (energy : ℝ)
    (z : EdgeGaussianInput m (k + 1) → ℝ) :
    (fun j => edgeGaussianInnovation m (k + 1) energy z (edgeInnovationInclusion m k j)) =
      edgeGaussianInnovation m k energy (fun j => z (edgeGaussianInputInclusion m k j)) := by
  ext j
  cases j with
  | inl b => rfl
  | inr bj => exact congrFun (branchNoiseInnovation_restrict m k _
      (fun j => z (Sum.inr (bj.1, j)))) bj.2

theorem vertexGaussianMap_restrict (m k : ℕ) (energy : ℝ)
    (z : VertexGaussianInput m (k + 1) → ℝ) :
    (fun v => vertexGaussianMap m (k + 1) energy z (vertexBallInclusion m k v)) =
      vertexGaussianMap m k energy (fun j => z (vertexGaussianInputInclusion m k j)) := by
  change (fun v => vertexBallBuild m (k + 1) energy _ (vertexBallInclusion m k v)) = _
  rw [vertexBallBuild_restrict]
  change vertexBallBuild m k energy
    (fun j => vertexGaussianInnovation m (k + 1) energy z (vertexInnovationInclusion m k j)) = _
  rw [vertexGaussianInnovation_restrict]
  rfl

theorem edgeGaussianMap_restrict (m k : ℕ) (energy : ℝ)
    (z : EdgeGaussianInput m (k + 1) → ℝ) :
    (fun v => edgeGaussianMap m (k + 1) energy z (edgeBallInclusion m k v)) =
      edgeGaussianMap m k energy (fun j => z (edgeGaussianInputInclusion m k j)) := by
  change (fun v => edgeBallBuild m (k + 1) energy _ (edgeBallInclusion m k v)) = _
  rw [edgeBallBuild_restrict]
  change edgeBallBuild m k energy
    (fun j => edgeGaussianInnovation m (k + 1) energy z (edgeInnovationInclusion m k j)) = _
  rw [edgeGaussianInnovation_restrict]
  rfl

def coordinateRestrictionMatrix {I J : Type*} [DecidableEq J] (e : I → J) : Matrix I J ℝ :=
  fun i j => if j = e i then 1 else 0

theorem coordinateRestrictionMatrix_mulVec {I J : Type*} [Fintype J] [DecidableEq J]
    (e : I → J) (z : J → ℝ) : (coordinateRestrictionMatrix e).mulVec z = fun i => z (e i) := by
  ext i
  simp [coordinateRestrictionMatrix, Matrix.mulVec, dotProduct]

theorem coordinateRestrictionMatrix_orthonormal {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (e : I → J) (he : Function.Injective e) :
    coordinateRestrictionMatrix e * (coordinateRestrictionMatrix e).transpose = 1 := by
  ext i j
  simp [Matrix.mul_apply, coordinateRestrictionMatrix, Matrix.transpose_apply,
    Matrix.one_apply, ← he.eq_iff, eq_comm]

theorem standardVector_map_coordinateRestriction {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (e : I → J) (he : Function.Injective e) :
    Measure.map (fun z : J → ℝ => fun i => z (e i)) (standardVector J) = standardVector I := by
  simpa only [coordinateRestrictionMatrix_mulVec] using
    standardVector_map_orthonormal_rows (coordinateRestrictionMatrix e)
      (coordinateRestrictionMatrix_orthonormal e he)

theorem vertexGaussianBallLaw_consistent (m k : ℕ) (energy : ℝ) :
    Measure.map (fun x => fun v => x (vertexBallInclusion m k v))
      (vertexGaussianBallLaw m (k + 1) energy) = vertexGaussianBallLaw m k energy := by
  rw [vertexGaussianBallLaw, Measure.map_map (by fun_prop)
    (vertexGaussianMap m (k + 1) energy).continuous_of_finiteDimensional.measurable]
  change Measure.map (fun z => fun v => vertexGaussianMap m (k + 1) energy z
    (vertexBallInclusion m k v)) _ = _
  have hf : (fun z => fun v => vertexGaussianMap m (k + 1) energy z
      (vertexBallInclusion m k v)) =
      (fun z => vertexGaussianMap m k energy (fun j => z (vertexGaussianInputInclusion m k j))) :=
    funext (vertexGaussianMap_restrict m k energy)
  rw [hf]
  change Measure.map ((vertexGaussianMap m k energy) ∘
    (fun z : VertexGaussianInput m (k + 1) → ℝ => fun j => z (vertexGaussianInputInclusion m k j))) _ = _
  rw [← Measure.map_map (vertexGaussianMap m k energy).continuous_of_finiteDimensional.measurable
    (by fun_prop), standardVector_map_coordinateRestriction _
      (vertexGaussianInputInclusion_injective m k)]
  rfl

theorem edgeGaussianBallLaw_consistent (m k : ℕ) (energy : ℝ) :
    Measure.map (fun x => fun v => x (edgeBallInclusion m k v))
      (edgeGaussianBallLaw m (k + 1) energy) = edgeGaussianBallLaw m k energy := by
  rw [edgeGaussianBallLaw, Measure.map_map (by fun_prop)
    (edgeGaussianMap m (k + 1) energy).continuous_of_finiteDimensional.measurable]
  change Measure.map (fun z => fun v => edgeGaussianMap m (k + 1) energy z
    (edgeBallInclusion m k v)) _ = _
  have hf : (fun z => fun v => edgeGaussianMap m (k + 1) energy z
      (edgeBallInclusion m k v)) =
      (fun z => edgeGaussianMap m k energy (fun j => z (edgeGaussianInputInclusion m k j))) :=
    funext (edgeGaussianMap_restrict m k energy)
  rw [hf]
  change Measure.map ((edgeGaussianMap m k energy) ∘
    (fun z : EdgeGaussianInput m (k + 1) → ℝ => fun j => z (edgeGaussianInputInclusion m k j))) _ = _
  rw [← Measure.map_map (edgeGaussianMap m k energy).continuous_of_finiteDimensional.measurable
    (by fun_prop), standardVector_map_coordinateRestriction _
      (edgeGaussianInputInclusion_injective m k)]
  rfl

end GaussianWave.BS
