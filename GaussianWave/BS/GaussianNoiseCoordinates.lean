import GaussianWave.BS.GaussianBallEnergy
import GaussianWave.BS.CenteredNoiseFrame

/-!
# Nonredundant Gaussian sibling coordinates

Each `q-1` dimensional white block is lifted by the proved orthonormal
zero-sum factor.  The resulting weighted energy has no cross-block terms.
-/
noncomputable section
open scoped BigOperators
namespace GaussianWave.BS

def branchOrthoNoiseLift (m : ℕ) : (k : ℕ) →
    (BranchInnovation (m + 1) k → ℝ) → (BranchNoise (m + 1) k → ℝ)
  | 0, _ => Empty.elim
  | k + 1, z => Sum.elim
      ((centeredNoiseFrame m).mulVec (fun i => z (Sum.inl i)))
      (fun aj => branchOrthoNoiseLift m k (fun j => z (Sum.inr (aj.1, j))) aj.2)

theorem branchOrthoNoiseLift_add (m k : ℕ)
    (z w : BranchInnovation (m + 1) k → ℝ) :
    branchOrthoNoiseLift m k (z + w) = branchOrthoNoiseLift m k z + branchOrthoNoiseLift m k w := by
  induction k with
  | zero => ext i; exact Empty.elim i
  | succ k ih =>
      ext j
      cases j with
      | inl a =>
          exact congrFun ((centeredNoiseFrame m).mulVecLin.map_add
            (fun i => z (Sum.inl i)) (fun i => w (Sum.inl i))) a
      | inr aj => exact congrFun (ih _ _) aj.2

theorem branchOrthoNoiseLift_smul (m k : ℕ) (a : ℝ)
    (z : BranchInnovation (m + 1) k → ℝ) :
    branchOrthoNoiseLift m k (a • z) = a • branchOrthoNoiseLift m k z := by
  induction k with
  | zero => ext i; exact Empty.elim i
  | succ k ih =>
      ext j
      cases j with
      | inl i =>
          exact congrFun ((centeredNoiseFrame m).mulVecLin.map_smul a (fun i => z (Sum.inl i))) i
      | inr aj => exact congrFun (ih _) aj.2

def branchOrthoNoiseLiftLinear (m k : ℕ) :
    (BranchInnovation (m + 1) k → ℝ) →ₗ[ℝ] (BranchNoise (m + 1) k → ℝ) where
  toFun := branchOrthoNoiseLift m k
  map_add' := branchOrthoNoiseLift_add m k
  map_smul' := branchOrthoNoiseLift_smul m k

def branchOrthoNoiseEnergy (m : ℕ) (energy : ℝ) : (k : ℕ) →
    (BranchInnovation (m + 1) k → ℝ) → ℝ
  | 0, _ => 0
  | k + 1, z => siblingVariance (m + 2) energy *
      (branchEnergyCoefficients (m + 1) energy k).1 * (∑ i : Fin m, z (Sum.inl i) ^ 2) +
      ∑ a, branchOrthoNoiseEnergy m energy k (fun j => z (Sum.inr (a, j)))

theorem centeredNoise_frame_mulVec (m : ℕ) (z : Fin m → ℝ) :
    centeredNoise ((centeredNoiseFrame m).mulVec z) = (centeredNoiseFrame m).mulVec z := by
  ext a
  simp only [centeredNoise, centeredNoiseFrame_mulVec_sum, zero_div, sub_zero]

theorem branchNoiseEnergy_orthoLift (m k : ℕ) (energy : ℝ)
    (z : BranchInnovation (m + 1) k → ℝ) :
    branchNoiseEnergy m energy k (branchOrthoNoiseLift m k z) =
      branchOrthoNoiseEnergy m energy k z := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change siblingVariance (m + 2) energy * (branchEnergyCoefficients (m + 1) energy k).1 *
          (∑ a, centeredNoise ((centeredNoiseFrame m).mulVec (fun i => z (Sum.inl i))) a ^ 2) +
          (∑ a, branchNoiseEnergy m energy k
            (branchOrthoNoiseLift m k (fun j => z (Sum.inr (a, j))))) = _
      rw [centeredNoise_frame_mulVec, centeredNoiseFrame_mulVec_energy]
      simp_rw [ih]
      rfl

def vertexOrthoInputLift (m k : ℕ) :
    (VertexBallInnovation (m + 2) k → ℝ) →ₗ[ℝ] (VertexGaussianInput m k → ℝ) where
  toFun z := Sum.elim (fun i => z (Sum.inl i))
    (fun aj => branchOrthoNoiseLift m k (fun j => z (Sum.inr (aj.1, j))) aj.2)
  map_add' z w := by
    ext j
    cases j with
    | inl i => rfl
    | inr aj => exact congrFun (branchOrthoNoiseLift_add m k _ _) aj.2
  map_smul' a z := by
    ext j
    cases j with
    | inl i => rfl
    | inr aj => exact congrFun (branchOrthoNoiseLift_smul m k a _) aj.2

def edgeOrthoInputLift (m k : ℕ) :
    (EdgeBallInnovation (m + 2) k → ℝ) →ₗ[ℝ] (EdgeGaussianInput m k → ℝ) where
  toFun z := Sum.elim (fun b => z (Sum.inl b))
    (fun bj => branchOrthoNoiseLift m k (fun j => z (Sum.inr (bj.1, j))) bj.2)
  map_add' z w := by
    ext j
    cases j with
    | inl b => rfl
    | inr bj => exact congrFun (branchOrthoNoiseLift_add m k _ _) bj.2
  map_smul' a z := by
    ext j
    cases j with
    | inl b => rfl
    | inr bj => exact congrFun (branchOrthoNoiseLift_smul m k a _) bj.2

def vertexOrthoGaussianMap (m k : ℕ) (energy : ℝ) :
    (VertexBallInnovation (m + 2) k → ℝ) →ₗ[ℝ] (VertexBallVertex (m + 2) k → ℝ) :=
  (vertexGaussianMap m k energy).comp (vertexOrthoInputLift m k)

def edgeOrthoGaussianMap (m k : ℕ) (energy : ℝ) :
    (EdgeBallInnovation (m + 2) k → ℝ) →ₗ[ℝ] (EdgeBallVertex (m + 2) k → ℝ) :=
  (edgeGaussianMap m k energy).comp (edgeOrthoInputLift m k)

end GaussianWave.BS
