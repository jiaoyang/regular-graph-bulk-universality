import GaussianWave.BS.EigenBallCoordinates
import GaussianWave.BS.PhysicalStarMap
import GaussianWave.BS.GaussianEntropyWitness

/-!
# Finite Gaussian-wave construction from independent noises

Each internal branch vertex receives an independent `q`-vector of standard
normals, projected to its zero-sum subspace.  The deterministic reconstruction
has the eigenrelation pointwise.  The noise representation is deliberately
redundant; the actual eigen-solution chart remains the nonredundant sibling-
difference chart of `EigenBallCoordinates`.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianWave.BS

def BranchNoise (q : ℕ) : ℕ → Type
  | 0 => Empty
  | k + 1 => Fin q ⊕ (Fin q × BranchNoise q k)

instance branchNoiseFintype (q k : ℕ) : Fintype (BranchNoise q k) := by
  induction k with
  | zero => exact inferInstanceAs (Fintype Empty)
  | succ k ih =>
      letI := ih
      exact inferInstanceAs (Fintype (Fin q ⊕ (Fin q × BranchNoise q k)))

instance branchNoiseDecidableEq (q k : ℕ) : DecidableEq (BranchNoise q k) := Classical.decEq _

def siblingVariance (d : ℕ) (energy : ℝ) : ℝ :=
  ((d : ℝ) ^ 2 - energy ^ 2) / ((d : ℝ) * ((d : ℝ) - 1))

theorem siblingVariance_pos (d : ℕ) (hd : 2 ≤ d) (energy : ℝ)
    (he : |energy| < (d : ℝ)) : 0 < siblingVariance d energy := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  apply div_pos
  · apply sub_pos.mpr
    simpa only [sq_abs] using (sq_lt_sq₀ (abs_nonneg energy) (by linarith)).mpr he
  · exact mul_pos (by linarith) (by linarith)

def centeredNoise {q : ℕ} (z : Fin q → ℝ) (a : Fin q) : ℝ :=
  z a - (∑ b, z b) / q

theorem sum_centeredNoise (q : ℕ) (hq : 0 < q) (z : Fin q → ℝ) :
    (∑ a, centeredNoise z a) = 0 := by
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp only [centeredNoise, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_div_cancel₀ _ hqR, sub_self]

def branchNoiseInnovation (m : ℕ) : (k : ℕ) → ℝ →
    (BranchNoise (m + 1) k → ℝ) → (BranchInnovation (m + 1) k → ℝ)
  | 0, _, _ => Empty.elim
  | k + 1, scale, z => Sum.elim
      (fun i => scale * (z (Sum.inl i.succ) - z (Sum.inl 0)))
      (fun aj => branchNoiseInnovation m k scale (fun j => z (Sum.inr (aj.1, j))) aj.2)

theorem branchNoiseInnovation_add (m k : ℕ) (scale : ℝ)
    (z w : BranchNoise (m + 1) k → ℝ) :
    branchNoiseInnovation m k scale (z + w) =
      branchNoiseInnovation m k scale z + branchNoiseInnovation m k scale w := by
  induction k with
  | zero => ext i; exact Empty.elim i
  | succ k ih =>
      ext j
      cases j with
      | inl i => simp only [branchNoiseInnovation, Sum.elim_inl, Pi.add_apply]; ring
      | inr aj => exact congrFun (ih _ _) aj.2

theorem branchNoiseInnovation_smul (m k : ℕ) (scale a : ℝ)
    (z : BranchNoise (m + 1) k → ℝ) :
    branchNoiseInnovation m k scale (a • z) = a • branchNoiseInnovation m k scale z := by
  induction k with
  | zero => ext i; exact Empty.elim i
  | succ k ih =>
      ext j
      cases j with
      | inl i =>
          simp only [branchNoiseInnovation, Sum.elim_inl, Pi.smul_apply, smul_eq_mul]
          ring
      | inr aj => exact congrFun (ih (fun j => z (Sum.inr (aj.1, j)))) aj.2

def branchNoiseInnovationLinear (m k : ℕ) (scale : ℝ) :
    (BranchNoise (m + 1) k → ℝ) →ₗ[ℝ] (BranchInnovation (m + 1) k → ℝ) where
  toFun := branchNoiseInnovation m k scale
  map_add' := branchNoiseInnovation_add m k scale
  map_smul' := branchNoiseInnovation_smul m k scale

def branchNoiseRightInverse (m : ℕ) : (k : ℕ) → ℝ →
    (BranchInnovation (m + 1) k → ℝ) → (BranchNoise (m + 1) k → ℝ)
  | 0, _, _ => Empty.elim
  | k + 1, scale, z => Sum.elim
      (Fin.cases 0 (fun i => z (Sum.inl i) / scale))
      (fun aj => branchNoiseRightInverse m k scale (fun j => z (Sum.inr (aj.1, j))) aj.2)

theorem branchNoiseInnovation_rightInverse (m k : ℕ) (scale : ℝ) (hs : scale ≠ 0)
    (z : BranchInnovation (m + 1) k → ℝ) :
    branchNoiseInnovation m k scale (branchNoiseRightInverse m k scale z) = z := by
  induction k with
  | zero => ext i; exact Empty.elim i
  | succ k ih =>
      ext j
      cases j with
      | inl i =>
          simp only [branchNoiseInnovation, branchNoiseRightInverse, Sum.elim_inl,
            Fin.cases_succ, Fin.cases_zero, sub_zero, mul_div_cancel₀ _ hs]
      | inr aj => exact congrFun (ih (fun j => z (Sum.inr (aj.1, j)))) aj.2

def gaussianBranchBuild (m k : ℕ) (energy parent root : ℝ)
    (z : BranchNoise (m + 1) k → ℝ) : BranchVertex (m + 1) k → ℝ :=
  branchBuild m k energy parent root
    (branchNoiseInnovation m k (Real.sqrt (siblingVariance (m + 2) energy)) z)

theorem gaussianBranchBuild_eigenrelation (m k : ℕ) (energy parent root : ℝ)
    (z : BranchNoise (m + 1) k → ℝ) :
    BranchEigenrelation m k energy parent (gaussianBranchBuild m k energy parent root z) :=
  branchBuild_eigenrelation _ _ _ _ _ _

/-- The recursion really is the eigenrelation conditional mean plus a
centered independent Gaussian sibling-noise vector. -/
theorem siblingFill_noise (m : ℕ) (total scale : ℝ) (z : Fin (m + 1) → ℝ) :
    siblingFill m total (fun i => scale * (z i.succ - z 0)) =
      fun a => total / (m + 1) + scale * centeredNoise z a := by
  have hs : (∑ i : Fin m, scale * (z i.succ - z 0)) =
      scale * ((∑ a : Fin (m + 1), z a) - (m + 1 : ℝ) * z 0) := by
    rw [Fin.sum_univ_succ]
    simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  ext a
  refine Fin.cases ?_ (fun i => ?_) a <;>
    simp only [siblingFill_zero, siblingFill_succ, hs, centeredNoise,
      Nat.cast_add, Nat.cast_one] <;> field_simp <;> ring

abbrev VertexGaussianInput (m k : ℕ) := Fin (m + 2) ⊕ (Fin (m + 2) × BranchNoise (m + 1) k)
abbrev EdgeGaussianInput (m k : ℕ) := Bool ⊕ (Bool × BranchNoise (m + 1) k)

def vertexGaussianInnovation (m k : ℕ) (energy : ℝ)
    (z : VertexGaussianInput m k → ℝ) : VertexBallInnovation (m + 2) k → ℝ :=
  Sum.elim
    (fun a => physicalStarMap (m + 2) (energy / (m + 2)) (fun j => z (Sum.inl j)) a.succ -
      physicalStarMap (m + 2) (energy / (m + 2)) (fun j => z (Sum.inl j)) 0)
    (fun aj => branchNoiseInnovation m k (Real.sqrt (siblingVariance (m + 2) energy))
      (fun j => z (Sum.inr (aj.1, j))) aj.2)

def edgeGaussianInnovation (m k : ℕ) (energy : ℝ)
    (z : EdgeGaussianInput m k → ℝ) : EdgeBallInnovation (m + 2) k → ℝ :=
  Sum.elim
    (fun b => (physicalEdgeMatrix (energy / (m + 2))).mulVec (fun j => z (Sum.inl j)) b)
    (fun bj => branchNoiseInnovation m k (Real.sqrt (siblingVariance (m + 2) energy))
      (fun j => z (Sum.inr (bj.1, j))) bj.2)

def vertexGaussianInnovationLinear (m k : ℕ) (energy : ℝ) :
    (VertexGaussianInput m k → ℝ) →ₗ[ℝ] (VertexBallInnovation (m + 2) k → ℝ) where
  toFun := vertexGaussianInnovation m k energy
  map_add' z w := by
    ext j
    cases j with
    | inl a =>
        change physicalStarMap _ _ ((fun j => z (Sum.inl j)) + (fun j => w (Sum.inl j))) a.succ -
          physicalStarMap _ _ ((fun j => z (Sum.inl j)) + (fun j => w (Sum.inl j))) 0 = _
        rw [(physicalStarMap _ _).map_add]
        simp only [Pi.add_apply, vertexGaussianInnovation, Sum.elim_inl]
        ring
    | inr aj => exact congrFun (branchNoiseInnovation_add m k _ _ _) aj.2
  map_smul' a z := by
    ext j
    cases j with
    | inl i =>
        change physicalStarMap _ _ (a • (fun j => z (Sum.inl j))) i.succ -
          physicalStarMap _ _ (a • (fun j => z (Sum.inl j))) 0 = _
        rw [(physicalStarMap _ _).map_smul]
        simp only [Pi.smul_apply, smul_eq_mul, vertexGaussianInnovation, Sum.elim_inl,
          RingHom.id_apply]
        ring
    | inr aj => exact congrFun (branchNoiseInnovation_smul m k _ a _) aj.2

def edgeGaussianInnovationLinear (m k : ℕ) (energy : ℝ) :
    (EdgeGaussianInput m k → ℝ) →ₗ[ℝ] (EdgeBallInnovation (m + 2) k → ℝ) where
  toFun := edgeGaussianInnovation m k energy
  map_add' z w := by
    ext j
    cases j with
    | inl b =>
        exact congrFun ((physicalEdgeMatrix (energy / (m + 2))).mulVecLin.map_add
          (fun j => z (Sum.inl j)) (fun j => w (Sum.inl j))) b
    | inr bj => exact congrFun (branchNoiseInnovation_add m k _ _ _) bj.2
  map_smul' a z := by
    ext j
    cases j with
    | inl b =>
        exact congrFun ((physicalEdgeMatrix (energy / (m + 2))).mulVecLin.map_smul a
          (fun j => z (Sum.inl j))) b
    | inr bj => exact congrFun (branchNoiseInnovation_smul m k _ a _) bj.2

def vertexGaussianMap (m k : ℕ) (energy : ℝ) :
    (VertexGaussianInput m k → ℝ) →ₗ[ℝ] (VertexBallVertex (m + 2) k → ℝ) :=
  (vertexBallBuildLinear m k energy).comp (vertexGaussianInnovationLinear m k energy)

def edgeGaussianMap (m k : ℕ) (energy : ℝ) :
    (EdgeGaussianInput m k → ℝ) →ₗ[ℝ] (EdgeBallVertex (m + 2) k → ℝ) :=
  (edgeBallBuildLinear m k energy).comp (edgeGaussianInnovationLinear m k energy)

def vertexGaussianBallLaw (m k : ℕ) (energy : ℝ) : Measure (VertexBallVertex (m + 2) k → ℝ) :=
  Measure.map (vertexGaussianMap m k energy) (standardVector (VertexGaussianInput m k))

def edgeGaussianBallLaw (m k : ℕ) (energy : ℝ) : Measure (EdgeBallVertex (m + 2) k → ℝ) :=
  Measure.map (edgeGaussianMap m k energy) (standardVector (EdgeGaussianInput m k))

instance vertexGaussianBallLaw_probability (m k : ℕ) (energy : ℝ) :
    IsProbabilityMeasure (vertexGaussianBallLaw m k energy) :=
  isProbabilityMeasure_map (vertexGaussianMap m k energy).continuous_of_finiteDimensional.measurable.aemeasurable

instance edgeGaussianBallLaw_probability (m k : ℕ) (energy : ℝ) :
    IsProbabilityMeasure (edgeGaussianBallLaw m k energy) :=
  isProbabilityMeasure_map (edgeGaussianMap m k energy).continuous_of_finiteDimensional.measurable.aemeasurable

theorem vertexGaussianMap_eigenrelation (m k : ℕ) (energy : ℝ)
    (he : energy ≠ (m + 2 : ℝ)) (z : VertexGaussianInput m k → ℝ) :
    VertexBallEigenrelation m k energy (vertexGaussianMap m k energy z) :=
  vertexBallBuild_eigenrelation m k energy he _

theorem edgeGaussianMap_eigenrelation (m k : ℕ) (energy : ℝ)
    (z : EdgeGaussianInput m k → ℝ) :
    EdgeBallEigenrelation m k energy (edgeGaussianMap m k energy z) :=
  edgeBallBuild_eigenrelation m k energy _

end GaussianWave.BS
