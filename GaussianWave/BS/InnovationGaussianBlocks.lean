import GaussianWave.BS.InnovationNodeCoordinates
import GaussianWave.GaussianProduct

/-!
# The reference sibling innovations are actual independent Gaussian blocks
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianWave.BS

def independentBlockFactor {A I J : Type*} [DecidableEq A] (L : Matrix I J ℝ) :
    Matrix (A × I) (A × J) ℝ := fun ai bj => if bj.1 = ai.1 then L ai.2 bj.2 else 0

theorem independentBlockFactor_mulVec {A I J : Type*} [Fintype A] [Fintype J] [DecidableEq A]
    (L : Matrix I J ℝ) (z : A × J → ℝ) (a : A) (i : I) :
    (independentBlockFactor (A := A) L).mulVec z (a, i) = L.mulVec (fun j => z (a, j)) i := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, independentBlockFactor, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

theorem independentBlockFactor_gram {A I J : Type*} [Fintype A] [Fintype J] [DecidableEq A]
    (L : Matrix I J ℝ) :
    independentBlockFactor (A := A) L * (independentBlockFactor (A := A) L).transpose =
      channelBlockCovariance (fun _ : A => L * L.transpose) := by
  ext ai bi
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_prod_type,
    independentBlockFactor, channelBlockCovariance]
  by_cases hab : ai.1 = bi.1
  · rw [hab]
    simp only [if_pos rfl]
    have he (a : A) (j : J) :
        (if a = bi.1 then L ai.2 j else 0) * (if a = bi.1 then L bi.2 j else 0) =
        if a = bi.1 then L ai.2 j * L bi.2 j else 0 := by split_ifs <;> simp
    simp_rw [he]
    rw [Finset.sum_comm]
    simp
  · rw [if_neg hab]
    have he (a : A) (j : J) :
        (if a = ai.1 then L ai.2 j else 0) * (if a = bi.1 then L bi.2 j else 0) = 0 := by
      split_ifs with ha hb hb <;> simp_all
    simp_rw [he]
    simp

theorem real_rowGram_posSemidef {I J : Type*} [Fintype I] [Fintype J] (L : Matrix I J ℝ) :
    (L * L.transpose).PosSemidef := by
  simpa only [Matrix.conjTranspose, star_trivial, Matrix.map_id] using
    Matrix.posSemidef_self_mul_conjTranspose L

theorem independentBlockFactor_gaussian_product {A I J : Type*}
    [Fintype A] [Fintype I] [Fintype J] [DecidableEq A] [DecidableEq I]
    (L : Matrix I J ℝ) :
    linearImageGaussian (independentBlockFactor (A := A) L) =
      Measure.map flattenChannels (Measure.pi (fun _ : A =>
        gaussianCovarianceLaw (L * L.transpose) (real_rowGram_posSemidef L))) := by
  apply gaussian_eq_flattened_product _ (fun _ : A => L * L.transpose)
    (fun _ => real_rowGram_posSemidef L)
  rw [← independentBlockFactor_gram]
  exact linearImageGaussian_characteristic _

def rawSiblingFactor (m : ℕ) (scale : ℝ) : Matrix (Fin m) (Fin (m + 1)) ℝ :=
  fun i j => scale * ((if j = i.succ then 1 else 0) - (if j = 0 then 1 else 0))

theorem rawSiblingFactor_mulVec (m : ℕ) (scale : ℝ) (z : Fin (m + 1) → ℝ) (i : Fin m) :
    (rawSiblingFactor m scale).mulVec z i = scale * (z i.succ - z 0) := by
  simp only [Matrix.mulVec, dotProduct, rawSiblingFactor, mul_sub, sub_mul, mul_assoc,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

def siblingInnovationGaussian (m : ℕ) (scale : ℝ) : Measure (Fin m → ℝ) :=
  gaussianCovarianceLaw (rawSiblingFactor m scale * (rawSiblingFactor m scale).transpose)
    (real_rowGram_posSemidef (rawSiblingFactor m scale))

instance siblingInnovationGaussian_probability (m : ℕ) (scale : ℝ) :
    IsProbabilityMeasure (siblingInnovationGaussian m scale) := by unfold siblingInnovationGaussian; infer_instance

def branchInnovationNodeLaw (m k : ℕ) (scale : ℝ) :
    Measure ((BranchInternalNode (m + 1) k × Fin m) → ℝ) :=
  Measure.map (fun z => fun ni => branchNoiseInnovation m k scale z ((branchInnovationNodeEquiv m k).symm ni))
    (standardVector (BranchNoise (m + 1) k))

/-- The actual finite branch innovation law, after literal node labeling,
is a product over independent internal-vertex Gaussian vectors. -/
theorem branchInnovationNodeLaw_eq_product (m k : ℕ) (scale : ℝ) :
    branchInnovationNodeLaw m k scale =
      Measure.map flattenChannels (Measure.pi (fun _ : BranchInternalNode (m + 1) k =>
        siblingInnovationGaussian m scale)) := by
  let L := independentBlockFactor (A := BranchInternalNode (m + 1) k) (rawSiblingFactor m scale)
  have hf : (fun z : BranchNoise (m + 1) k → ℝ => fun ni =>
      branchNoiseInnovation m k scale z ((branchInnovationNodeEquiv m k).symm ni)) =
      (fun z => L.mulVec (fun nj => z ((branchNoiseNodeEquiv (m + 1) k).symm nj))) := by
    funext z ni
    rcases ni with ⟨node, i⟩
    rw [independentBlockFactor_mulVec, rawSiblingFactor_mulVec]
    exact branchNoiseInnovation_at_node m k scale z node i
  unfold branchInnovationNodeLaw
  rw [hf]
  change Measure.map (L.mulVec ∘
    (fun z : BranchNoise (m + 1) k → ℝ => fun nj => z ((branchNoiseNodeEquiv (m + 1) k).symm nj))) _ = _
  rw [← Measure.map_map (measurable_finiteMatrixAction L) (by fun_prop),
    standardVector_map_coordinateRestriction _ (branchNoiseNodeEquiv (m + 1) k).symm.injective]
  exact independentBlockFactor_gaussian_product (A := BranchInternalNode (m + 1) k) (rawSiblingFactor m scale)

end GaussianWave.BS
