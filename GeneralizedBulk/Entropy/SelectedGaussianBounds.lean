import GeneralizedBulk.Entropy.SelectedGaussian
import GeneralizedBulk.Gaussian.CoordinateLaw

/-! The computed density factors retain exactly the selected coordinate
variances and the inherited covariance lower bound. -/
noncomputable section
open scoped BigOperators Classical NNReal

namespace GeneralizedBulk.Entropy
open GeneralizedBulk.Gaussian GeneralizedBulk.Covariance

variable {I J K : Type*} [Fintype I] [DecidableEq I] [Fintype J] [Fintype K] [DecidableEq K]

theorem selectedGaussianFactor_coordinateVariance (A : Matrix I J ℝ) (e : K → I)
    (he : Function.Injective e) (lo : ℝ) (hlo : 0 < lo)
    (hbound : ∀ x : I → ℝ,lo*(∑ i,x i^2) ≤ dotProduct x ((A*A.transpose).mulVec x)) (i : K) :
    coordinateVariance (selectedGaussianFactor A e he lo hlo hbound) i = coordinateVariance A (e i) := by
  apply NNReal.eq
  rw [coordinateVariance_eq_covariance_diagonal,selectedGaussianFactor_covariance]
  exact (coordinateVariance_eq_covariance_diagonal A (e i)).symm

theorem selectedGaussianFactor_lower (A : Matrix I J ℝ) (e : K → I)
    (he : Function.Injective e) (lo : ℝ) (hlo : 0 < lo)
    (hbound : ∀ x : I → ℝ,lo*(∑ i,x i^2) ≤ dotProduct x ((A*A.transpose).mulVec x)) (x : K → ℝ) :
    lo*(∑ i,x i^2) ≤ dotProduct x ((selectedGaussianFactor A e he lo hlo hbound*
      (selectedGaussianFactor A e he lo hlo hbound).transpose).mulVec x) := by
  rw [selectedGaussianFactor_covariance,← coordinateSelection_congruence,quadratic_compression]
  simpa only [transpose_mulVec_sq_sum _ (coordinateSelection_orthonormal e he) x] using
    hbound ((coordinateSelection e).transpose.mulVec x)

end GeneralizedBulk.Entropy
