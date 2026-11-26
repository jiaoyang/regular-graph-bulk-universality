import GeneralizedBulk.Entropy.SelectedGaussianBounds

/-! Actual coordinate-variance bounds control the trace of every selected
Gaussian covariance, independently of the original ambient dimension. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.Entropy
open GeneralizedBulk.Gaussian
variable {I J K : Type*} [Fintype I] [DecidableEq I] [Fintype J] [Fintype K] [DecidableEq K]

theorem selectedGaussianFactor_trace_le (A : Matrix I J ℝ) (e : K → I)
    (he : Function.Injective e) (lo : ℝ) (hlo : 0 < lo)
    (hbound : ∀ x : I → ℝ,lo*(∑ i,x i^2) ≤ dotProduct x ((A*A.transpose).mulVec x))
    (U : ℝ) (hU : ∀ i,(coordinateVariance A i : ℝ) ≤ U) :
    Matrix.trace (selectedGaussianFactor A e he lo hlo hbound*
      (selectedGaussianFactor A e he lo hlo hbound).transpose) ≤ (Fintype.card K : ℝ)*U := by
  change (∑ i,(selectedGaussianFactor A e he lo hlo hbound*
    (selectedGaussianFactor A e he lo hlo hbound).transpose) i i) ≤ _
  simp_rw [← coordinateVariance_eq_covariance_diagonal,selectedGaussianFactor_coordinateVariance]
  exact (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hU (e i))).trans_eq
    (by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul])

end GeneralizedBulk.Entropy
