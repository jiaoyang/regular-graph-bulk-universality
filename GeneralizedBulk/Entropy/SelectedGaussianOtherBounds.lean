import GeneralizedBulk.Entropy.SelectedGaussianBounds
import GeneralizedBulk.Matrix.CoordinateCompression

/-! A selected Gaussian factor inherits every genuine covariance bound,
independently of the floor used to construct its square root. -/
noncomputable section
open scoped BigOperators Classical
namespace GeneralizedBulk.Entropy
open GeneralizedBulk.Covariance
variable {I J K : Type*} [Fintype I] [DecidableEq I] [Fintype J] [Fintype K] [DecidableEq K]

theorem selectedGaussianFactor_other_bounds (A : Matrix I J ℝ) (e : K → I)
    (he : Function.Injective e) (lo : ℝ) (hlo : 0 < lo)
    (hbound : ∀ x : I → ℝ, lo*(∑ i,x i^2) ≤ dotProduct x ((A*A.transpose).mulVec x))
    (κ U : ℝ) (hcov : ∀ x : I → ℝ,
      κ*(∑ i,x i^2) ≤ dotProduct x ((A*A.transpose).mulVec x) ∧
      dotProduct x ((A*A.transpose).mulVec x) ≤ U*(∑ i,x i^2)) (x : K → ℝ) :
    κ*(∑ i,x i^2) ≤ dotProduct x ((selectedGaussianFactor A e he lo hlo hbound*
      (selectedGaussianFactor A e he lo hlo hbound).transpose).mulVec x) ∧
    dotProduct x ((selectedGaussianFactor A e he lo hlo hbound*
      (selectedGaussianFactor A e he lo hlo hbound).transpose).mulVec x) ≤ U*(∑ i,x i^2) := by
  rw [selectedGaussianFactor_covariance]
  exact coordinate_compression_bounds _ e he κ U hcov x

theorem covariance_diagonal_le_of_quadratic_upper (Q : Matrix K K ℝ) (U : ℝ)
    (hQ : ∀ x : K → ℝ, dotProduct x (Q.mulVec x) ≤ U*(∑ i,x i^2)) (i : K) : Q i i ≤ U := by
  have hh := hQ (Pi.single i 1)
  simpa [dotProduct, Matrix.mulVec, Pi.single_apply] using hh

theorem covariance_trace_le_of_quadratic_upper (Q : Matrix K K ℝ) (U : ℝ)
    (hQ : ∀ x : K → ℝ, dotProduct x (Q.mulVec x) ≤ U*(∑ i,x i^2)) :
    Matrix.trace Q ≤ (Fintype.card K : ℝ)*U := by
  change (∑ i,Q i i) ≤ _
  exact (Finset.sum_le_sum (fun i _ => covariance_diagonal_le_of_quadratic_upper Q U hQ i)).trans_eq
    (by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul])

end GeneralizedBulk.Entropy
