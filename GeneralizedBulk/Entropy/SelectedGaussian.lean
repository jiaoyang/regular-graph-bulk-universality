import GeneralizedBulk.Entropy.ProjectedGaussianMixture
import GeneralizedBulk.Matrix.CoordinateCompression
import GeneralizedBulk.Matrix.CovarianceDeterminant

/-! Nonsingular density factors for actual injective coordinate observations
of a Gaussian vector with a proved covariance lower bound. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace GeneralizedBulk.Entropy
open GeneralizedBulk.Gaussian GeneralizedBulk.Covariance

variable {I J K S : Type*} [Fintype I] [DecidableEq I] [Fintype J]
  [Fintype K] [DecidableEq K] [Fintype S]

theorem selectedGaussian_exists_factor (A : Matrix I J ℝ) (e : K → I)
    (he : Function.Injective e) (lo : ℝ) (hlo : 0 < lo)
    (hbound : ∀ x : I → ℝ,lo*(∑ i,x i^2) ≤ dotProduct x ((A*A.transpose).mulVec x)) :
    ∃ B : Matrix K K ℝ,B*B.transpose = (A*A.transpose).submatrix e e ∧ B.det ≠ 0 := by
  have hHerm : (A*A.transpose).IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.isHermitian_mul_conjTranspose_self A
  exact exists_nonsingular_covariance_factor _ (coordinate_compression_posDef _ hHerm e he lo hlo hbound)

def selectedGaussianFactor (A : Matrix I J ℝ) (e : K → I)
    (he : Function.Injective e) (lo : ℝ) (hlo : 0 < lo)
    (hbound : ∀ x : I → ℝ,lo*(∑ i,x i^2) ≤ dotProduct x ((A*A.transpose).mulVec x)) : Matrix K K ℝ :=
  Classical.choose (selectedGaussian_exists_factor A e he lo hlo hbound)

theorem selectedGaussianFactor_covariance (A : Matrix I J ℝ) (e : K → I)
    (he : Function.Injective e) (lo : ℝ) (hlo : 0 < lo)
    (hbound : ∀ x : I → ℝ,lo*(∑ i,x i^2) ≤ dotProduct x ((A*A.transpose).mulVec x)) :
    selectedGaussianFactor A e he lo hlo hbound*(selectedGaussianFactor A e he lo hlo hbound).transpose =
      (A*A.transpose).submatrix e e :=
  (Classical.choose_spec (selectedGaussian_exists_factor A e he lo hlo hbound)).1

theorem selectedGaussianFactor_det_ne_zero (A : Matrix I J ℝ) (e : K → I)
    (he : Function.Injective e) (lo : ℝ) (hlo : 0 < lo)
    (hbound : ∀ x : I → ℝ,lo*(∑ i,x i^2) ≤ dotProduct x ((A*A.transpose).mulVec x)) :
    (selectedGaussianFactor A e he lo hlo hbound).det ≠ 0 :=
  (Classical.choose_spec (selectedGaussian_exists_factor A e he lo hlo hbound)).2

theorem selectedGaussianFactor_gram (A : Matrix I J ℝ) (e : K → I)
    (he : Function.Injective e) (lo : ℝ) (hlo : 0 < lo)
    (hbound : ∀ x : I → ℝ,lo*(∑ i,x i^2) ≤ dotProduct x ((A*A.transpose).mulVec x)) :
    (coordinateSelection e*A)*(coordinateSelection e*A).transpose =
      selectedGaussianFactor A e he lo hlo hbound*(selectedGaussianFactor A e he lo hlo hbound).transpose := by
  rw [selectedGaussianFactor_covariance,Matrix.transpose_mul,← Matrix.mul_assoc,
    Matrix.mul_assoc (coordinateSelection e) A A.transpose,coordinateSelection_congruence]

theorem finiteSampleLaw_selected_gaussian (A : Matrix I J ℝ) (mean : I → ℝ) (weight : S → ℝ)
    (e : S → K → I) (he : ∀ s,Function.Injective (e s)) (lo : ℝ) (hlo : 0 < lo)
    (hbound : ∀ x : I → ℝ,lo*(∑ i,x i^2) ≤ dotProduct x ((A*A.transpose).mulVec x)) :
    finiteSampleLaw (linearImageGaussian A) weight (fun s x => (mean+x) ∘ e s) =
      gaussianMixtureLaw weight (fun s => mean ∘ e s)
        (fun s => selectedGaussianFactor A (e s) (he s) lo hlo hbound) := by
  have h := finiteSampleLaw_projected_gaussian A mean weight (fun s => coordinateSelection (e s))
    (fun s => selectedGaussianFactor A (e s) (he s) lo hlo hbound)
    (fun s => selectedGaussianFactor_gram A (e s) (he s) lo hlo hbound)
  simpa only [coordinateSelection_mulVec] using h

end GeneralizedBulk.Entropy
