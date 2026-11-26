import GeneralizedBulk.Gaussian.FiniteVector
import GeneralizedBulk.Entropy.GaussianShiftEntropy

/-! Actual rectangular Gaussian observations depend only on their computed covariance. -/
noncomputable section
open MeasureTheory
namespace GeneralizedBulk.Gaussian
variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]

theorem linearImageGaussian_eq_of_covariance (A : Matrix I J ℝ) (B : Matrix I K ℝ)
    (hcov : A*A.transpose=B*B.transpose) : linearImageGaussian A=linearImageGaussian B := by
  apply measure_eq_of_linear_characteristic
  intro t
  change (∫ x, Complex.exp ((finiteLinearForm t x : ℂ) * Complex.I) ∂linearImageGaussian A) =
    ∫ x, Complex.exp ((finiteLinearForm t x : ℂ) * Complex.I) ∂linearImageGaussian B
  rw [linearImageGaussian_characteristic A t, linearImageGaussian_characteristic B t, hcov]

theorem linearImageGaussian_map_matrix {L : Type*} [Fintype L]
    (A : Matrix I J ℝ) (B : Matrix L I ℝ) :
    (linearImageGaussian A).map (fun x => B.mulVec x) = linearImageGaussian (B*A) := by
  rw [linearImageGaussian, Measure.map_map (measurable_finiteMatrixAction B) (measurable_finiteMatrixAction A)]
  congr 1
  funext x
  exact Matrix.mulVec_mulVec x B A

theorem shifted_rectangularGaussian_eq_affine [DecidableEq I]
    (mean : I → ℝ) (A : Matrix I J ℝ) (B : Matrix I I ℝ) (hcov : A*A.transpose=B*B.transpose) :
    (linearImageGaussian A).map (fun x => mean+x) = GeneralizedBulk.Entropy.affineGaussian mean B := by
  rw [linearImageGaussian_eq_of_covariance A B hcov]
  rfl

end GeneralizedBulk.Gaussian
