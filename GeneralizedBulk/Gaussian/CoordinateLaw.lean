import GeneralizedBulk.Gaussian.FiniteVector

/-! Actual scalar coordinate laws of possibly singular rectangular Gaussian
linear images, with arbitrary deterministic shifts. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace GeneralizedBulk.Gaussian

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def coordinateVariance (A : Matrix I J ℝ) (i : I) : ℝ≥0 :=
  ⟨∑ j,A i j^2,Finset.sum_nonneg (fun j hj => sq_nonneg _)⟩

theorem coordinateVariance_eq_covariance_diagonal (A : Matrix I J ℝ) (i : I) :
    (coordinateVariance A i : ℝ) = (A*A.transpose) i i := by
  change (∑ j,A i j^2) = ∑ j,A i j*A i j
  simp only [pow_two]

set_option maxHeartbeats 1000000 in
theorem linearImageGaussian_coordinate (A : Matrix I J ℝ) (i : I) :
    Measure.map (fun x : I → ℝ => x i) (linearImageGaussian A) = gaussianReal 0 (coordinateVariance A i) := by
  have hpos (t : I → ℝ) : 0 ≤ finiteCovarianceQuadratic (A*A.transpose) t := by
    rw [finiteCovarianceQuadratic_gram]
    exact Finset.sum_nonneg (fun j hj => sq_nonneg _)
  have h := centeredGaussian_linearProjection (linearImageGaussian A) (A*A.transpose) hpos
    (linearImageGaussian_characteristic A) (Pi.single i 1)
  have hf : finiteLinearForm (Pi.single i (1 : ℝ)) = fun x : I → ℝ => x i := by
    funext x
    simp [finiteLinearForm,Pi.single_apply]
  have hq : finiteCovarianceQuadratic (A*A.transpose) (Pi.single i (1 : ℝ)) =
      (coordinateVariance A i : ℝ) := by
    simp [finiteCovarianceQuadratic,Pi.single_apply,coordinateVariance,Matrix.mul_apply,Matrix.transpose_apply,pow_two]
  have hv : (⟨finiteCovarianceQuadratic (A*A.transpose) (Pi.single i (1 : ℝ)),hpos _⟩ : ℝ≥0) =
      coordinateVariance A i := NNReal.eq hq
  rwa [hf,hv] at h

theorem linearImageGaussian_shifted_coordinate (A : Matrix I J ℝ) (a : I → ℝ) (i : I) :
    Measure.map (fun x : I → ℝ => a i+x i) (linearImageGaussian A) =
      gaussianReal (a i) (coordinateVariance A i) := by
  calc
    _ = Measure.map (fun t : ℝ => a i+t) (Measure.map (fun x : I → ℝ => x i) (linearImageGaussian A)) := by
      rw [Measure.map_map (f := fun x : I → ℝ => x i) (g := fun t : ℝ => a i+t)
        (by fun_prop) (measurable_pi_apply i)]
      rfl
    _ = _ := by rw [linearImageGaussian_coordinate,gaussianReal_map_const_add]; simp only [zero_add]

end GeneralizedBulk.Gaussian
