import GeneralizedBulk.Entropy.FiniteSampleLaw
import GeneralizedBulk.Entropy.GaussianMixtureLaw
import GeneralizedBulk.Gaussian.CovarianceLaw

/-! Finite sampling of actual Gaussian coordinate observations is the
computed finite Gaussian mixture; covariance factors are proved by linear
characteristic uniqueness, rather than assumed marginal laws. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace GeneralizedBulk.Entropy
open GeneralizedBulk.Gaussian

variable {I J K S : Type*} [Fintype I] [Fintype J] [Fintype K] [DecidableEq K] [Fintype S]

theorem projected_shifted_gaussian_law (A : Matrix I J ℝ) (mean : I → ℝ)
    (L : Matrix K I ℝ) (B : Matrix K K ℝ)
    (hcov : (L*A)*(L*A).transpose = B*B.transpose) :
    Measure.map (fun x => L.mulVec (mean+x)) (linearImageGaussian A) =
      affineGaussian (L.mulVec mean) B := by
  have he : (fun x => L.mulVec (mean+x)) = (fun y => L.mulVec mean+y) ∘ (fun x => L.mulVec x) := by
    funext x
    exact Matrix.mulVec_add L mean x
  rw [he,← Measure.map_map (by fun_prop) (measurable_finiteMatrixAction L),linearImageGaussian_map_matrix]
  exact shifted_rectangularGaussian_eq_affine _ _ B hcov

theorem finiteSampleLaw_projected_gaussian (A : Matrix I J ℝ) (mean : I → ℝ)
    (weight : S → ℝ) (L : S → Matrix K I ℝ) (B : S → Matrix K K ℝ)
    (hcov : ∀ s,(L s*A)*(L s*A).transpose = B s*(B s).transpose) :
    finiteSampleLaw (linearImageGaussian A) weight (fun s x => (L s).mulVec (mean+x)) =
      gaussianMixtureLaw weight (fun s => (L s).mulVec mean) B := by
  unfold finiteSampleLaw gaussianMixtureLaw
  apply Finset.sum_congr rfl
  intro s hs
  rw [projected_shifted_gaussian_law A mean (L s) (B s) (hcov s)]

end GeneralizedBulk.Entropy
