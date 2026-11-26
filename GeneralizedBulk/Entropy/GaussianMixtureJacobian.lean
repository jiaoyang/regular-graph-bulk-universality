import GeneralizedBulk.Analysis.LinearDensityEntropy
import GeneralizedBulk.Analysis.CoordinateEntropy
import GeneralizedBulk.Entropy.GaussianMixtureLaw

/-! Actual finite Gaussian-mixture entropy under nonsingular linear maps and
finite coordinate permutations. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Matrix
namespace GeneralizedBulk.Entropy
open GeneralizedBulk.Analysis
variable {I J S : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype S]

theorem affineGaussianPDF_identity (mean x : I → ℝ) :
    affineGaussianPDF mean (1 : Matrix I I ℝ) x = standardGaussianPDF (x - mean) := by
  simp [affineGaussianPDF, linearGaussianPDF]

theorem gaussianMixturePDF_linear_identity (weight : S → ℝ) (mean : S → I → ℝ)
    (M : Matrix I I ℝ) (hM : M.det ≠ 0) :
    gaussianMixturePDF weight (fun s => M.mulVec (mean s)) (fun _ => M) =
      linearDensity M (gaussianMixturePDF weight mean (fun _ => 1)) := by
  funext x
  simp only [gaussianMixturePDF, affineGaussianPDF, linearGaussianPDF, linearDensity,
    Matrix.det_one, abs_one, inv_one, Matrix.one_mulVec, one_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM), Matrix.one_mulVec]
  ring

theorem gaussianMixture_entropy_linear_identity (weight : S → ℝ) (mean : S → I → ℝ)
    (hw : ∀ s, 0 ≤ weight s) (hnorm : ∑ s, weight s = 1)
    (M : Matrix I I ℝ) (hM : M.det ≠ 0) :
    differentialEntropy (gaussianMixturePDF weight (fun s => M.mulVec (mean s)) (fun _ => M)) =
      differentialEntropy (gaussianMixturePDF weight mean (fun _ => 1)) + Real.log (|M.det|) := by
  rw [gaussianMixturePDF_linear_identity weight mean M hM]
  have hp := gaussianMixtureLaw_probability weight mean (fun _ => (1 : Matrix I I ℝ)) hw hnorm
    (fun _ => by simp)
  rw [gaussianMixtureLaw_eq_withDensity weight mean (fun _ => (1 : Matrix I I ℝ)) hw
    (fun _ => by simp)] at hp
  exact linearDensity_entropy_change M hM _ (measurable_gaussianMixturePDF _ _ _)
    (gaussianMixturePDF_pos _ _ _ hw hnorm (fun _ => by simp))
    (integrable_gaussianMixturePDF_mul_log _ _ _ hw hnorm (fun _ => by simp)) hp

theorem standardGaussianPDF_coordinate (e : I ≃ J) (x : J → ℝ) :
    standardGaussianPDF x = standardGaussianPDF (fun i => x (e i)) := by
  exact (Equiv.prod_comp e (fun j => ProbabilityTheory.gaussianPDFReal 0 1 (x j))).symm

theorem gaussianMixturePDF_coordinate_identity (e : I ≃ J) (weight : S → ℝ) (mean : S → I → ℝ) :
    gaussianMixturePDF weight (fun s j => mean s (e.symm j)) (fun _ => (1 : Matrix J J ℝ)) =
      coordinateDensity e (gaussianMixturePDF weight mean (fun _ => (1 : Matrix I I ℝ))) := by
  funext x
  simp only [gaussianMixturePDF, coordinateDensity, affineGaussianPDF_identity]
  apply Finset.sum_congr rfl
  intro s hs
  congr 1
  rw [standardGaussianPDF_coordinate e]
  congr 1
  funext i
  simp

theorem gaussianMixture_entropy_coordinate_identity (e : I ≃ J) (weight : S → ℝ) (mean : S → I → ℝ) :
    differentialEntropy (gaussianMixturePDF weight (fun s j => mean s (e.symm j))
      (fun _ => (1 : Matrix J J ℝ))) =
      differentialEntropy (gaussianMixturePDF weight mean (fun _ => (1 : Matrix I I ℝ))) := by
  rw [gaussianMixturePDF_coordinate_identity, differentialEntropy_coordinateDensity]

theorem affineGaussianPDF_coordinate (e : I ≃ J) (mean : I → ℝ) (M : Matrix I I ℝ) (x : J → ℝ) :
    affineGaussianPDF (fun j => mean (e.symm j)) (M.submatrix e.symm e.symm) x =
      affineGaussianPDF mean M (fun i => x (e i)) := by
  simp only [affineGaussianPDF, linearGaussianPDF, Matrix.det_submatrix_equiv_self,
    Matrix.inv_submatrix_equiv, Matrix.submatrix_mulVec_equiv]
  rw [standardGaussianPDF_coordinate e]
  congr 2
  funext i
  simp [Function.comp_def, Pi.sub_def]

theorem gaussianMixturePDF_coordinate (e : I ≃ J) (weight : S → ℝ) (mean : S → I → ℝ)
    (M : S → Matrix I I ℝ) :
    gaussianMixturePDF weight (fun s j => mean s (e.symm j))
      (fun s => (M s).submatrix e.symm e.symm) =
      coordinateDensity e (gaussianMixturePDF weight mean M) := by
  funext x
  simp only [gaussianMixturePDF, coordinateDensity, affineGaussianPDF_coordinate]

theorem gaussianMixture_entropy_coordinate (e : I ≃ J) (weight : S → ℝ) (mean : S → I → ℝ)
    (M : S → Matrix I I ℝ) :
    differentialEntropy (gaussianMixturePDF weight (fun s j => mean s (e.symm j))
      (fun s => (M s).submatrix e.symm e.symm)) =
      differentialEntropy (gaussianMixturePDF weight mean M) := by
  rw [gaussianMixturePDF_coordinate, differentialEntropy_coordinateDensity]

end GeneralizedBulk.Entropy
