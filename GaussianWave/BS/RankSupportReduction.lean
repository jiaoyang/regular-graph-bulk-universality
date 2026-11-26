import GaussianWave.BS.SecondMomentTransport
import GaussianWave.BS.HeatCovariance

/-!
# Actual support reconstruction for singular Gram covariances

The measure need not be Gaussian. Its finite second moments alone force it
to equal the pushforward of its reduced coordinates under a full-column Gram
factor. This removes zero-variance directions before any entropy calculation.
-/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace GaussianWave.BS

theorem gram_leftInverse_reconstruction_ae
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (μ : Measure (I → ℝ)) (hμ : Integrable (squareRadius (I := I)) μ)
    (L : Matrix I J ℝ) (B : Matrix J I ℝ)
    (hC : HasSecondMoments μ (L * L.transpose)) (hBL : B * L = 1) :
    ∀ᵐ x ∂μ, L.mulVec (B.mulVec x) = x := by
  let R : Matrix I I ℝ := 1 - L * B
  have hRL : R * L = 0 := by
    dsimp [R]
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hBL, Matrix.mul_one, sub_self]
  have hzero : R * (L * L.transpose) * R.transpose = 0 := by
    calc
      _ = (R * L) * (R * L).transpose := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hRL]; simp
  have hm := secondMoments_matrixImage μ hμ (L * L.transpose) hC R
  rw [hzero] at hm
  have hcoord (i : I) : ∀ᵐ x ∂μ, R.mulVec x i = 0 := by
    have hmom := hm i i
    rw [integral_map (measurable_finiteMatrixAction R).aemeasurable
      ((continuous_apply i).mul (continuous_apply i)).measurable.aestronglyMeasurable] at hmom
    have hint : (∫ x, (R.mulVec x i) ^ 2 ∂μ) = 0 := by simpa only [pow_two, Matrix.zero_apply] using hmom
    have hi : Integrable (fun x => (R.mulVec x i) ^ 2) μ :=
      integrable_linearForm_sq_of_squareRadius μ hμ (R i)
    have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (R.mulVec x i)) hi).mp hint
    exact hae.mono (fun _ hx => sq_eq_zero_iff.mp hx)
  have hall : ∀ᵐ x ∂μ, ∀ i, R.mulVec x i = 0 := ae_all_iff.mpr hcoord
  filter_upwards [hall] with x hx
  have hz : R.mulVec x = 0 := funext hx
  dsimp [R] at hz
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec] at hz
  exact (sub_eq_zero.mp hz).symm

theorem gram_leftInverse_reconstruction_law
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (μ : Measure (I → ℝ)) (hμ : Integrable (squareRadius (I := I)) μ)
    (L : Matrix I J ℝ) (B : Matrix J I ℝ)
    (hC : HasSecondMoments μ (L * L.transpose)) (hBL : B * L = 1) :
    Measure.map (fun y => L.mulVec y) (Measure.map (fun x => B.mulVec x) μ) = μ := by
  rw [Measure.map_map (measurable_finiteMatrixAction L) (measurable_finiteMatrixAction B)]
  change Measure.map (fun x => L.mulVec (B.mulVec x)) μ = μ
  rw [Measure.map_congr (gram_leftInverse_reconstruction_ae μ hμ L B hC hBL)]
  exact Measure.map_id

/-- Gaussianity of the reduced coordinates reconstructs the correct actual
possibly singular ambient Gaussian. The reduction and support assertions
are proved from the source second moments before Gaussianity is used. -/
theorem gaussian_of_standard_whitened_gram_law
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ)
    (L : Matrix I J ℝ) (B : Matrix J I ℝ)
    (hC : HasSecondMoments μ (L * L.transpose)) (hBL : B * L = 1)
    (hwhite : Measure.map (fun x => B.mulVec x) μ = standardVector J) :
    μ = linearImageGaussian L := by
  rw [← gram_leftInverse_reconstruction_law μ hμ L B hC hBL, hwhite]
  rfl

end GaussianWave.BS
