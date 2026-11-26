import GaussianWave.BS.ChannelProcessTransform
import GaussianWave.BS.GaussianIntrinsicDensity

/-! Adding one independent standard Gaussian channel covariance makes
actual root whitening invertible, including zero original covariance. -/
noncomputable section
open MeasureTheory
namespace GaussianWave.BS

variable {I : Type*} [Fintype I] [DecidableEq I]

def positiveRootCovariance (C : Matrix I I ℝ) := C+1

theorem positiveRootCovariance_posDef (C : Matrix I I ℝ) (hC : C.PosSemidef) :
    (positiveRootCovariance C).PosDef := Matrix.PosDef.posSemidef_add hC Matrix.PosDef.one

def positiveRootFactor (C : Matrix I I ℝ) (hC : C.PosSemidef) : Matrix I I ℝ :=
  (positiveRootCovariance_posDef C hC).posSemidef.sqrt

def positiveRootWhitening (C : Matrix I I ℝ) (hC : C.PosSemidef) : Matrix I I ℝ :=
  (positiveRootFactor C hC)⁻¹

theorem positiveRootFactor_det_ne_zero (C : Matrix I I ℝ) (hC : C.PosSemidef) :
    (positiveRootFactor C hC).det ≠ 0 :=
  posDef_sqrt_det_ne_zero _ (positiveRootCovariance_posDef C hC)

theorem positiveRootWhitening_leftInverse (C : Matrix I I ℝ) (hC : C.PosSemidef) :
    positiveRootWhitening C hC * positiveRootFactor C hC = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (positiveRootFactor_det_ne_zero C hC))

theorem positiveRootFactor_gram (C : Matrix I I ℝ) (hC : C.PosSemidef) :
    positiveRootFactor C hC * (positiveRootFactor C hC).transpose=positiveRootCovariance C := by
  have ht : (positiveRootFactor C hC).transpose=positiveRootFactor C hC := by
    simpa only [Matrix.conjTranspose,star_trivial,Matrix.map_id] using
      (positiveRootCovariance_posDef C hC).posSemidef.posSemidef_sqrt.1
  rw [ht]
  exact (positiveRootCovariance_posDef C hC).posSemidef.sqrt_mul_self

theorem positiveRootWhitening_covariance (C : Matrix I I ℝ) (hC : C.PosSemidef) :
    positiveRootWhitening C hC * positiveRootCovariance C * (positiveRootWhitening C hC).transpose = 1 := by
  rw [← positiveRootFactor_gram C hC]
  calc
    _ = (positiveRootWhitening C hC*positiveRootFactor C hC)*
        (positiveRootWhitening C hC*positiveRootFactor C hC).transpose := by
      simp only [Matrix.transpose_mul,Matrix.mul_assoc]
    _ = 1 := by rw [positiveRootWhitening_leftInverse]; simp

theorem positiveRootWhitening_det_ne_zero (C : Matrix I I ℝ) (hC : C.PosSemidef) :
    (positiveRootWhitening C hC).det ≠ 0 := by
  rw [positiveRootWhitening,Matrix.det_nonsing_inv,Ring.inverse_eq_inv]
  exact inv_ne_zero (positiveRootFactor_det_ne_zero C hC)

theorem positiveRootWhitening_identity_secondMoments
    (μ : Measure (I → ℝ)) (hμ : Integrable (squareRadius (I := I)) μ)
    (C : Matrix I I ℝ) (hC : C.PosSemidef) (hMom : HasSecondMoments μ (positiveRootCovariance C)) :
    HasIdentitySecondMoments (Measure.map (positiveRootWhitening C hC).mulVec μ) := by
  apply identitySecondMoments_of_gram_leftInverse μ hμ (positiveRootFactor C hC) _
  · rw [positiveRootFactor_gram]
    exact hMom
  · exact positiveRootWhitening_leftInverse C hC

end GaussianWave.BS
