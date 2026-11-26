import GaussianWave.BS.ActualSecondMomentMatrix
import GaussianWave.BS.SecondMomentTransport
import GaussianWave.GaussianProduct

/-! All actual mixed second moments are recovered from a centered Gaussian
characteristic function, including singular covariance matrices. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GaussianWave.BS

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem gaussian_coordinate_integrable_square
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] (C : Matrix I I ℝ)
    (hC : C.PosSemidef) (hG : HasGaussianCovariance μ C) (i : I) :
    Integrable (fun x => x i^2) μ := by
  rw [eq_gaussianCovarianceLaw μ C hC hG]
  exact gaussianCovarianceLaw_coordinate_integrable_pow C hC i 2

theorem gaussian_coordinate_second
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] (C : Matrix I I ℝ)
    (hC : C.PosSemidef) (hG : HasGaussianCovariance μ C) (i : I) :
    (∫ x,x i^2 ∂μ)=C i i := by
  rw [eq_gaussianCovarianceLaw μ C hC hG]
  exact gaussianCovarianceLaw_coordinate_second C hC i

theorem gaussian_hasSecondMoments
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] (C : Matrix I I ℝ)
    (hC : C.PosSemidef) (hG : HasGaussianCovariance μ C) : HasSecondMoments μ C := by
  intro i j
  have hi := gaussian_coordinate_integrable_square μ C hC hG i
  have hj := gaussian_coordinate_integrable_square μ C hC hG j
  have hmi := (memLp_two_iff_integrable_sq (measurable_pi_apply i).aestronglyMeasurable).2 hi
  have hmj := (memLp_two_iff_integrable_sq (measurable_pi_apply j).aestronglyMeasurable).2 hj
  have hij : Integrable (fun x => x i*x j) μ := hmi.integrable_mul hmj
  have hs := centeredGaussian_projection_second_moment μ C
    (finiteCovarianceQuadratic_nonneg_of_posSemidef C hC) hG (Pi.single i 1+Pi.single j 1)
  have hlin (x : I → ℝ) : finiteLinearForm (Pi.single i 1+Pi.single j 1) x=x i+x j := by
    simp [finiteLinearForm,add_mul,Finset.sum_add_distrib,Pi.single_apply,ite_mul]
  simp_rw [hlin] at hs
  have he (x : I → ℝ) : (x i+x j)^2=x i^2+2*(x i*x j)+x j^2 := by ring
  simp_rw [he] at hs
  rw [integral_add (μ := μ) (f := fun x : I → ℝ => x i^2+2*(x i*x j)) (g := fun x => x j^2)
    (hi.add (hij.const_mul 2)) hj,
    integral_add (μ := μ) (f := fun x : I → ℝ => x i^2) (g := fun x => 2*(x i*x j)) hi (hij.const_mul 2),
    integral_const_mul,gaussian_coordinate_second μ C hC hG i,
    gaussian_coordinate_second μ C hC hG j] at hs
  have hquad : finiteCovarianceQuadratic C (Pi.single i 1+Pi.single j 1)=
      C i i+C i j+C j i+C j j := by
    simp [finiteCovarianceQuadratic,Pi.add_apply,add_mul,mul_add,Finset.sum_add_distrib,
      Pi.single_apply,ite_mul,mul_ite]
    <;> ring
  rw [hquad] at hs
  have hsym : C j i=C i j := by
    have hh := congrArg (fun A => A i j) hC.1
    simpa only [Matrix.conjTranspose_apply,star_trivial] using hh
  rw [hsym] at hs
  linarith

theorem gaussian_integrable_squareRadius
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] (C : Matrix I I ℝ)
    (hC : C.PosSemidef) (hG : HasGaussianCovariance μ C) : Integrable (squareRadius (I := I)) μ :=
  integrable_finset_sum _ (fun i _ => gaussian_coordinate_integrable_square μ C hC hG i)

end GaussianWave.BS
