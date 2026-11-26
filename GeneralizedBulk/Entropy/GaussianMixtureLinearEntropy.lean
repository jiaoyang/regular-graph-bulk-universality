import GeneralizedBulk.Entropy.GaussianMixtureCovarianceEntropy
import GeneralizedBulk.Analysis.LinearDensityEntropy

/-! Exact Jacobians for actual finite Gaussian mixtures under a common
nonsingular linear map, including the normal rescaling used for stars. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace GeneralizedBulk.Entropy
open GeneralizedBulk.Gaussian GeneralizedBulk.Analysis Hermite
variable {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S]

theorem affineGaussian_map_linear (mean : I → ℝ) (A T : Matrix I I ℝ) :
    (affineGaussian mean A).map (fun x => T.mulVec x)=affineGaussian (T.mulVec mean) (T*A) := by
  rw [affineGaussian_map_standardGaussian,Measure.map_map (measurable_finiteMatrixAction T) (by fun_prop),
    affineGaussian_map_standardGaussian]
  congr 1
  funext z
  simp only [Function.comp_def,Matrix.mulVec_add,Matrix.mulVec_mulVec]

theorem gaussianMixtureLaw_map_linear (weight : S → ℝ) (mean : S → I → ℝ)
    (A : S → Matrix I I ℝ) (T : Matrix I I ℝ) :
    (gaussianMixtureLaw weight mean A).map (fun x => T.mulVec x)=
      gaussianMixtureLaw weight (fun s => T.mulVec (mean s)) (fun s => T*A s) := by
  unfold gaussianMixtureLaw
  rw [← Measure.mapₗ_apply_of_measurable (measurable_finiteMatrixAction T),map_sum]
  simp only [map_smul,Measure.map_smul,Measure.mapₗ_apply_of_measurable (measurable_finiteMatrixAction T),affineGaussian_map_linear]

theorem gaussianMixture_linear_entropy_change
    (weight : S → ℝ) (mean : S → I → ℝ) (A : S → Matrix I I ℝ) (T : Matrix I I ℝ)
    (hw : ∀ s,0 ≤ weight s) (hnorm : ∑ s,weight s=1) (hA : ∀ s,(A s).det ≠ 0) (hT : T.det ≠ 0) :
    differentialEntropy (gaussianMixturePDF weight (fun s => T.mulVec (mean s)) (fun s => T*A s)) =
      differentialEntropy (gaussianMixturePDF weight mean A)+Real.log (|T.det|) := by
  let f := gaussianMixturePDF weight mean A
  let g := gaussianMixturePDF weight (fun s => T.mulVec (mean s)) (fun s => T*A s)
  have hf : Measurable f := measurable_gaussianMixturePDF _ _ _
  have hp : ∀ x,0 < f x := gaussianMixturePDF_pos _ _ _ hw hnorm hA
  have hTA (s) : (T*A s).det ≠ 0 := by rw [Matrix.det_mul]; exact mul_ne_zero hT (hA s)
  have hg : Measurable g := measurable_gaussianMixturePDF _ _ _
  have hgp : ∀ x,0 < g x := gaussianMixturePDF_pos _ _ _ hw hnorm hTA
  have hprob : IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (f x))) := by
    rw [← gaussianMixtureLaw_eq_withDensity weight mean A hw hA]
    exact gaussianMixtureLaw_probability weight mean A hw hnorm hA
  have hlaw : volume.withDensity (fun x => ENNReal.ofReal (linearDensity T f x))=
      volume.withDensity (fun x => ENNReal.ofReal (g x)) := by
    rw [← linearDensity_pushforward T hT f hf]
    change (volume.withDensity (fun x => ENNReal.ofReal (gaussianMixturePDF weight mean A x))).map
      (fun x => T.mulVec x) = _
    rw [← gaussianMixtureLaw_eq_withDensity weight mean A hw hA,gaussianMixtureLaw_map_linear,
      gaussianMixtureLaw_eq_withDensity _ _ _ hw hTA]
  have heq := differentialEntropy_eq_of_density_law (linearDensity T f) g
    (measurable_linearDensity T f hf) hg
    (fun x => mul_nonneg (by positivity) (hp _).le) (fun x => (hgp x).le) hlaw
  rw [← heq]
  exact linearDensity_entropy_change T hT f hf hp
    (integrable_gaussianMixturePDF_mul_log weight mean A hw hnorm hA) hprob

theorem gaussianMixture_linear_entropy_fixed_means
    (weight : S → ℝ) (mean : S → I → ℝ) (A : S → Matrix I I ℝ) (T : Matrix I I ℝ)
    (hw : ∀ s,0 ≤ weight s) (hnorm : ∑ s,weight s=1) (hA : ∀ s,(A s).det ≠ 0) (hT : T.det ≠ 0)
    (hfix : ∀ s,T.mulVec (mean s)=mean s) :
    differentialEntropy (gaussianMixturePDF weight mean (fun s => T*A s)) =
      differentialEntropy (gaussianMixturePDF weight mean A)+Real.log (|T.det|) := by
  simpa only [hfix] using gaussianMixture_linear_entropy_change weight mean A T hw hnorm hA hT

end GeneralizedBulk.Entropy
