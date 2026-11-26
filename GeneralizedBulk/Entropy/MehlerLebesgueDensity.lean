import GeneralizedBulk.Entropy.NormalizedFiniteSignal
import GeneralizedBulk.Entropy.GaussianMixtureClipping

/-! The actual normalized smoothing law has both its Gaussian-relative
Mehler density and its ordinary Lebesgue Gaussian-mixture density. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace GeneralizedBulk.Entropy.Mehler
open GeneralizedBulk.Gaussian GeneralizedBulk.Analysis Hermite
variable {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S]

def smoothingFactor (I : Type*) [Fintype I] [DecidableEq I] (a : ℝ) : Matrix I I ℝ :=
  Matrix.diagonal (fun _ => Real.sqrt (1-a^2))

theorem smoothingFactor_det_ne_zero (a : ℝ) (ha : 0 < 1-a^2) :
    (smoothingFactor I a).det ≠ 0 := by
  rw [smoothingFactor,Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr (fun i hi => (Real.sqrt_pos.mpr ha).ne')

theorem smoothingFactor_mulVec (a : ℝ) (x : I → ℝ) :
    (smoothingFactor I a).mulVec x = fun i => Real.sqrt (1-a^2)*x i := by
  ext i
  simp [smoothingFactor,Matrix.mulVec_diagonal]

theorem smoothing_affineGaussian (a : ℝ) (ha : 0 < 1-a^2) (y : I → ℝ) :
    affineGaussian (fun i => a*y i) (smoothingFactor I a) =
      Measure.pi (fun i => gaussianReal (a*y i) ⟨1-a^2,ha.le⟩) := by
  rw [affineGaussian_map_standardGaussian]
  simpa only [smoothingFactor_mulVec,Pi.add_apply] using smoothedGaussianLaw_eq_affine_map a ha y

namespace NormalizedFiniteSignal
variable (D : NormalizedFiniteSignal I S)

def lebesgueDensity (a : ℝ) : (I → ℝ) → ℝ :=
  gaussianMixturePDF D.weight (fun s i => a*D.signal s i) (fun _ => smoothingFactor I a)

def smoothingLaw (a : ℝ) : Measure (I → ℝ) :=
  gaussianMixtureLaw D.weight (fun s i => a*D.signal s i) (fun _ => smoothingFactor I a)

theorem smoothingLaw_relative (a : ℝ) (ha : 0 < 1-a^2) :
    D.smoothingLaw a = (standardGaussian I).withDensity (fun x => ENNReal.ofReal (D.density a x)) := by
  unfold smoothingLaw gaussianMixtureLaw
  simp_rw [smoothing_affineGaussian a ha]
  exact finiteMixtureLaw_eq_withDensity D.weight D.signal D.nonneg a ha

theorem smoothingLaw_lebesgue (a : ℝ) (ha : 0 < 1-a^2) :
    D.smoothingLaw a = volume.withDensity (fun x => ENNReal.ofReal (D.lebesgueDensity a x)) :=
  gaussianMixtureLaw_eq_withDensity _ _ _ D.nonneg (fun _ => smoothingFactor_det_ne_zero a ha)

theorem lebesgueDensity_pos (a : ℝ) (ha : 0 < 1-a^2) (x : I → ℝ) :
    0 < D.lebesgueDensity a x :=
  gaussianMixturePDF_pos _ _ _ D.nonneg D.total (fun _ => smoothingFactor_det_ne_zero a ha) x

theorem measurable_lebesgueDensity (a : ℝ) : Measurable (D.lebesgueDensity a) :=
  measurable_gaussianMixturePDF _ _ _

theorem lebesgueDensity_eq_relative_ae (a : ℝ) (ha : 0 < 1-a^2) :
    D.lebesgueDensity a =ᵐ[volume] fun x => standardGaussianPDF x*D.density a x := by
  have hm := D.smoothingLaw_relative a ha
  rw [D.smoothingLaw_lebesgue a ha,standardGaussian_eq_volume_withDensity] at hm
  have he : (fun x => ENNReal.ofReal (standardGaussianPDF x*D.density a x)) =
      (fun x => ENNReal.ofReal (standardGaussianPDF x)*ENNReal.ofReal (D.density a x)) := by
    funext x
    exact ENNReal.ofReal_mul (standardGaussianPDF_pos x).le
  rw [← withDensity_mul _ measurable_standardGaussianPDF.ennreal_ofReal
    (D.density_continuous a).measurable.ennreal_ofReal] at hm
  change (volume.withDensity (fun x => ENNReal.ofReal (D.lebesgueDensity a x))) =
    volume.withDensity (fun x => ENNReal.ofReal (standardGaussianPDF x)*ENNReal.ofReal (D.density a x)) at hm
  rw [← he] at hm
  have hh := (withDensity_eq_iff_of_sigmaFinite
    (D.measurable_lebesgueDensity a).ennreal_ofReal.aemeasurable
    (measurable_standardGaussianPDF.mul (D.density_continuous a).measurable).ennreal_ofReal.aemeasurable).mp hm
  filter_upwards [hh] with x hx
  exact (ENNReal.ofReal_eq_ofReal_iff (D.lebesgueDensity_pos a ha x).le
    (mul_nonneg (standardGaussianPDF_pos x).le (D.density_nonneg a x))).mp hx

end NormalizedFiniteSignal
end GeneralizedBulk.Entropy.Mehler
