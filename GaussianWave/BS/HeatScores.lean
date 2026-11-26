import GaussianWave.BS.HeatRegularity
import GaussianWave.BS.MixtureFisher
import GaussianWave.BS.UpperGeometry

/-!
# Actual directional heat scores as L2 random variables

Every L2 membership assertion is derived from the proved finite Fisher
information of Gaussian smoothing. The law is the actual heated measure.
-/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace GaussianWave.BS
variable {I : Type*} [Fintype I]

def heatDirectionalScore (μ : Measure (I → ℝ)) (t : ℝ) (v x : I → ℝ) : ℝ :=
  (∑ i, heatDensityGradient μ t x i * v i) / heatDensity μ t x

theorem measurable_heatDirectionalScore
    (μ : Measure (I → ℝ)) [SFinite μ] (t : ℝ) (v : I → ℝ) :
    Measurable (heatDirectionalScore μ t v) := by
  apply Measurable.div _ (measurable_heatDensity μ t)
  exact Finset.measurable_sum _ (fun i _ =>
    (measurable_heatDensityGradient μ t i).mul_const (v i))

theorem heatDirectionalScore_sq_density_le
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t)
    (v x : I → ℝ) :
    heatDirectionalScore μ t v x ^ 2 * heatDensity μ t x ≤
      squareRadius v * ∑ i, heatFisherCoordinate μ t i x := by
  have hf := heatDensity_pos μ ht x
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => heatDensityGradient μ t x i) v
  have hbound := div_le_div_of_nonneg_right hcs hf.le
  have hleft : heatDirectionalScore μ t v x ^ 2 * heatDensity μ t x =
      (∑ i, heatDensityGradient μ t x i * v i) ^ 2 / heatDensity μ t x := by
    unfold heatDirectionalScore
    field_simp [hf.ne']
    ring
  rw [hleft]
  convert hbound using 1
  unfold squareRadius heatFisherCoordinate
  rw [← Finset.sum_div]
  ring

theorem integrable_heatDirectionalScore_sq_density
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t) (v : I → ℝ) :
    Integrable (fun x => heatDirectionalScore μ t v x ^ 2 * heatDensity μ t x) := by
  refine ((integrable_finset_sum Finset.univ (fun i _ => integrable_heatFisherCoordinate μ ht i)).const_mul
    (squareRadius v)).mono'
    (((measurable_heatDirectionalScore μ t v).pow_const 2).mul
      (measurable_heatDensity μ t)).aestronglyMeasurable ?_
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (heatDensity_nonneg _ _ _))]
  exact heatDirectionalScore_sq_density_le μ ht v x

theorem memLp_heatDirectionalScore
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t) (v : I → ℝ) :
    MemLp (heatDirectionalScore μ t v) 2 (heatedLaw μ t) := by
  apply (memLp_two_iff_integrable_sq (measurable_heatDirectionalScore μ t v).aestronglyMeasurable).mpr
  rw [heatedLaw_eq_withDensity μ ht]
  apply (integrable_withDensity_iff_integrable_smul'
    (measurable_heatDensity μ t).ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mpr
  simpa only [ENNReal.toReal_ofReal (heatDensity_nonneg _ _ _), smul_eq_mul, mul_comm] using
    integrable_heatDirectionalScore_sq_density μ ht v

def heatDirectionalScoreL2
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t) (v : I → ℝ) :
    Lp ℝ 2 (heatedLaw μ t) :=
  (memLp_heatDirectionalScore μ ht v).toLp (heatDirectionalScore μ t v)

theorem heatDirectionalScoreL2_ae_eq
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t) (v : I → ℝ) :
    (heatDirectionalScoreL2 μ ht v : (I → ℝ) → ℝ) =ᵐ[heatedLaw μ t] heatDirectionalScore μ t v :=
  (memLp_heatDirectionalScore μ ht v).coeFn_toLp

theorem heatDirectionalScoreL2_norm_sq
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t) (v : I → ℝ) :
    ‖heatDirectionalScoreL2 μ ht v‖ ^ 2 =
      ∫ x, heatDirectionalScore μ t v x ^ 2 * heatDensity μ t x := by
  rw [score_norm_sq_eq_integral]
  rw [integral_congr_ae ((heatDirectionalScoreL2_ae_eq μ ht v).mono
    (fun _ h => congrArg (fun z : ℝ => z ^ 2) h))]
  rw [heatedLaw_eq_withDensity μ ht, integral_withDensity_eq_integral_toReal_smul
    (measurable_heatDensity μ t).ennreal_ofReal (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (heatDensity_nonneg _ _ _), smul_eq_mul, mul_comm]

theorem heatDirectionalScore_coordinate [DecidableEq I]
    (μ : Measure (I → ℝ)) (t : ℝ) (i : I) (x : I → ℝ) :
    heatDirectionalScore μ t (Pi.single i 1) x = heatDensityGradient μ t x i / heatDensity μ t x := by
  simp [heatDirectionalScore, Pi.single_apply]

theorem heatDirectionalScore_eq_fderiv
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t) (v x : I → ℝ) :
    heatDirectionalScore μ t v x = fderiv ℝ (heatDensity μ t) x v / heatDensity μ t x := by
  rw [fderiv_heatDensity_apply μ ht]
  rfl

end GaussianWave.BS
