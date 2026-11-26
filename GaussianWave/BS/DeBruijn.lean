import GaussianWave.BS.HeatBounds
import GaussianWave.BS.HeatIntegrationByParts

/-!
# De Bruijn's identity for arbitrary finite-second-moment input laws

The entropy is the Lebesgue density entropy of the actual independent
Gaussian convolution. Its derivative is proved by differentiation under the
integral using a locally uniform widened-Gaussian envelope. Spatial
integration by parts then identifies that derivative with the actual Fisher
information. There is no entropy-differentiation or de Bruijn premise.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators

namespace GaussianWave.BS
variable {I : Type*} [Fintype I]

theorem hasDerivAt_heatDensity_mul_log
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t) (x : I → ℝ) :
    HasDerivAt (fun u : ℝ => heatDensity μ u x * Real.log (heatDensity μ u x))
      (heatDensityTimeDerivative μ t x * (Real.log (heatDensity μ t x) + 1)) t := by
  have h := hasDerivAt_heatDensity_time μ ht x
  convert h.mul (h.log (heatDensity_pos μ ht x).ne') using 1
  field_simp [(heatDensity_pos μ ht x).ne']
  ring

/-- Actual entropy differentiation at every positive time, before the spatial
integration-by-parts identification. Finite input second moment supplies all
domination conditions internally. -/
theorem hasDerivAt_heatEntropy_integralFormula
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => densityEntropy volume (heatDensity μ u))
      (-(∫ x, heatDensityTimeDerivative μ t x * (Real.log (heatDensity μ t x) + 1))) t := by
  let a := t / 2
  let b := 3 * t / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hT : 0 < 2 * b := by positivity
  have hinterval (u : ℝ) (hu : u ∈ Metric.ball t (t / 2)) : u ∈ Set.Icc a b := by
    rw [Metric.mem_ball, Real.dist_eq] at hu
    obtain ⟨hlo, hhi⟩ := abs_lt.mp hu
    dsimp [a, b]
    constructor <;> linarith
  obtain ⟨L, hL, hlog⟩ := exists_uniform_log_heatDensity_bound μ hμ a b ha
  let C := (Fintype.card I : ℝ) * heatHessianComparison I a b
  have hC : 0 ≤ C := mul_nonneg (Nat.cast_nonneg _) (heatHessianComparison_nonneg ha hb)
  let B : (I → ℝ) → ℝ := fun x =>
    (C * (L + 1)) * (heatDensity μ (2 * b) x + heatDensity μ (2 * b) x * squareRadius x)
  have hB : Integrable B :=
    ((integrable_heatDensity μ hT).add (integrable_heatDensity_mul_squareRadius μ hμ hT)).const_mul _
  have hm (u : ℝ) : AEStronglyMeasurable
      (fun x : I → ℝ => heatDensity μ u x * Real.log (heatDensity μ u x)) :=
    ((measurable_heatDensity μ u).mul (Real.measurable_log.comp
      (measurable_heatDensity μ u))).aestronglyMeasurable
  have hgm : AEStronglyMeasurable (fun x : I → ℝ => heatDensityTimeDerivative μ t x *
      (Real.log (heatDensity μ t x) + 1)) :=
    ((measurable_heatDensityTimeDerivative μ t).mul
      ((Real.measurable_log.comp (measurable_heatDensity μ t)).add_const 1)).aestronglyMeasurable
  have hbound : ∀ x : I → ℝ, ∀ u ∈ Metric.ball t (t / 2),
      ‖heatDensityTimeDerivative μ u x * (Real.log (heatDensity μ u x) + 1)‖ ≤ B x := by
    intro x u hu
    have hui := hinterval u hu
    have hq := squareRadius_nonneg x
    have hf := heatDensity_nonneg μ (2 * b) x
    have hd := norm_heatDensityTimeDerivative_le_comparison μ ha hui x
    have hl : |Real.log (heatDensity μ u x) + 1| ≤ (L + 1) * (1 + squareRadius x) := by
      have hh := hlog u hui x
      calc
        _ ≤ |Real.log (heatDensity μ u x)| + |(1 : ℝ)| := abs_add _ _
        _ ≤ L * (1 + squareRadius x) + 1 := by simpa using add_le_add_right hh 1
        _ ≤ _ := by nlinarith
    rw [norm_mul, Real.norm_eq_abs]
    calc
      _ ≤ (C * heatDensity μ (2 * b) x) * ((L + 1) * (1 + squareRadius x)) :=
        mul_le_mul hd hl (abs_nonneg _) (mul_nonneg hC hf)
      _ = _ := by dsimp [B]; ring
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure (I → ℝ))) (x₀ := t) (ε := t / 2)
    (F := fun u x => heatDensity μ u x * Real.log (heatDensity μ u x))
    (F' := fun u x => heatDensityTimeDerivative μ u x * (Real.log (heatDensity μ u x) + 1))
    (bound := B) (by positivity) (Filter.Eventually.of_forall hm)
    (integrable_heatDensity_log μ hμ ht) hgm (ae_of_all _ hbound) hB
    (ae_of_all _ (fun x u hu => hasDerivAt_heatDensity_mul_log μ
      (lt_of_lt_of_le ha (hinterval u hu).1) x))
  exact hd.2.neg

/-- De Bruijn's identity for the actual Gaussian convolution of an arbitrary
probability law with finite second moment. -/
theorem hasDerivAt_heatEntropy [DecidableEq I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => densityEntropy volume (heatDensity μ u))
      (heatFisherInformation μ t) t := by
  have hformula := hasDerivAt_heatEntropy_integralFormula μ hμ ht
  have hlog : Integrable (fun x => Real.log (heatDensity μ t x) * heatDensityTimeDerivative μ t x) :=
    integrable_log_mul_heatDensityTimeDerivative μ hμ ht
  have hi : Integrable (heatDensityTimeDerivative μ t) := by
    change Integrable (fun x => heatDensityTimeDerivative μ t x)
    simp_rw [heatDensityTimeDerivative_eq_laplacian μ ht]
    exact integrable_finset_sum _ (fun i _ => integrable_heatDensityHessian_diagonal μ ht i)
  have hzero : (∫ x, heatDensityTimeDerivative μ t x) = 0 := by
    simp_rw [heatDensityTimeDerivative_eq_laplacian μ ht]
    rw [integral_finset_sum _ (fun i _ => integrable_heatDensityHessian_diagonal μ ht i)]
    simp_rw [integral_heatDensityHessian_diagonal_eq_zero μ ht]
    simp
  have hparts : (∫ x, Real.log (heatDensity μ t x) * heatDensityTimeDerivative μ t x) =
      -heatFisherInformation μ t := by
    simp_rw [heatDensityTimeDerivative_eq_laplacian μ ht]
    exact integral_log_mul_laplacian_eq_neg_fisher μ ht
      (fun i => integrable_log_mul_heatDensityHessian μ hμ ht i i)
      (fun i => integrable_log_mul_heatDensityGradient μ hμ ht i)
  apply hformula.congr_deriv
  have heq : (fun x : I → ℝ => heatDensityTimeDerivative μ t x *
      (Real.log (heatDensity μ t x) + 1)) =
      (fun x => Real.log (heatDensity μ t x) * heatDensityTimeDerivative μ t x +
        heatDensityTimeDerivative μ t x) := by funext x; ring
  rw [heq, integral_add hlog hi, hparts, hzero]
  ring

end GaussianWave.BS
