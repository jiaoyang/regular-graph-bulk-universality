import GaussianWave.BS.HeatDerivatives
import GaussianWave.BS.MixtureFisher
import GaussianWave.BS.EntropyEndpoint

/-!
# Integrable widened-Gaussian bounds for heat derivatives

On a compact positive-time interval, the kernel and each derivative of order
at most two are bounded by a constant times one wider Gaussian kernel. Their
convolutions therefore have integrable quadratic weights for every input
probability measure of finite second moment.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators ENNReal NNReal

namespace GaussianWave.BS
variable {I : Type*} [Fintype I]

theorem heatKernelBound_pos {t : ℝ} (ht : 0 < t) : 0 < heatKernelBound I t := by
  apply Finset.prod_pos
  intro i _
  have := heatVariance_pos ht
  positivity

def heatComparisonFactor (I : Type*) [Fintype I] (a b : ℝ) : ℝ :=
  heatKernelBound I a / heatKernelBound I (2 * b)

theorem heatComparisonFactor_nonneg (I : Type*) [Fintype I] (a b : ℝ) :
    0 ≤ heatComparisonFactor I a b :=
  div_nonneg (heatKernelBound_nonneg _ _) (heatKernelBound_nonneg _ _)

private theorem comparisonFactor_mul_kernel {a b : ℝ} (hb : 0 < b) (x : I → ℝ) :
    heatComparisonFactor I a b * heatKernel (2 * b) x =
      heatKernelBound I a * Real.exp (-squareMass x / (8 * b)) := by
  rw [heatKernel_factor (by positivity : 0 < 2 * b)]
  unfold heatComparisonFactor
  have hn : heatKernelBound I (2 * b) ≠ 0 := (heatKernelBound_pos (by positivity)).ne'
  rw [div_mul_eq_mul_div, mul_div_assoc, mul_div_cancel_left₀ _ hn]
  congr 2
  ring

private theorem heatKernel_le_coarse {a b u : ℝ} (ha : 0 < a) (hu : u ∈ Set.Icc a b)
    (x : I → ℝ) :
    heatKernel u x ≤ heatKernelBound I a * Real.exp (-squareMass x / (4 * b)) := by
  have hupos : 0 < u := lt_of_lt_of_le ha hu.1
  rw [heatKernel_factor hupos]
  apply mul_le_mul
  · exact heatKernelBound_antitoneOn I ha hupos hu.1
  · apply Real.exp_le_exp.mpr
    have hdiv : squareMass x / (4 * b) ≤ squareMass x / (4 * u) :=
      div_le_div_of_nonneg_left (squareMass_nonneg x)
        (by positivity : 0 < 4 * u) (by linarith [hu.2])
    simpa only [neg_div] using neg_le_neg hdiv
  · exact (Real.exp_pos _).le
  · exact heatKernelBound_nonneg _ _

theorem heatKernel_le_comparison {a b u : ℝ} (ha : 0 < a) (hu : u ∈ Set.Icc a b)
    (x : I → ℝ) :
    heatKernel u x ≤ heatComparisonFactor I a b * heatKernel (2 * b) x := by
  have hb : 0 < b := lt_of_lt_of_le ha (hu.1.trans hu.2)
  rw [comparisonFactor_mul_kernel hb]
  refine (heatKernel_le_coarse ha hu x).trans ?_
  apply mul_le_mul_of_nonneg_left _ (heatKernelBound_nonneg _ _)
  apply Real.exp_le_exp.mpr
  have hq := squareMass_nonneg x
  have hd : 0 < 8 * b := by positivity
  have hqdiv : 0 ≤ squareMass x / (8 * b) := by positivity
  have he : squareMass x / (4 * b) = 2 * (squareMass x / (8 * b)) := by ring
  rw [neg_div, neg_div, he]
  linarith

theorem squareMass_mul_heatKernel_le_comparison {a b u : ℝ}
    (ha : 0 < a) (hu : u ∈ Set.Icc a b) (x : I → ℝ) :
    squareMass x * heatKernel u x ≤
      (8 * b * heatComparisonFactor I a b) * heatKernel (2 * b) x := by
  have hb : 0 < b := lt_of_lt_of_le ha (hu.1.trans hu.2)
  have h := squareMass_mul_heatKernel_le (by positivity : 0 < 2 * b) x
  have hpoly : squareMass x * Real.exp (-squareMass x / (8 * b)) ≤ 8 * b := by
    rw [heatKernel_factor (by positivity : 0 < 2 * b)] at h
    have hB := heatKernelBound_pos (I := I) (by positivity : 0 < 2 * b)
    have he : -(squareMass x) / (4 * (2 * b)) = -squareMass x / (8 * b) := by ring
    rw [he] at h
    nlinarith
  have hexp : Real.exp (-squareMass x / (4 * b)) =
      Real.exp (-squareMass x / (8 * b)) * Real.exp (-squareMass x / (8 * b)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ squareMass x * (heatKernelBound I a * Real.exp (-squareMass x / (4 * b))) :=
      mul_le_mul_of_nonneg_left (heatKernel_le_coarse ha hu x) (squareMass_nonneg x)
    _ = (squareMass x * Real.exp (-squareMass x / (8 * b))) *
        (heatKernelBound I a * Real.exp (-squareMass x / (8 * b))) := by rw [hexp]; ring
    _ ≤ (8 * b) * (heatKernelBound I a * Real.exp (-squareMass x / (8 * b))) :=
      mul_le_mul_of_nonneg_right hpoly (by have := heatKernelBound_nonneg I a; positivity)
    _ = _ := by rw [← comparisonFactor_mul_kernel hb]; ring

def heatGradientComparison (I : Type*) [Fintype I] (a b : ℝ) : ℝ :=
  ((1 + 8 * b) * heatComparisonFactor I a b) / (2 * a)

def heatHessianComparison (I : Type*) [Fintype I] (a b : ℝ) : ℝ :=
  (8 * b * heatComparisonFactor I a b) / (4 * a ^ 2) +
    heatComparisonFactor I a b / (2 * a)

theorem norm_heatKernelGradient_le_comparison {a b u : ℝ}
    (ha : 0 < a) (hu : u ∈ Set.Icc a b) (x : I → ℝ) (i : I) :
    ‖heatKernelGradient u x i‖ ≤ heatGradientComparison I a b * heatKernel (2 * b) x := by
  have hupos : 0 < u := lt_of_lt_of_le ha hu.1
  have habs : |x i| ≤ 1 + squareMass x := by
    have := sq_coordinate_le_squareMass x i
    nlinarith [sq_nonneg (|x i| - 1), sq_abs (x i)]
  have hq := squareMass_nonneg x
  unfold heatKernelGradient heatGradientComparison
  rw [Real.norm_eq_abs, abs_mul, abs_div, abs_neg, abs_of_pos (by positivity : 0 < 2 * u),
    abs_of_nonneg (heatKernel_nonneg _ _), div_mul_eq_mul_div]
  calc
    _ ≤ ((1 + squareMass x) * heatKernel u x) / (2 * a) :=
      div_le_div₀ (mul_nonneg (by positivity) (heatKernel_nonneg _ _))
        (mul_le_mul_of_nonneg_right habs (heatKernel_nonneg _ _))
        (by positivity) (by linarith [hu.1])
    _ = (heatKernel u x + squareMass x * heatKernel u x) / (2 * a) := by ring
    _ ≤ ((heatComparisonFactor I a b + 8 * b * heatComparisonFactor I a b) *
        heatKernel (2 * b) x) / (2 * a) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [heatKernel_le_comparison ha hu x, squareMass_mul_heatKernel_le_comparison ha hu x]
    _ = _ := by ring

theorem norm_heatKernelHessian_le_comparison [DecidableEq I] {a b u : ℝ}
    (ha : 0 < a) (hu : u ∈ Set.Icc a b) (x : I → ℝ) (i j : I) :
    ‖heatKernelHessian u x i j‖ ≤ heatHessianComparison I a b * heatKernel (2 * b) x := by
  have hupos : 0 < u := lt_of_lt_of_le ha hu.1
  have hf : |x i * x j / (4 * u ^ 2) - if i = j then 1 / (2 * u) else 0| ≤
      squareMass x / (4 * u ^ 2) + 1 / (2 * u) := by
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rw [abs_div, abs_of_pos (by positivity : 0 < 4 * u ^ 2)]
      exact div_le_div_of_nonneg_right (abs_coordinate_product_le_squareMass x i j) (by positivity)
    · by_cases hij : i = j
      · rw [if_pos hij, abs_of_pos (by positivity : 0 < 1 / (2 * u))]
      · rw [if_neg hij, abs_zero]; positivity
  unfold heatKernelHessian heatHessianComparison
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel_nonneg _ _)]
  calc
    _ ≤ (squareMass x / (4 * u ^ 2) + 1 / (2 * u)) * heatKernel u x :=
      mul_le_mul_of_nonneg_right hf (heatKernel_nonneg _ _)
    _ = squareMass x * heatKernel u x / (4 * u ^ 2) + heatKernel u x / (2 * u) := by ring
    _ ≤ ((8 * b * heatComparisonFactor I a b) * heatKernel (2 * b) x) / (4 * a ^ 2) +
        (heatComparisonFactor I a b * heatKernel (2 * b) x) / (2 * a) := by
      apply add_le_add
      · apply div_le_div₀ (by
            have hb : 0 < b := by linarith [hu.1, hu.2]
            exact mul_nonneg (mul_nonneg (by positivity) (heatComparisonFactor_nonneg I a b))
              (heatKernel_nonneg _ _))
          (squareMass_mul_heatKernel_le_comparison ha hu x) (by positivity)
        nlinarith [hu.1]
      · exact div_le_div₀ (mul_nonneg (heatComparisonFactor_nonneg _ _ _) (heatKernel_nonneg _ _))
          (heatKernel_le_comparison ha hu x) (by positivity) (by linarith [hu.1])
    _ = _ := by ring

theorem norm_heatKernelTimeDerivative_le_comparison {a b u : ℝ}
    (ha : 0 < a) (hu : u ∈ Set.Icc a b) (x : I → ℝ) :
    ‖heatKernelTimeDerivative u x‖ ≤
      ((Fintype.card I : ℝ) * heatHessianComparison I a b) * heatKernel (2 * b) x := by
  classical
  rw [heatKernelTimeDerivative_eq_laplacian]
  calc
    _ ≤ ∑ i, ‖heatKernelHessian u x i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : I, heatHessianComparison I a b * heatKernel (2 * b) x :=
      Finset.sum_le_sum (fun i _ => norm_heatKernelHessian_le_comparison ha hu x i i)
    _ = _ := by simp; ring

theorem norm_heatDensityGradient_le_comparison
    (μ : Measure (I → ℝ)) [IsFiniteMeasure μ] {a b u : ℝ}
    (ha : 0 < a) (hu : u ∈ Set.Icc a b) (x : I → ℝ) (i : I) :
    ‖heatDensityGradient μ u x i‖ ≤ heatGradientComparison I a b * heatDensity μ (2 * b) x := by
  unfold heatDensityGradient
  calc
    _ ≤ ∫ y, ‖heatKernelGradient u (x - y) i‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, heatGradientComparison I a b * heatKernel (2 * b) (x - y) ∂μ :=
      integral_mono (integrable_heatKernelGradient_shift μ (lt_of_lt_of_le ha hu.1) x i).norm
        ((integrable_heatKernel_shift μ (2 * b) x).const_mul _)
        (fun y => norm_heatKernelGradient_le_comparison ha hu (x - y) i)
    _ = _ := integral_const_mul _ _

theorem norm_heatDensityHessian_le_comparison [DecidableEq I]
    (μ : Measure (I → ℝ)) [IsFiniteMeasure μ] {a b u : ℝ}
    (ha : 0 < a) (hu : u ∈ Set.Icc a b) (x : I → ℝ) (i j : I) :
    ‖heatDensityHessian μ u x i j‖ ≤ heatHessianComparison I a b * heatDensity μ (2 * b) x := by
  unfold heatDensityHessian
  calc
    _ ≤ ∫ y, ‖heatKernelHessian u (x - y) i j‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, heatHessianComparison I a b * heatKernel (2 * b) (x - y) ∂μ :=
      integral_mono (integrable_heatKernelHessian_shift μ (lt_of_lt_of_le ha hu.1) x i j).norm
        ((integrable_heatKernel_shift μ (2 * b) x).const_mul _)
        (fun y => norm_heatKernelHessian_le_comparison ha hu (x - y) i j)
    _ = _ := integral_const_mul _ _

theorem norm_heatDensityTimeDerivative_le_comparison
    (μ : Measure (I → ℝ)) [IsFiniteMeasure μ] {a b u : ℝ}
    (ha : 0 < a) (hu : u ∈ Set.Icc a b) (x : I → ℝ) :
    ‖heatDensityTimeDerivative μ u x‖ ≤
      ((Fintype.card I : ℝ) * heatHessianComparison I a b) * heatDensity μ (2 * b) x := by
  unfold heatDensityTimeDerivative
  calc
    _ ≤ ∫ y, ‖heatKernelTimeDerivative u (x - y)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, ((Fintype.card I : ℝ) * heatHessianComparison I a b) *
        heatKernel (2 * b) (x - y) ∂μ :=
      integral_mono (integrable_heatKernelTimeDerivative_shift μ (lt_of_lt_of_le ha hu.1) x).norm
        ((integrable_heatKernel_shift μ (2 * b) x).const_mul _)
        (fun y => norm_heatKernelTimeDerivative_le_comparison ha hu (x - y))
    _ = _ := integral_const_mul _ _

theorem measurable_heatDensityHessian [DecidableEq I]
    (μ : Measure (I → ℝ)) [SFinite μ] (t : ℝ) (i j : I) :
    Measurable (fun x => heatDensityHessian μ t x i j) := by
  have hm : StronglyMeasurable (fun z : (I → ℝ) × (I → ℝ) =>
      heatKernelHessian t (z.1 - z.2) i j) :=
    ((continuous_heatKernelHessian t i j).comp
      (continuous_fst.sub continuous_snd)).stronglyMeasurable
  exact hm.integral_prod_right'.measurable

theorem measurable_heatDensityTimeDerivative
    (μ : Measure (I → ℝ)) [SFinite μ] (t : ℝ) :
    Measurable (heatDensityTimeDerivative μ t) := by
  have hm : StronglyMeasurable (fun z : (I → ℝ) × (I → ℝ) =>
      heatKernelTimeDerivative t (z.1 - z.2)) :=
    ((continuous_heatKernelTimeDerivative t).comp
      (continuous_fst.sub continuous_snd)).stronglyMeasurable
  exact hm.integral_prod_right'.measurable

theorem heatGradientComparison_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 ≤ heatGradientComparison I a b := by
  unfold heatGradientComparison
  exact div_nonneg (mul_nonneg (by positivity) (heatComparisonFactor_nonneg _ _ _)) (by positivity)

theorem heatHessianComparison_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 ≤ heatHessianComparison I a b := by
  unfold heatHessianComparison
  have := heatComparisonFactor_nonneg I a b
  positivity

/-- A widened-density bound supplies the logarithm-weighted integrability
needed in spatial integration by parts. Both bounds are obtained from the
actual heat density, with finite input second moment as the only moment
assumption. -/
theorem integrable_log_heatDensity_mul_of_bound
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ)
    {t T : ℝ} (ht : 0 < t) (hT : 0 < T)
    (A : (I → ℝ) → ℝ) (hA : Measurable A)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x, ‖A x‖ ≤ C * heatDensity μ T x) :
    Integrable (fun x => Real.log (heatDensity μ t x) * A x) := by
  obtain ⟨L, hL, hlog⟩ := exists_uniform_log_heatDensity_bound μ hμ t t ht
  apply (((integrable_heatDensity μ hT).add
    (integrable_heatDensity_mul_squareRadius μ hμ hT)).const_mul (C * L)).mono'
    (((Real.measurable_log.comp (measurable_heatDensity μ t)).mul hA).aestronglyMeasurable)
  filter_upwards [] with x
  have hq := squareRadius_nonneg x
  have hf := heatDensity_nonneg μ T x
  have hh := hlog t ⟨le_rfl, le_rfl⟩ x
  change |Real.log (heatDensity μ t x) * A x| ≤
    (C * L) * (heatDensity μ T x + heatDensity μ T x * squareRadius x)
  rw [abs_mul]
  calc
    _ ≤ (L * (1 + squareRadius x)) * (C * heatDensity μ T x) :=
      mul_le_mul hh (hbound x) (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem integrable_log_mul_heatDensityGradient
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) {t : ℝ} (ht : 0 < t) (i : I) :
    Integrable (fun x => Real.log (heatDensity μ t x) * heatDensityGradient μ t x i) := by
  exact integrable_log_heatDensity_mul_of_bound μ hμ ht (by positivity : 0 < 2 * t)
    (fun x => heatDensityGradient μ t x i) (measurable_heatDensityGradient μ t i)
    (heatGradientComparison I t t) (heatGradientComparison_nonneg ht ht)
    (fun x => norm_heatDensityGradient_le_comparison μ ht ⟨le_rfl, le_rfl⟩ x i)

theorem integrable_log_mul_heatDensityHessian [DecidableEq I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) {t : ℝ} (ht : 0 < t) (i j : I) :
    Integrable (fun x => Real.log (heatDensity μ t x) * heatDensityHessian μ t x i j) := by
  exact integrable_log_heatDensity_mul_of_bound μ hμ ht (by positivity : 0 < 2 * t)
    (fun x => heatDensityHessian μ t x i j) (measurable_heatDensityHessian μ t i j)
    (heatHessianComparison I t t) (heatHessianComparison_nonneg ht ht)
    (fun x => norm_heatDensityHessian_le_comparison μ ht ⟨le_rfl, le_rfl⟩ x i j)

theorem integrable_log_mul_heatDensityTimeDerivative
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x => Real.log (heatDensity μ t x) * heatDensityTimeDerivative μ t x) := by
  exact integrable_log_heatDensity_mul_of_bound μ hμ ht (by positivity : 0 < 2 * t)
    (heatDensityTimeDerivative μ t) (measurable_heatDensityTimeDerivative μ t)
    ((Fintype.card I : ℝ) * heatHessianComparison I t t)
    (mul_nonneg (Nat.cast_nonneg _) (heatHessianComparison_nonneg ht ht))
    (fun x => norm_heatDensityTimeDerivative_le_comparison μ ht ⟨le_rfl, le_rfl⟩ x)

end GaussianWave.BS
