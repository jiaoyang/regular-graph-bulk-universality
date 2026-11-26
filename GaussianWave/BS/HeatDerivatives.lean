import GaussianWave.BS.HeatFlow
import GaussianWave.BS.GaussianReference
import GaussianWave.MomentTail
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Derivatives of the actual arbitrary-measure heat density

This layer starts from `heatDensity`, the density of the actual convolution
constructed in `HeatFlow`. In particular, differentiability is not encoded
as an input structure. No moment assumption is required for its spatial
derivatives: polynomial times Gaussian kernels are uniformly bounded.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators ENNReal NNReal

namespace GaussianWave.BS

variable {I : Type*} [Fintype I]

theorem coe_heatVariance {t : ℝ} (ht : 0 ≤ t) : (heatVariance t : ℝ) = 2 * t := by
  change max (2 * t) 0 = 2 * t
  exact max_eq_left (by positivity)

theorem heatKernel_factor {t : ℝ} (ht : 0 < t) (x : I → ℝ) :
    heatKernel t x = heatKernelBound I t * Real.exp (-squareMass x / (4 * t)) := by
  unfold heatKernel heatKernelBound gaussianPDFReal
  simp only [sub_zero, coe_heatVariance ht.le]
  rw [Finset.prod_mul_distrib, ← Real.exp_sum]
  congr 2
  simp only [squareMass, ← Finset.sum_neg_distrib, ← Finset.sum_div]
  congr 1
  ring

/-- The actual first kernel derivative in the coordinate `i`. -/
def heatKernelGradient (t : ℝ) (x : I → ℝ) (i : I) : ℝ :=
  -(x i) / (2 * t) * heatKernel t x

/-- The actual second kernel derivative in coordinates `i,j`. -/
def heatKernelHessian [DecidableEq I] (t : ℝ) (x : I → ℝ) (i j : I) : ℝ :=
  (x i * x j / (4 * t ^ 2) - if i = j then 1 / (2 * t) else 0) * heatKernel t x

/-- The actual heat-time derivative of the kernel. -/
def heatKernelTimeDerivative (t : ℝ) (x : I → ℝ) : ℝ :=
  (squareMass x / (4 * t ^ 2) - (Fintype.card I : ℝ) / (2 * t)) * heatKernel t x

theorem hasDerivAt_squareMass_line (x v : I → ℝ) (s : ℝ) :
    HasDerivAt (fun u : ℝ => squareMass (x + u • v))
      (∑ i, 2 * (x i + s * v i) * v i) s := by
  unfold squareMass
  apply HasDerivAt.sum
  intro i _
  convert (((hasDerivAt_const s (x i)).add
    ((hasDerivAt_id s).mul_const (v i))).pow 2) using 1 <;> simp

theorem hasDerivAt_heatKernel_line {t : ℝ} (ht : 0 < t)
    (x v : I → ℝ) (s : ℝ) :
    HasDerivAt (fun u : ℝ => heatKernel t (x + u • v))
      ((∑ i, -(x i + s * v i) / (2 * t) * v i) *
        heatKernel t (x + s • v)) s := by
  simp_rw [heatKernel_factor ht]
  convert ((((hasDerivAt_squareMass_line x v s).neg.div_const (4 * t)).exp).const_mul
    (heatKernelBound I t)) using 1
  have hs : (∑ i, -(x i + s * v i) / (2 * t) * v i) =
      (-(∑ i, 2 * (x i + s * v i) * v i)) / (4 * t) := by
    rw [← Finset.sum_neg_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    field_simp
    ring
  rw [hs]
  ring

theorem continuous_heatKernelGradient (t : ℝ) (i : I) :
    Continuous (fun x : I → ℝ => heatKernelGradient t x i) := by
  unfold heatKernelGradient
  exact (((continuous_apply i).neg.div_const _).mul (continuous_heatKernel t))

theorem sq_coordinate_le_squareMass (x : I → ℝ) (i : I) :
    (x i) ^ 2 ≤ squareMass x :=
  Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)

private theorem mul_exp_neg_le_one (u : ℝ) :
    u * Real.exp (-u) ≤ 1 := by
  have h := Real.add_one_le_exp u
  have he := Real.exp_pos (-u)
  have hm : u * Real.exp (-u) ≤ Real.exp u * Real.exp (-u) :=
    mul_le_mul_of_nonneg_right (by linarith) he.le
  simpa only [← Real.exp_add, add_neg_cancel, Real.exp_zero] using hm

theorem squareMass_mul_heatKernel_le {t : ℝ} (ht : 0 < t) (x : I → ℝ) :
    squareMass x * heatKernel t x ≤ 4 * t * heatKernelBound I t := by
  have h := mul_exp_neg_le_one (squareMass x / (4 * t))
  have hB : 0 ≤ heatKernelBound I t :=
    Finset.prod_nonneg (fun _ _ => by positivity)
  rw [heatKernel_factor ht]
  have hq : squareMass x * Real.exp (-squareMass x / (4 * t)) ≤ 4 * t := by
    rw [div_mul_eq_mul_div] at h
    simpa only [neg_div, one_mul] using
      (div_le_iff₀ (by positivity : 0 < 4 * t)).mp h
  nlinarith [mul_le_mul_of_nonneg_left hq hB]

theorem abs_coordinate_mul_heatKernel_le {t : ℝ} (ht : 0 < t)
    (x : I → ℝ) (i : I) :
    |x i| * heatKernel t x ≤ (1 + 4 * t) * heatKernelBound I t := by
  have hq := sq_coordinate_le_squareMass x i
  have habs : |x i| ≤ 1 + squareMass x := by
    have hs : |x i| ^ 2 = (x i) ^ 2 := sq_abs _
    nlinarith [sq_nonneg (|x i| - 1)]
  calc
    _ ≤ (1 + squareMass x) * heatKernel t x :=
      mul_le_mul_of_nonneg_right habs (heatKernel_nonneg _ _)
    _ = heatKernel t x + squareMass x * heatKernel t x := by ring
    _ ≤ heatKernelBound I t + 4 * t * heatKernelBound I t :=
      add_le_add (heatKernel_le_bound _ _) (squareMass_mul_heatKernel_le ht x)
    _ = _ := by ring

/-- A uniform bound, independent of the input point and the mixing measure. -/
def heatGradientBound (I : Type*) [Fintype I] (t : ℝ) : ℝ :=
  (1 + 4 * t) * heatKernelBound I t / (2 * t)

theorem norm_heatKernelGradient_le {t : ℝ} (ht : 0 < t) (x : I → ℝ) (i : I) :
    ‖heatKernelGradient t x i‖ ≤ heatGradientBound I t := by
  unfold heatKernelGradient heatGradientBound
  rw [Real.norm_eq_abs, abs_mul, abs_div, abs_neg, abs_of_pos (by positivity : 0 < 2 * t),
    abs_of_nonneg (heatKernel_nonneg _ _), div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right (abs_coordinate_mul_heatKernel_le ht x i) (by positivity)

theorem hasDerivAt_heatKernel_line_gradient {t : ℝ} (ht : 0 < t)
    (x v : I → ℝ) (s : ℝ) :
    HasDerivAt (fun u : ℝ => heatKernel t (x + u • v))
      (∑ i, heatKernelGradient t (x + s • v) i * v i) s := by
  convert hasDerivAt_heatKernel_line ht x v s using 1
  simp only [heatKernelGradient, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem norm_heatKernel_line_gradient_le {t : ℝ} (ht : 0 < t)
    (x v : I → ℝ) :
    ‖∑ i, heatKernelGradient t x i * v i‖ ≤
      ∑ i, heatGradientBound I t * ‖v i‖ := by
  calc
    _ ≤ ∑ i, ‖heatKernelGradient t x i * v i‖ := norm_sum_le _ _
    _ = ∑ i, ‖heatKernelGradient t x i‖ * ‖v i‖ := by simp_rw [norm_mul]
    _ ≤ _ := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (norm_heatKernelGradient_le ht x i) (norm_nonneg _)

/-- The actual spatial derivative, as an absolutely convergent mixture. -/
def heatDensityGradient (μ : Measure (I → ℝ)) (t : ℝ) (x : I → ℝ) (i : I) : ℝ :=
  ∫ y, heatKernelGradient t (x - y) i ∂μ

theorem integrable_heatKernelGradient_shift
    (μ : Measure (I → ℝ)) [IsFiniteMeasure μ] {t : ℝ} (ht : 0 < t)
    (x : I → ℝ) (i : I) :
    Integrable (fun y => heatKernelGradient t (x - y) i) μ := by
  apply (integrable_const (heatGradientBound I t)).mono'
    (((continuous_heatKernelGradient t i).comp
      (continuous_const.sub continuous_id)).measurable.aestronglyMeasurable)
  exact ae_of_all _ (fun y => norm_heatKernelGradient_le ht (x - y) i)

/-- Differentiation of the actual arbitrary-measure convolution under the
integral, along every spatial line. The domination is a constant Gaussian
derivative bound, so no moment hypothesis on the finite input is needed. -/
theorem hasDerivAt_heatDensity_line
    (μ : Measure (I → ℝ)) [IsFiniteMeasure μ] {t : ℝ} (ht : 0 < t)
    (x v : I → ℝ) (s : ℝ) :
    HasDerivAt (fun u : ℝ => heatDensity μ t (x + u • v))
      (∑ i, heatDensityGradient μ t (x + s • v) i * v i) s := by
  have hm (u : ℝ) : AEStronglyMeasurable
      (fun y : I → ℝ => heatKernel t (x + u • v - y)) μ :=
    ((continuous_heatKernel t).comp (continuous_const.sub continuous_id)).measurable.aestronglyMeasurable
  have hgm (u : ℝ) : AEStronglyMeasurable
      (fun y : I → ℝ => ∑ i, heatKernelGradient t (x + u • v - y) i * v i) μ := by
    apply (continuous_finset_sum _ (fun i _ =>
      ((continuous_heatKernelGradient t i).comp
        (continuous_const.sub continuous_id)).mul continuous_const)).measurable.aestronglyMeasurable
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (x₀ := s) (ε := 1)
    (F := fun u y => heatKernel t (x + u • v - y))
    (F' := fun u y => ∑ i, heatKernelGradient t (x + u • v - y) i * v i)
    (bound := fun _ => ∑ i, heatGradientBound I t * ‖v i‖)
    zero_lt_one (Filter.Eventually.of_forall hm)
    (integrable_heatKernel_shift μ t (x + s • v)) (hgm s)
    (ae_of_all _ (fun y u _ => norm_heatKernel_line_gradient_le ht _ v))
    (integrable_const _) (ae_of_all _ (fun y u _ => by
      simpa only [sub_add_eq_add_sub] using
        hasDerivAt_heatKernel_line_gradient ht (x - y) v u))
  convert hd.2 using 1
  rw [integral_finset_sum _ (fun i _ =>
    (integrable_heatKernelGradient_shift μ ht (x + s • v) i).mul_const (v i))]
  apply Finset.sum_congr rfl
  intro i _
  simp only [heatDensityGradient, integral_mul_const]

theorem hasDerivAt_heatKernel_coordinate [DecidableEq I] {t : ℝ} (ht : 0 < t)
    (x : I → ℝ) (i : I) (s : ℝ) :
    HasDerivAt (fun u : ℝ => heatKernel t (x + u • (Pi.single i 1 : I → ℝ)))
      (heatKernelGradient t (x + s • (Pi.single i 1 : I → ℝ)) i) s := by
  simpa [Pi.single_apply] using
    hasDerivAt_heatKernel_line_gradient ht x (Pi.single i 1) s

theorem hasDerivAt_heatDensity_coordinate [DecidableEq I]
    (μ : Measure (I → ℝ)) [IsFiniteMeasure μ] {t : ℝ} (ht : 0 < t)
    (x : I → ℝ) (i : I) (s : ℝ) :
    HasDerivAt (fun u : ℝ => heatDensity μ t (x + u • (Pi.single i 1 : I → ℝ)))
      (heatDensityGradient μ t (x + s • (Pi.single i 1 : I → ℝ)) i) s := by
  simpa [Pi.single_apply] using hasDerivAt_heatDensity_line μ ht x (Pi.single i 1) s

theorem heatKernel_eq_exp_logFormula {t : ℝ} (ht : 0 < t) (x : I → ℝ) :
    heatKernel t x = Real.exp
      (-((Fintype.card I : ℝ) / 2) * Real.log (4 * Real.pi * t) -
        squareMass x / (4 * t)) := by
  calc
    _ = Real.exp (Real.log (heatKernel t x)) := (Real.exp_log (heatKernel_pos ht x)).symm
    _ = _ := by
      rw [log_heatKernel ht x, coe_heatVariance ht.le]
      congr 2
      · ring
      · simp only [squareRadius, squareMass]
        ring

theorem hasDerivAt_heatKernel_time {t : ℝ} (ht : 0 < t) (x : I → ℝ) :
    HasDerivAt (fun u : ℝ => heatKernel u x) (heatKernelTimeDerivative t x) t := by
  let m : ℝ := Fintype.card I
  have hl : HasDerivAt (fun u : ℝ =>
      -(m / 2) * Real.log (4 * Real.pi * u) - squareMass x / (4 * u))
      (-(m / 2) * (4 * Real.pi / (4 * Real.pi * t)) -
        (-(squareMass x * 4) / (4 * t) ^ 2)) t := by
    simpa only [id_eq, mul_one, zero_mul, zero_sub] using
      ((((hasDerivAt_id t).const_mul (4 * Real.pi)).log (by positivity)).const_mul
      (-(m / 2))).sub ((hasDerivAt_const t (squareMass x)).div
        ((hasDerivAt_id t).const_mul 4) (by positivity))
  have he := hl.exp
  have heq : (fun u : ℝ => heatKernel u x) =ᶠ[𝓝 t]
      (fun u : ℝ => Real.exp (-(m / 2) * Real.log (4 * Real.pi * u) -
        squareMass x / (4 * u))) := by
    filter_upwards [eventually_gt_nhds ht] with u hu
    exact heatKernel_eq_exp_logFormula hu x
  convert he.congr_of_eventuallyEq heq using 1
  rw [← heatKernel_eq_exp_logFormula ht x]
  unfold heatKernelTimeDerivative
  dsimp [m]
  field_simp [ht.ne', Real.pi_ne_zero]
  ring

theorem heatKernelBound_nonneg (I : Type*) [Fintype I] (t : ℝ) :
    0 ≤ heatKernelBound I t := Finset.prod_nonneg fun _ _ => by positivity

theorem heatKernelBound_antitoneOn (I : Type*) [Fintype I] :
    AntitoneOn (heatKernelBound I) (Set.Ioi 0) := by
  intro a ha b hb hab
  apply Finset.prod_le_prod (fun _ _ => by positivity)
  intro i _
  apply (inv_le_inv₀
    (Real.sqrt_pos.mpr (by have := heatVariance_pos hb; positivity))
    (Real.sqrt_pos.mpr (by have := heatVariance_pos ha; positivity))).mpr
  apply Real.sqrt_le_sqrt
  rw [coe_heatVariance ha.le, coe_heatVariance hb.le]
  nlinarith [Real.pi_pos]

theorem abs_coordinate_product_le_squareMass (x : I → ℝ) (i j : I) :
    |x i * x j| ≤ squareMass x := by
  have hi := sq_coordinate_le_squareMass x i
  have hj := sq_coordinate_le_squareMass x j
  rw [abs_mul]
  nlinarith [sq_nonneg (|x i| - |x j|), sq_abs (x i), sq_abs (x j)]

def heatHessianBound (I : Type*) [Fintype I] (t : ℝ) : ℝ :=
  (4 * t * heatKernelBound I t) / (4 * t ^ 2) + heatKernelBound I t / (2 * t)

theorem norm_heatKernelHessian_le [DecidableEq I] {t : ℝ} (ht : 0 < t)
    (x : I → ℝ) (i j : I) :
    ‖heatKernelHessian t x i j‖ ≤ heatHessianBound I t := by
  have hfac : |x i * x j / (4 * t ^ 2) - if i = j then 1 / (2 * t) else 0| ≤
      squareMass x / (4 * t ^ 2) + 1 / (2 * t) := by
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rw [abs_div, abs_of_pos (by positivity : 0 < 4 * t ^ 2)]
      exact div_le_div_of_nonneg_right (abs_coordinate_product_le_squareMass x i j)
        (by positivity)
    · by_cases hij : i = j
      · rw [if_pos hij, abs_of_pos (by positivity : 0 < 1 / (2 * t))]
      · rw [if_neg hij, abs_zero]
        positivity
  unfold heatKernelHessian heatHessianBound
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel_nonneg _ _)]
  calc
    _ ≤ (squareMass x / (4 * t ^ 2) + 1 / (2 * t)) * heatKernel t x :=
      mul_le_mul_of_nonneg_right hfac (heatKernel_nonneg _ _)
    _ = squareMass x * heatKernel t x / (4 * t ^ 2) +
        heatKernel t x / (2 * t) := by ring
    _ ≤ _ := add_le_add
      (div_le_div_of_nonneg_right (squareMass_mul_heatKernel_le ht x) (by positivity))
      (div_le_div_of_nonneg_right (heatKernel_le_bound t x) (by positivity))

theorem continuous_heatKernelHessian [DecidableEq I] (t : ℝ) (i j : I) :
    Continuous (fun x : I → ℝ => heatKernelHessian t x i j) := by
  unfold heatKernelHessian
  exact (((continuous_apply i).mul (continuous_apply j)).div_const _ |>.sub continuous_const).mul
    (continuous_heatKernel t)

theorem hasDerivAt_heatKernelGradient_coordinate [DecidableEq I]
    {t : ℝ} (ht : 0 < t) (x : I → ℝ) (i j : I) (s : ℝ) :
    HasDerivAt (fun u : ℝ => heatKernelGradient t (x + u • (Pi.single j 1 : I → ℝ)) i)
      (heatKernelHessian t (x + s • (Pi.single j 1 : I → ℝ)) i j) s := by
  have hc : HasDerivAt (fun u : ℝ => -(x i + u * (Pi.single j 1 : I → ℝ) i) / (2 * t))
      (-(Pi.single j 1 : I → ℝ) i / (2 * t)) s := by
    simpa using (((hasDerivAt_const s (x i)).add
      ((hasDerivAt_id s).mul_const ((Pi.single j 1 : I → ℝ) i))).neg.div_const (2 * t))
  convert hc.mul (hasDerivAt_heatKernel_coordinate ht x j s) using 1
  unfold heatKernelGradient heatKernelHessian
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst j
    simp [Pi.single_apply]
    field_simp <;> ring
  · simp [Pi.single_apply, hij, Ne.symm hij]
    field_simp <;> ring

theorem heatKernelTimeDerivative_eq_laplacian [DecidableEq I] (t : ℝ) (x : I → ℝ) :
    heatKernelTimeDerivative t x = ∑ i, heatKernelHessian t x i i := by
  unfold heatKernelTimeDerivative heatKernelHessian
  simp only [ite_true, ← Finset.sum_mul, Finset.sum_sub_distrib, ← Finset.sum_div,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  simp only [squareMass, pow_two, mul_one]

def heatDensityHessian [DecidableEq I]
    (μ : Measure (I → ℝ)) (t : ℝ) (x : I → ℝ) (i j : I) : ℝ :=
  ∫ y, heatKernelHessian t (x - y) i j ∂μ

theorem integrable_heatKernelHessian_shift [DecidableEq I]
    (μ : Measure (I → ℝ)) [IsFiniteMeasure μ] {t : ℝ} (ht : 0 < t)
    (x : I → ℝ) (i j : I) :
    Integrable (fun y => heatKernelHessian t (x - y) i j) μ := by
  apply (integrable_const (heatHessianBound I t)).mono'
    (((continuous_heatKernelHessian t i j).comp
      (continuous_const.sub continuous_id)).measurable.aestronglyMeasurable)
  exact ae_of_all _ (fun y => norm_heatKernelHessian_le ht (x - y) i j)

theorem hasDerivAt_heatDensityGradient_coordinate [DecidableEq I]
    (μ : Measure (I → ℝ)) [IsFiniteMeasure μ] {t : ℝ} (ht : 0 < t)
    (x : I → ℝ) (i j : I) (s : ℝ) :
    HasDerivAt
      (fun u : ℝ => heatDensityGradient μ t (x + u • (Pi.single j 1 : I → ℝ)) i)
      (heatDensityHessian μ t (x + s • (Pi.single j 1 : I → ℝ)) i j) s := by
  have hm (u : ℝ) : AEStronglyMeasurable
      (fun y : I → ℝ => heatKernelGradient t (x + u • (Pi.single j 1 : I → ℝ) - y) i) μ :=
    ((continuous_heatKernelGradient t i).comp
      (continuous_const.sub continuous_id)).measurable.aestronglyMeasurable
  have hgm (u : ℝ) : AEStronglyMeasurable
      (fun y : I → ℝ => heatKernelHessian t
        (x + u • (Pi.single j 1 : I → ℝ) - y) i j) μ :=
    ((continuous_heatKernelHessian t i j).comp
      (continuous_const.sub continuous_id)).measurable.aestronglyMeasurable
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (x₀ := s) (ε := 1)
    (F := fun u y => heatKernelGradient t (x + u • (Pi.single j 1 : I → ℝ) - y) i)
    (F' := fun u y => heatKernelHessian t (x + u • (Pi.single j 1 : I → ℝ) - y) i j)
    (bound := fun _ => heatHessianBound I t)
    zero_lt_one (Filter.Eventually.of_forall hm)
    (integrable_heatKernelGradient_shift μ ht _ i) (hgm s)
    (ae_of_all _ (fun y u _ => norm_heatKernelHessian_le ht _ i j))
    (integrable_const _) (ae_of_all _ (fun y u _ => by
      simpa only [sub_add_eq_add_sub] using
        hasDerivAt_heatKernelGradient_coordinate ht (x - y) i j u))).2

theorem heatHessianBound_eq {t : ℝ} (ht : 0 < t) :
    heatHessianBound I t = ((3 / 2 : ℝ) * heatKernelBound I t) / t := by
  unfold heatHessianBound
  field_simp [ht.ne']
  ring

theorem heatHessianBound_antitoneOn (I : Type*) [Fintype I] :
    AntitoneOn (heatHessianBound I) (Set.Ioi 0) := by
  intro a ha b hb hab
  rw [heatHessianBound_eq ha, heatHessianBound_eq hb]
  exact div_le_div₀ (by have := heatKernelBound_nonneg I a; positivity)
    (mul_le_mul_of_nonneg_left (heatKernelBound_antitoneOn I ha hb hab) (by norm_num)) ha hab

theorem continuous_heatKernelTimeDerivative (t : ℝ) :
    Continuous (heatKernelTimeDerivative (I := I) t) := by
  unfold heatKernelTimeDerivative
  exact ((continuous_squareMass.div_const _).sub continuous_const).mul (continuous_heatKernel t)

theorem norm_heatKernelTimeDerivative_le {t : ℝ} (ht : 0 < t) (x : I → ℝ) :
    ‖heatKernelTimeDerivative t x‖ ≤ (Fintype.card I : ℝ) * heatHessianBound I t := by
  classical
  rw [heatKernelTimeDerivative_eq_laplacian]
  calc
    _ ≤ ∑ i, ‖heatKernelHessian t x i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : I, heatHessianBound I t :=
      Finset.sum_le_sum (fun i _ => norm_heatKernelHessian_le ht x i i)
    _ = _ := by simp

def heatDensityTimeDerivative (μ : Measure (I → ℝ)) (t : ℝ) (x : I → ℝ) : ℝ :=
  ∫ y, heatKernelTimeDerivative t (x - y) ∂μ

theorem integrable_heatKernelTimeDerivative_shift
    (μ : Measure (I → ℝ)) [IsFiniteMeasure μ] {t : ℝ} (ht : 0 < t) (x : I → ℝ) :
    Integrable (fun y => heatKernelTimeDerivative t (x - y)) μ := by
  apply (integrable_const ((Fintype.card I : ℝ) * heatHessianBound I t)).mono'
    (((continuous_heatKernelTimeDerivative t).comp
      (continuous_const.sub continuous_id)).measurable.aestronglyMeasurable)
  exact ae_of_all _ (fun y => norm_heatKernelTimeDerivative_le ht (x - y))

/-- Heat-time differentiation under the arbitrary finite mixing measure.
The time interval is kept a positive distance from zero, and all derivative
kernels are bounded by one integrable constant on that interval. -/
theorem hasDerivAt_heatDensity_time
    (μ : Measure (I → ℝ)) [IsFiniteMeasure μ] {t : ℝ} (ht : 0 < t) (x : I → ℝ) :
    HasDerivAt (fun u : ℝ => heatDensity μ u x) (heatDensityTimeDerivative μ t x) t := by
  have htime (u : ℝ) (hu : u ∈ Metric.ball t (t / 2)) : t / 2 < u := by
    rw [Metric.mem_ball, Real.dist_eq] at hu
    have := (abs_lt.mp hu).1
    linarith
  have hm (u : ℝ) : AEStronglyMeasurable (fun y : I → ℝ => heatKernel u (x - y)) μ :=
    ((continuous_heatKernel u).comp (continuous_const.sub continuous_id)).measurable.aestronglyMeasurable
  have hgm : AEStronglyMeasurable
      (fun y : I → ℝ => heatKernelTimeDerivative t (x - y)) μ :=
    ((continuous_heatKernelTimeDerivative t).comp
      (continuous_const.sub continuous_id)).measurable.aestronglyMeasurable
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (x₀ := t) (ε := t / 2)
    (F := fun u y => heatKernel u (x - y))
    (F' := fun u y => heatKernelTimeDerivative u (x - y))
    (bound := fun _ => (Fintype.card I : ℝ) * heatHessianBound I (t / 2))
    (by positivity) (Filter.Eventually.of_forall hm)
    (integrable_heatKernel_shift μ t x) hgm
    (ae_of_all _ (fun y u hu => (norm_heatKernelTimeDerivative_le
      (lt_trans (by positivity : 0 < t / 2) (htime u hu)) (x - y)).trans
        (mul_le_mul_of_nonneg_left
          (heatHessianBound_antitoneOn I (show 0 < t / 2 by positivity)
            (lt_trans (by positivity : 0 < t / 2) (htime u hu)) (htime u hu).le)
          (Nat.cast_nonneg _))))
    (integrable_const _)
    (ae_of_all _ (fun y u hu => hasDerivAt_heatKernel_time
      (lt_trans (by positivity : 0 < t / 2) (htime u hu)) (x - y)))).2

theorem heatDensityTimeDerivative_eq_laplacian [DecidableEq I]
    (μ : Measure (I → ℝ)) [IsFiniteMeasure μ] {t : ℝ} (ht : 0 < t) (x : I → ℝ) :
    heatDensityTimeDerivative μ t x = ∑ i, heatDensityHessian μ t x i i := by
  unfold heatDensityTimeDerivative
  simp_rw [heatKernelTimeDerivative_eq_laplacian]
  rw [integral_finset_sum _ (fun i _ => integrable_heatKernelHessian_shift μ ht x i i)]
  rfl

/-- The actual density solves the heat equation at every positive time. -/
theorem heatDensity_heatEquation [DecidableEq I]
    (μ : Measure (I → ℝ)) [IsFiniteMeasure μ] {t : ℝ} (ht : 0 < t) (x : I → ℝ) :
    deriv (fun u : ℝ => heatDensity μ u x) t =
      ∑ i, deriv (fun u : ℝ =>
        heatDensityGradient μ t (x + u • (Pi.single i 1 : I → ℝ)) i) 0 := by
  rw [(hasDerivAt_heatDensity_time μ ht x).deriv, heatDensityTimeDerivative_eq_laplacian μ ht]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [zero_smul, add_zero] using
    (hasDerivAt_heatDensityGradient_coordinate μ ht x i i 0).deriv.symm

end GaussianWave.BS
