import GaussianWave.BS.HeatRegularity
import GaussianWave.BS.HeatBounds
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Third-order smoothing for the actual arbitrary-measure heat density

Finite Gaussian derivative bounds justify differentiating the actual finite
mixing integral. The resulting third-order regularity is used for the
symmetric mixed-derivative tensor of the logarithmic heat density.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators ContDiff

namespace GaussianWave.BS
variable {I : Type*} [Fintype I] [DecidableEq I]

private theorem pi_eq_sum_single (v : I → ℝ) :
    v = ∑ i, v i • (Pi.single i 1 : I → ℝ) := by
  ext j
  simp [Pi.single_apply, Finset.sum_apply]

private theorem clm_apply_eq_sum (L : (I → ℝ) →L[ℝ] ℝ) (v : I → ℝ) :
    L v = ∑ i, L (Pi.single i 1) * v i := by
  conv_lhs => rw [pi_eq_sum_single v]
  simp only [map_sum, map_smul, smul_eq_mul]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

private theorem norm_clm_le_of_single_bound (L : (I → ℝ) →L[ℝ] ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hL : ∀ i, ‖L (Pi.single i 1)‖ ≤ B) :
    ‖L‖ ≤ (Fintype.card I : ℝ) * B := by
  apply L.opNorm_le_bound (mul_nonneg (Nat.cast_nonneg _) hB)
  intro v
  rw [clm_apply_eq_sum]
  calc
    _ ≤ ∑ i, ‖L (Pi.single i 1) * v i‖ := norm_sum_le _ _
    _ = ∑ i, ‖L (Pi.single i 1)‖ * ‖v i‖ := by simp_rw [norm_mul]
    _ ≤ ∑ _i : I, B * ‖v‖ := Finset.sum_le_sum (fun i _ =>
      mul_le_mul (hL i) (norm_le_pi_norm v i) (norm_nonneg _) hB)
    _ = _ := by simp; ring

/-- A bounded first derivative gives genuine C1 smoothing under every finite
mixing measure. This is a proved differentiation theorem, not a regularity
contract on the heat flow. -/
private theorem contDiff_one_integral_translate
    (μ : Measure (I → ℝ)) [IsFiniteMeasure μ]
    (k : (I → ℝ) → ℝ) (hk : ContDiff ℝ ∞ k)
    (B₀ B₁ : ℝ) (hB₀ : ∀ x, ‖k x‖ ≤ B₀) (hB₁ : ∀ x, ‖fderiv ℝ k x‖ ≤ B₁) :
    ContDiff ℝ 1 (fun x => ∫ y, k (x - y) ∂μ) := by
  let D : (I → ℝ) → (I → ℝ) →L[ℝ] ℝ := fun x => ∫ y, fderiv ℝ k (x - y) ∂μ
  have hi (x : I → ℝ) : Integrable (fun y => k (x - y)) μ := by
    apply (integrable_const B₀).mono'
      ((hk.continuous.comp (continuous_const.sub continuous_id)).measurable.aestronglyMeasurable)
    exact ae_of_all _ (fun y => hB₀ (x - y))
  have hD : Continuous D := by
    apply continuous_iff_continuousAt.mpr
    intro x
    apply continuousAt_of_dominated (bound := fun _ => B₁)
    · exact Eventually.of_forall (fun z =>
        (((hk.continuous_fderiv (by simp)).comp
          (continuous_const.sub continuous_id)).measurable.aestronglyMeasurable))
    · exact Eventually.of_forall (fun z => ae_of_all _ (fun y => hB₁ (z - y)))
    · exact integrable_const _
    · exact ae_of_all _ (fun y =>
        ((hk.continuous_fderiv (by simp)).comp
          (continuous_id.sub continuous_const)).continuousAt)
  apply contDiff_one_iff_hasFDerivAt.mpr
  refine ⟨D, hD, ?_⟩
  intro x
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun z y : I → ℝ => k (z - y))
    (F' := fun z y : I → ℝ => fderiv ℝ k (z - y))
    (bound := fun _ => B₁) (ε := 1) zero_lt_one
  · exact Eventually.of_forall (fun z =>
      (hk.continuous.comp (continuous_const.sub continuous_id)).measurable.aestronglyMeasurable)
  · exact hi x
  · exact ((hk.continuous_fderiv (by simp)).comp
      (continuous_const.sub continuous_id)).measurable.aestronglyMeasurable
  · exact ae_of_all _ (fun y z _ => hB₁ (z - y))
  · exact integrable_const _
  · exact ae_of_all _ (fun y z _ => by
      simpa only [ContinuousLinearMap.comp_id] using
        ((hk.differentiable (by simp) (z - y)).hasFDerivAt).comp z (hasFDerivAt_sub_const y))

theorem contDiff_heatKernelGradient (t : ℝ) (i : I) :
    ContDiff ℝ ∞ (fun x : I → ℝ => heatKernelGradient t x i) := by
  unfold heatKernelGradient
  exact (((contDiff_apply ℝ ℝ i).neg.div_const _).mul (contDiff_heatKernel t))

theorem contDiff_heatKernelHessian (t : ℝ) (i j : I) :
    ContDiff ℝ ∞ (fun x : I → ℝ => heatKernelHessian t x i j) := by
  unfold heatKernelHessian
  exact ((((contDiff_apply ℝ ℝ i).mul (contDiff_apply ℝ ℝ j)).div_const _).sub
    contDiff_const).mul (contDiff_heatKernel t)

theorem fderiv_heatKernelGradient_single {t : ℝ} (ht : 0 < t)
    (x : I → ℝ) (i j : I) :
    fderiv ℝ (fun z => heatKernelGradient t z i) x (Pi.single j 1) = heatKernelHessian t x i j := by
  have h1 := ((contDiff_heatKernelGradient t i).differentiable (by simp) x).hasFDerivAt.hasLineDerivAt
    (Pi.single j 1 : I → ℝ)
  have h2 := hasDerivAt_heatKernelGradient_coordinate ht x i j 0
  simp only [zero_smul, add_zero] at h2
  exact h1.unique h2

theorem norm_fderiv_heatKernelGradient_le {t : ℝ} (ht : 0 < t) (x : I → ℝ) (i : I) :
    ‖fderiv ℝ (fun z => heatKernelGradient t z i) x‖ ≤
      (Fintype.card I : ℝ) * heatHessianBound I t := by
  apply norm_clm_le_of_single_bound _ _
    (by rw [heatHessianBound_eq ht]; have := heatKernelBound_nonneg I t; positivity)
  intro j
  rw [fderiv_heatKernelGradient_single ht]
  exact norm_heatKernelHessian_le ht x i j

theorem contDiff_one_heatDensityGradient
    (μ : Measure (I → ℝ)) [IsFiniteMeasure μ] {t : ℝ} (ht : 0 < t) (i : I) :
    ContDiff ℝ 1 (fun x => heatDensityGradient μ t x i) :=
  contDiff_one_integral_translate μ _ (contDiff_heatKernelGradient t i)
    (heatGradientBound I t) ((Fintype.card I : ℝ) * heatHessianBound I t)
    (fun x => norm_heatKernelGradient_le ht x i)
    (fun x => norm_fderiv_heatKernelGradient_le ht x i)

theorem squareMass_sq_mul_heatKernel_le {t : ℝ} (ht : 0 < t) (x : I → ℝ) :
    squareMass x ^ 2 * heatKernel t x ≤ (64 * t ^ 2) * heatKernelBound I t := by
  have h := squareMass_mul_heatKernel_le (by positivity : 0 < 2 * t) x
  rw [heatKernel_factor (by positivity : 0 < 2 * t)] at h
  have hB := heatKernelBound_pos (I := I) (by positivity : 0 < 2 * t)
  have he : -squareMass x / (4 * (2 * t)) = -squareMass x / (8 * t) := by ring
  rw [he] at h
  have hp : squareMass x * Real.exp (-squareMass x / (8 * t)) ≤ 8 * t := by nlinarith
  have hpn : 0 ≤ squareMass x * Real.exp (-squareMass x / (8 * t)) :=
    mul_nonneg (squareMass_nonneg _) (Real.exp_pos _).le
  have hs : (squareMass x * Real.exp (-squareMass x / (8 * t))) ^ 2 ≤ (8 * t) ^ 2 := by
    nlinarith
  have hsplit : Real.exp (-squareMass x / (4 * t)) =
      Real.exp (-squareMass x / (8 * t)) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [heatKernel_factor ht, hsplit]
  calc
    _ = heatKernelBound I t * (squareMass x * Real.exp (-squareMass x / (8 * t))) ^ 2 := by ring
    _ ≤ heatKernelBound I t * (8 * t) ^ 2 :=
      mul_le_mul_of_nonneg_left hs (heatKernelBound_nonneg _ _)
    _ = _ := by ring

theorem abs_coordinate_triple_mul_heatKernel_le {t : ℝ} (ht : 0 < t)
    (x : I → ℝ) (i j k : I) :
    |x i * x j * x k| * heatKernel t x ≤
      (1 + 128 * t ^ 2) * heatKernelBound I t := by
  have hq := squareMass_nonneg x
  have hk : |x k| ≤ 1 + squareMass x := by
    have := sq_coordinate_le_squareMass x k
    nlinarith [sq_nonneg (|x k| - 1), sq_abs (x k)]
  have hp : |x i * x j * x k| ≤ 1 + 2 * squareMass x ^ 2 := by
    rw [abs_mul]
    calc
      _ ≤ squareMass x * (1 + squareMass x) := mul_le_mul
        (abs_coordinate_product_le_squareMass x i j) hk (abs_nonneg _) hq
      _ ≤ _ := by nlinarith [sq_nonneg (squareMass x - 1)]
  calc
    _ ≤ (1 + 2 * squareMass x ^ 2) * heatKernel t x :=
      mul_le_mul_of_nonneg_right hp (heatKernel_nonneg _ _)
    _ = heatKernel t x + 2 * (squareMass x ^ 2 * heatKernel t x) := by ring
    _ ≤ heatKernelBound I t + 2 * ((64 * t ^ 2) * heatKernelBound I t) :=
      add_le_add (heatKernel_le_bound _ _) (mul_le_mul_of_nonneg_left
        (squareMass_sq_mul_heatKernel_le ht x) (by norm_num))
    _ = _ := by ring

def heatKernelThird (t : ℝ) (x : I → ℝ) (i j k : I) : ℝ :=
  (-(x i * x j * x k) / (8 * t ^ 3) +
    (if i = j then x k / (4 * t ^ 2) else 0) +
    (if i = k then x j / (4 * t ^ 2) else 0) +
    (if j = k then x i / (4 * t ^ 2) else 0)) * heatKernel t x

theorem hasDerivAt_heatKernelHessian_coordinate {t : ℝ} (ht : 0 < t)
    (x : I → ℝ) (i j k : I) (s : ℝ) :
    HasDerivAt (fun u : ℝ => heatKernelHessian t
      (x + u • (Pi.single k 1 : I → ℝ)) i j)
      (heatKernelThird t (x + s • (Pi.single k 1 : I → ℝ)) i j k) s := by
  let v : I → ℝ := Pi.single k 1
  have hi := (hasDerivAt_const s (x i)).add ((hasDerivAt_id s).mul_const (v i))
  have hj := (hasDerivAt_const s (x j)).add ((hasDerivAt_id s).mul_const (v j))
  have hp := ((hi.mul hj).div_const (4 * t ^ 2)).sub_const
    (if i = j then 1 / (2 * t) else 0)
  convert hp.mul (hasDerivAt_heatKernel_coordinate ht x k s) using 1
  unfold heatKernelThird heatKernelGradient
  dsimp only [v]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hik : i = k
  · subst i
    by_cases hjk : j = k
    · subst j
      simp only [Pi.single_eq_same, ite_true]
      field_simp <;> ring
    · simp only [Pi.single_eq_same, Pi.single_eq_of_ne hjk, if_neg hjk,
        if_neg (Ne.symm hjk), ite_true, zero_mul, mul_zero, add_zero]
      field_simp <;> ring
  · by_cases hjk : j = k
    · subst j
      simp only [Pi.single_eq_same, Pi.single_eq_of_ne hik, if_neg hik,
        if_neg (Ne.symm hik), ite_true, zero_mul, mul_zero, zero_add]
      field_simp <;> ring
    · by_cases hij : i = j
      · simp only [Pi.single_eq_of_ne hik, Pi.single_eq_of_ne hjk,
          if_pos hij, if_neg hik, if_neg hjk, zero_mul, mul_zero, zero_add, add_zero]
        field_simp <;> ring
      · simp only [Pi.single_eq_of_ne hik, Pi.single_eq_of_ne hjk,
          if_neg hij, if_neg hik, if_neg hjk, zero_mul, mul_zero, zero_add, add_zero]
        field_simp <;> ring

def heatThirdBound (I : Type*) [Fintype I] (t : ℝ) : ℝ :=
  ((1 + 128 * t ^ 2) * heatKernelBound I t) / (8 * t ^ 3) +
    3 * (((1 + 4 * t) * heatKernelBound I t) / (4 * t ^ 2))

theorem norm_heatKernelThird_le {t : ℝ} (ht : 0 < t)
    (x : I → ℝ) (i j k : I) : ‖heatKernelThird t x i j k‖ ≤ heatThirdBound I t := by
  let A := ((1 + 4 * t) * heatKernelBound I t) / (4 * t ^ 2)
  have hlin (l : I) : |x l / (4 * t ^ 2)| * heatKernel t x ≤ A := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 4 * t ^ 2), div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (abs_coordinate_mul_heatKernel_le ht x l) (by positivity)
  have hif (p : Prop) [Decidable p] (l : I) :
      |if p then x l / (4 * t ^ 2) else 0| * heatKernel t x ≤ A := by
    by_cases hp : p
    · simpa [hp] using hlin l
    · simp only [if_neg hp, abs_zero, zero_mul]
      dsimp [A]
      have := heatKernelBound_nonneg I t
      positivity
  have htriple : |-(x i * x j * x k) / (8 * t ^ 3)| * heatKernel t x ≤
      ((1 + 128 * t ^ 2) * heatKernelBound I t) / (8 * t ^ 3) := by
    rw [abs_div, abs_neg, abs_of_pos (by positivity : 0 < 8 * t ^ 3), div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (abs_coordinate_triple_mul_heatKernel_le ht x i j k) (by positivity)
  unfold heatKernelThird heatThirdBound
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel_nonneg _ _)]
  have habs := (abs_add (-(x i * x j * x k) / (8 * t ^ 3) +
    (if i = j then x k / (4 * t ^ 2) else 0) +
    (if i = k then x j / (4 * t ^ 2) else 0)) (if j = k then x i / (4 * t ^ 2) else 0)).trans
    (add_le_add_right ((abs_add _ _).trans (add_le_add_right (abs_add _ _) _)) _)
  have hm := mul_le_mul_of_nonneg_right habs (heatKernel_nonneg t x)
  dsimp [A] at hif
  nlinarith [hif (i = j) k, hif (i = k) j, hif (j = k) i]

theorem fderiv_heatKernelHessian_single {t : ℝ} (ht : 0 < t)
    (x : I → ℝ) (i j k : I) :
    fderiv ℝ (fun z => heatKernelHessian t z i j) x (Pi.single k 1) =
      heatKernelThird t x i j k := by
  have h1 := ((contDiff_heatKernelHessian t i j).differentiable (by simp) x).hasFDerivAt.hasLineDerivAt
    (Pi.single k 1 : I → ℝ)
  have h2 := hasDerivAt_heatKernelHessian_coordinate ht x i j k 0
  simp only [zero_smul, add_zero] at h2
  exact h1.unique h2

theorem norm_fderiv_heatKernelHessian_le {t : ℝ} (ht : 0 < t)
    (x : I → ℝ) (i j : I) :
    ‖fderiv ℝ (fun z => heatKernelHessian t z i j) x‖ ≤
      (Fintype.card I : ℝ) * heatThirdBound I t := by
  apply norm_clm_le_of_single_bound _ _
    (by unfold heatThirdBound; have := heatKernelBound_nonneg I t; positivity)
  intro k
  rw [fderiv_heatKernelHessian_single ht]
  exact norm_heatKernelThird_le ht x i j k

theorem contDiff_one_heatDensityHessian
    (μ : Measure (I → ℝ)) [IsFiniteMeasure μ] {t : ℝ} (ht : 0 < t) (i j : I) :
    ContDiff ℝ 1 (fun x => heatDensityHessian μ t x i j) :=
  contDiff_one_integral_translate μ _ (contDiff_heatKernelHessian t i j)
    (heatHessianBound I t) ((Fintype.card I : ℝ) * heatThirdBound I t)
    (fun x => norm_heatKernelHessian_le ht x i j)
    (fun x => norm_fderiv_heatKernelHessian_le ht x i j)

theorem fderiv_heatDensityGradient_single
    (μ : Measure (I → ℝ)) [IsFiniteMeasure μ] {t : ℝ} (ht : 0 < t)
    (x : I → ℝ) (i j : I) :
    fderiv ℝ (fun z => heatDensityGradient μ t z i) x (Pi.single j 1) =
      heatDensityHessian μ t x i j := by
  have h1 := ((contDiff_one_heatDensityGradient μ ht i).differentiable (by simp) x).hasFDerivAt.hasLineDerivAt
    (Pi.single j 1 : I → ℝ)
  have h2 := hasDerivAt_heatDensityGradient_coordinate μ ht x i j 0
  simp only [zero_smul, add_zero] at h2
  exact h1.unique h2

theorem fderiv_heatDensityGradient_apply
    (μ : Measure (I → ℝ)) [IsFiniteMeasure μ] {t : ℝ} (ht : 0 < t)
    (x v : I → ℝ) (i : I) :
    fderiv ℝ (fun z => heatDensityGradient μ t z i) x v =
      ∑ j, heatDensityHessian μ t x i j * v j := by
  rw [clm_apply_eq_sum]
  simp_rw [fderiv_heatDensityGradient_single μ ht]

theorem contDiff_two_heatDensityGradient
    (μ : Measure (I → ℝ)) [IsFiniteMeasure μ] {t : ℝ} (ht : 0 < t) (i : I) :
    ContDiff ℝ 2 (fun x => heatDensityGradient μ t x i) := by
  change ContDiff ℝ (1 + 1 : WithTop ℕ∞) (fun x => heatDensityGradient μ t x i)
  rw [contDiff_succ_iff_fderiv_apply]
  refine ⟨(contDiff_one_heatDensityGradient μ ht i).differentiable (by simp), by simp, ?_⟩
  intro v
  simp_rw [fderiv_heatDensityGradient_apply μ ht]
  exact ContDiff.sum (fun j _ => (contDiff_one_heatDensityHessian μ ht i j).mul contDiff_const)

/-- Every actual finite-measure Gaussian convolution is C3 at positive time.
No regularity premise on the initial input measure is used. -/
theorem contDiff_three_heatDensity
    (μ : Measure (I → ℝ)) [IsFiniteMeasure μ] {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ 3 (heatDensity μ t) := by
  change ContDiff ℝ (2 + 1 : WithTop ℕ∞) (heatDensity μ t)
  rw [contDiff_succ_iff_fderiv_apply]
  refine ⟨(contDiff_one_heatDensity μ ht).differentiable (by simp), by simp, ?_⟩
  intro v
  simp_rw [fderiv_heatDensity_apply μ ht]
  exact ContDiff.sum (fun i _ => (contDiff_two_heatDensityGradient μ ht i).mul contDiff_const)

/-- The actual log density has the C3 regularity required for the symmetric
third derivative tensor in the equality argument. -/
theorem contDiff_three_log_heatDensity
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ 3 (fun x => Real.log (heatDensity μ t x)) :=
  (contDiff_three_heatDensity μ ht).log (fun x => (heatDensity_pos μ ht x).ne')

end GaussianWave.BS
