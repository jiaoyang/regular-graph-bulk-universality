import GaussianWave.MomentTail

/-!
# Gaussian normalization from actual weak convergence and fourth moments

Adapted from the user's earlier GeneralizedBulk/Gaussian/UniformIntegrability
proofs, with dependencies reduced to Mathlib and this project's concrete
law definitions. Covariance is existential until the final theorem.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal
namespace GaussianWave

theorem centeredGaussian_mgf (v : ℝ≥0) (t : ℝ) :
    mgf id (gaussianReal 0 v) t = Real.exp ((v : ℝ) * t ^ 2 / 2) := by
  have h := mgf_gaussianReal (μ := (0 : ℝ)) (v := v)
    (by simp : Measure.map id (gaussianReal 0 v) = gaussianReal 0 v) t
  simpa only [zero_mul, zero_add] using h

theorem centeredGaussian_zero_interior (v : ℝ≥0) :
    (0 : ℝ) ∈ interior (integrableExpSet id (gaussianReal 0 v)) := by
  have heq : integrableExpSet id (gaussianReal 0 v) = Set.univ := by
    ext t
    simp only [integrableExpSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact mgf_pos_iff.mp (by rw [centeredGaussian_mgf]; exact Real.exp_pos _)
  rw [heq, interior_univ]
  trivial

theorem centeredGaussian_integrable_pow (v : ℝ≥0) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (gaussianReal 0 v) :=
  integrable_pow_of_mem_interior_integrableExpSet (centeredGaussian_zero_interior v) n

theorem centeredGaussian_second_moment (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v) = v := by
  let f0 := fun t : ℝ => Real.exp ((v : ℝ) * t ^ 2 / 2)
  let f1 := fun t : ℝ => (v : ℝ) * t * f0 t
  let f2 := fun t : ℝ => ((v : ℝ) + (v : ℝ) ^ 2 * t ^ 2) * f0 t
  have hd0 (t : ℝ) : HasDerivAt f0 (f1 t) t := by
    have h := ((((hasDerivAt_id t).pow 2).const_mul (v : ℝ)).div_const 2).exp
    convert h using 1; dsimp [f0, f1]; ring
  have hd1 (t : ℝ) : HasDerivAt f1 (f2 t) t := by
    convert ((hasDerivAt_id t).const_mul (v : ℝ)).mul (hd0 t) using 1;
      dsimp [f0, f1, f2]; ring
  have hi1 : iteratedDeriv 1 f0 = f1 := funext (fun t => by simpa using (hd0 t).deriv)
  have hi2 : iteratedDeriv 2 f0 = f2 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, hi1]
    exact funext (fun t => (hd1 t).deriv)
  have hm := iteratedDeriv_mgf_zero (centeredGaussian_zero_interior v) 2
  rw [show mgf id (gaussianReal 0 v) = f0 from funext (centeredGaussian_mgf v), hi2] at hm
  simpa [f0, f2] using hm.symm

theorem continuous_finiteLinearForm {ι : Type*} [Fintype ι] (t : ι → ℝ) :
    Continuous (finiteLinearForm t) :=
  continuous_finset_sum _ (fun i _ => continuous_const.mul (continuous_apply i))

theorem finiteCovarianceQuadratic_smul {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (s : ℝ) (t : ι → ℝ) :
    finiteCovarianceQuadratic C (fun i => s * t i) = s ^ 2 * finiteCovarianceQuadratic C t := by
  simp only [finiteCovarianceQuadratic, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Qualitative centered Gaussianity already supplies an actual scalar Gaussian
law for every projection, including degenerate projections. Its variance is
still the unspecified Gaussian covariance, not the desired normalization. -/
theorem centeredGaussian_linearProjection {ι : Type*} [Fintype ι]
    (ν : Measure (ι → ℝ)) [IsProbabilityMeasure ν] (C : Matrix ι ι ℝ)
    (hpos : ∀ t, 0 ≤ finiteCovarianceQuadratic C t)
    (hcf : ∀ t : ι → ℝ,
      (∫ x, Complex.exp ((↑(finiteLinearForm t x) : ℂ) * Complex.I) ∂ν) =
        Complex.exp (↑(-(1 / 2 : ℝ) * finiteCovarianceQuadratic C t) : ℂ))
    (t : ι → ℝ) :
    Measure.map (finiteLinearForm t) ν =
      gaussianReal 0 ⟨finiteCovarianceQuadratic C t, hpos t⟩ := by
  have hmeas := (continuous_finiteLinearForm t).measurable
  letI : IsProbabilityMeasure (Measure.map (finiteLinearForm t) ν) :=
    MeasureTheory.isProbabilityMeasure_map hmeas.aemeasurable
  apply Measure.ext_of_charFun
  funext s
  rw [charFun_apply, charFun_gaussianReal]
  rw [integral_map hmeas.aemeasurable]
  · have h := hcf (fun i => s * t i)
    rw [finiteCovarianceQuadratic_smul] at h
    convert h using 1
    · apply integral_congr_ae
      filter_upwards with x
      congr 1
      simp only [finiteLinearForm, RCLike.inner_apply, conj_trivial]
      push_cast
      simp [Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
    · congr 1
      push_cast
      ring
  · apply Measurable.aestronglyMeasurable
    fun_prop

theorem centeredGaussian_projection_integrable_pow {ι : Type*} [Fintype ι]
    (ν : Measure (ι → ℝ)) [IsProbabilityMeasure ν] (C : Matrix ι ι ℝ)
    (hpos : ∀ t, 0 ≤ finiteCovarianceQuadratic C t)
    (hcf : ∀ t : ι → ℝ,
      (∫ x, Complex.exp ((↑(finiteLinearForm t x) : ℂ) * Complex.I) ∂ν) =
        Complex.exp (↑(-(1 / 2 : ℝ) * finiteCovarianceQuadratic C t) : ℂ))
    (t : ι → ℝ) (q : ℕ) : Integrable (fun x => finiteLinearForm t x ^ q) ν := by
  have hmap := centeredGaussian_linearProjection ν C hpos hcf t
  have hi := centeredGaussian_integrable_pow ⟨finiteCovarianceQuadratic C t, hpos t⟩ q
  rw [← hmap] at hi
  exact (integrable_map_measure (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x ^ q)
    (Measure.map (finiteLinearForm t) ν)) (continuous_finiteLinearForm t).measurable.aemeasurable).mp hi

theorem centeredGaussian_projection_second_moment {ι : Type*} [Fintype ι]
    (ν : Measure (ι → ℝ)) [IsProbabilityMeasure ν] (C : Matrix ι ι ℝ)
    (hpos : ∀ t, 0 ≤ finiteCovarianceQuadratic C t)
    (hcf : ∀ t : ι → ℝ,
      (∫ x, Complex.exp ((↑(finiteLinearForm t x) : ℂ) * Complex.I) ∂ν) =
        Complex.exp (↑(-(1 / 2 : ℝ) * finiteCovarianceQuadratic C t) : ℂ))
    (t : ι → ℝ) :
    (∫ x, finiteLinearForm t x ^ 2 ∂ν) = finiteCovarianceQuadratic C t := by
  calc
    _ = ∫ y : ℝ, y ^ 2 ∂Measure.map (finiteLinearForm t) ν :=
      (integral_map (continuous_finiteLinearForm t).measurable.aemeasurable (by fun_prop)).symm
    _ = _ := by
      rw [centeredGaussian_linearProjection ν C hpos hcf, centeredGaussian_second_moment]
      rfl

/-- Qualitative BS Gaussianity, fourth-moment uniform integrability, and the
exact limiting empirical covariance determine the normalized characteristic
function. There is no covariance-loss assumption in this statement. -/
theorem no_covariance_loss {ι : Type*} [Fintype ι]
    (μ : ℕ → Measure (ι → ℝ)) (ν : Measure (ι → ℝ))
    [∀ n, IsProbabilityMeasure (μ n)]
    (hweak : WeakLawConverges μ ν) (hGaussian : CenteredGaussianLaw ν)
    (target : Matrix ι ι ℝ)
    (h4 : ∀ t : ι → ℝ, ∀ n, Integrable (fun x => finiteLinearForm t x ^ 4) (μ n))
    (hM : ∀ t : ι → ℝ, ∃ M : ℝ, ∀ n, (∫ x, finiteLinearForm t x ^ 4 ∂μ n) ≤ M)
    (hsecond : ∀ t : ι → ℝ, Tendsto (fun n => ∫ x, finiteLinearForm t x ^ 2 ∂μ n)
      atTop (𝓝 (finiteCovarianceQuadratic target t))) :
    ∀ t : ι → ℝ,
      (∫ x, Complex.exp ((↑(finiteLinearForm t x) : ℂ) * Complex.I) ∂ν) =
        Complex.exp (↑(-(1 / 2 : ℝ) * finiteCovarianceQuadratic target t) : ℂ) := by
  obtain ⟨hprob, C, hsym, hpos, hcf⟩ := hGaussian
  letI := hprob
  intro t
  obtain ⟨M, hM⟩ := hM t
  have hlim := weak_integral_sq_of_fourth μ ν hweak (finiteLinearForm t)
    (continuous_finiteLinearForm t) (h4 t)
    (centeredGaussian_projection_integrable_pow ν C hpos hcf t 4) M hM
  rw [centeredGaussian_projection_second_moment ν C hpos hcf t] at hlim
  have heq := tendsto_nhds_unique hlim (hsecond t)
  have h := hcf t
  change (∫ x, Complex.exp ((↑(finiteLinearForm t x) : ℂ) * Complex.I) ∂ν) =
    Complex.exp (↑(-(1 / 2 : ℝ) * finiteCovarianceQuadratic C t) : ℂ) at h
  rw [heq] at h
  exact h

theorem finiteLinearForm_norm_le {ι : Type*} [Fintype ι] (t x : ι → ℝ) :
    |finiteLinearForm t x| ≤ (∑ i, |t i|) * ‖x‖ := by
  calc
    _ ≤ ∑ i, |t i * x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |t i| * ‖x‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i)
        (abs_nonneg _)
    _ = _ := (Finset.sum_mul ..).symm

theorem finiteLinearForm_fourth_bound {ι : Type*} [Fintype ι] (t x : ι → ℝ) :
    finiteLinearForm t x ^ 4 ≤ (∑ i, |t i|) ^ 4 * ‖x‖ ^ 4 := by
  calc
    _ = |finiteLinearForm t x| ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
    _ ≤ ((∑ i, |t i|) * ‖x‖) ^ 4 :=
      pow_le_pow_left₀ (abs_nonneg _) (finiteLinearForm_norm_le t x) _
    _ = _ := mul_pow _ _ _

theorem integrable_finiteLinearForm_fourth {ι : Type*} [Fintype ι]
    (μ : Measure (ι → ℝ)) (h4 : Integrable (fun x => ‖x‖ ^ 4) μ) (t : ι → ℝ) :
    Integrable (fun x => finiteLinearForm t x ^ 4) μ := by
  apply (h4.const_mul ((∑ i, |t i|) ^ 4)).mono'
    (((continuous_finiteLinearForm t).pow 4).measurable.aestronglyMeasurable)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact finiteLinearForm_fourth_bound t x

/-- One fourth-norm bound is enough for every linear projection used in the
normalization theorem. -/
theorem projection_fourth_integral_bound {ι : Type*} [Fintype ι]
    (μ : Measure (ι → ℝ)) (h4 : Integrable (fun x => ‖x‖ ^ 4) μ)
    (M : ℝ) (hM : (∫ x, ‖x‖ ^ 4 ∂μ) ≤ M) (t : ι → ℝ) :
    (∫ x, finiteLinearForm t x ^ 4 ∂μ) ≤ (∑ i, |t i|) ^ 4 * M := by
  calc
    _ ≤ ∫ x, (∑ i, |t i|) ^ 4 * ‖x‖ ^ 4 ∂μ :=
      integral_mono (integrable_finiteLinearForm_fourth μ h4 t) (h4.const_mul _)
        (finiteLinearForm_fourth_bound t)
    _ = (∑ i, |t i|) ^ 4 * ∫ x, ‖x‖ ^ 4 ∂μ := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hM (by positivity)

theorem integrable_coord_product_of_norm_fourth {ι : Type*} [Fintype ι]
    (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ]
    (h4 : Integrable (fun x => ‖x‖ ^ 4) μ) (i j : ι) :
    Integrable (fun x => x i * x j) μ := by
  apply ((integrable_const (1 : ℝ)).add h4).mono'
    (((measurable_pi_apply i).mul (measurable_pi_apply j)).aestronglyMeasurable)
  filter_upwards [] with x
  change |x i * x j| ≤ 1 + ‖x‖ ^ 4
  rw [abs_mul]
  have hi : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
  have hj : |x j| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j
  have hm := mul_le_mul hi hj (abs_nonneg _) (norm_nonneg x)
  have hs := sq_nonneg (‖x‖ ^ 2 - 1)
  nlinarith

theorem integral_finiteLinearForm_sq {ι : Type*} [Fintype ι]
    (μ : Measure (ι → ℝ)) (t : ι → ℝ)
    (hpair : ∀ i j, Integrable (fun x => x i * x j) μ) :
    (∫ x, finiteLinearForm t x ^ 2 ∂μ) =
      ∑ i, ∑ j, t i * (∫ x, x i * x j ∂μ) * t j := by
  have heq (x : ι → ℝ) : finiteLinearForm t x ^ 2 =
      ∑ i, ∑ j, (t i * t j) * (x i * x j) := by
    simp only [finiteLinearForm, pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [heq]
  rw [integral_finset_sum _ (fun i hi => integrable_finset_sum _
    (fun j hj => (hpair i j).const_mul _))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finset_sum _ (fun j hj => (hpair i j).const_mul _)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_const_mul]
  ring

/-- Entrywise empirical covariance convergence and one uniform fourth-norm
bound completely normalize the qualitative joint Gaussian weak limit. -/
theorem no_covariance_loss_of_norm_fourth {ι : Type*} [Fintype ι]
    (μ : ℕ → Measure (ι → ℝ)) (ν : Measure (ι → ℝ))
    [∀ n, IsProbabilityMeasure (μ n)]
    (hweak : WeakLawConverges μ ν) (hGaussian : CenteredGaussianLaw ν)
    (target : Matrix ι ι ℝ)
    (h4 : ∀ n, Integrable (fun x => ‖x‖ ^ 4) (μ n))
    (M : ℝ) (hM : ∀ n, (∫ x, ‖x‖ ^ 4 ∂μ n) ≤ M)
    (hsecond : ∀ i j, Tendsto (fun n => ∫ x, x i * x j ∂μ n)
      atTop (𝓝 (target i j))) :
    ∀ t : ι → ℝ,
      (∫ x, Complex.exp ((↑(finiteLinearForm t x) : ℂ) * Complex.I) ∂ν) =
        Complex.exp (↑(-(1 / 2 : ℝ) * finiteCovarianceQuadratic target t) : ℂ) := by
  apply no_covariance_loss μ ν hweak hGaussian target
    (fun t n => integrable_finiteLinearForm_fourth (μ n) (h4 n) t)
    (fun t => ⟨(∑ i, |t i|) ^ 4 * M, fun n => projection_fourth_integral_bound (μ n) (h4 n) M (hM n) t⟩)
  intro t
  have hlim := tendsto_finset_sum Finset.univ (fun i hi => tendsto_finset_sum Finset.univ
    (fun j hj => ((hsecond i j).const_mul (t i)).mul_const (t j)))
  simpa only [integral_finiteLinearForm_sq (μ _) t
    (integrable_coord_product_of_norm_fourth (μ _) (h4 _)), finiteCovarianceQuadratic] using hlim


end GaussianWave
