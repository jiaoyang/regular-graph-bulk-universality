import GaussianWave.GaussianContinuity

/-!
# The actual-law Gaussian step in BS upper-bound strictness

This module proves uniqueness of the stationary law of a contractive Gaussian
Ornstein--Uhlenbeck step, simultaneously for any fixed finite number of
channels. Stationarity is equality of actual probability measures obtained by
mapping a genuine product law. No Gaussianity or moment hypothesis on the
unknown measure is assumed. The separate score/log-density argument that
produces this stationarity is not asserted here.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace GaussianWave.BS

/-- Finite-dimensional characteristic integral in physical channel coordinates. -/
def characteristicIntegral {ι : Type*} [Fintype ι]
    (μ : Measure (ι → ℝ)) (t : ι → ℝ) : ℂ :=
  ∫ x, Complex.exp ((↑(finiteLinearForm t x) : ℂ) * Complex.I) ∂μ

lemma finiteLinearForm_scale_coeff {ι : Type*} [Fintype ι]
    (a : ℝ) (t x : ι → ℝ) :
    finiteLinearForm (fun i => a * t i) x = a * finiteLinearForm t x := by
  simp only [finiteLinearForm, Finset.mul_sum, mul_assoc]

/-- The map applied to an unknown vector and an independent Gaussian vector. -/
def affineGaussianMap {ι : Type*} (c a : ℝ)
    (z : (ι → ℝ) × (ι → ℝ)) : ι → ℝ :=
  fun i => c * z.1 i + a * z.2 i

lemma measurable_affineGaussianMap {ι : Type*} (c a : ℝ) :
    Measurable (@affineGaussianMap ι c a) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_const.mul ((measurable_pi_apply i).comp measurable_fst)).add
    (measurable_const.mul ((measurable_pi_apply i).comp measurable_snd))

/-- Actual affine Gaussian convolution, with independence represented by `prod`. -/
def affineGaussianLaw {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (ι → ℝ)) (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (c a : ℝ) :
    Measure (ι → ℝ) :=
  Measure.map (affineGaussianMap c a) (μ.prod (gaussianCovarianceLaw C hC))

instance affineGaussianLaw_isProbability {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (c a : ℝ) :
    IsProbabilityMeasure (affineGaussianLaw μ C hC c a) :=
  MeasureTheory.isProbabilityMeasure_map (measurable_affineGaussianMap c a).aemeasurable

lemma finiteLinearForm_affineGaussianMap {ι : Type*} [Fintype ι]
    (c a : ℝ) (t : ι → ℝ) (z : (ι → ℝ) × (ι → ℝ)) :
    finiteLinearForm t (affineGaussianMap c a z) =
      finiteLinearForm (fun i => c * t i) z.1 +
        finiteLinearForm (fun i => a * t i) z.2 := by
  simp only [finiteLinearForm, affineGaussianMap, mul_add, Finset.sum_add_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring_nf

/-- The characteristic factor is computed from the literal independent product. -/
theorem affineGaussianLaw_characteristic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (c a : ℝ) (t : ι → ℝ) :
    characteristicIntegral (affineGaussianLaw μ C hC c a) t =
      characteristicIntegral μ (fun i => c * t i) *
        Complex.exp (Complex.ofReal (-(1 / 2 : ℝ) * a ^ 2 * finiteCovarianceQuadratic C t)) := by
  rw [characteristicIntegral, affineGaussianLaw,
    integral_map (measurable_affineGaussianMap c a).aemeasurable]
  · have heq (z : (ι → ℝ) × (ι → ℝ)) :
        Complex.exp ((↑(finiteLinearForm t (affineGaussianMap c a z)) : ℂ) * Complex.I) =
          Complex.exp ((↑(finiteLinearForm (fun i => c * t i) z.1) : ℂ) * Complex.I) *
            Complex.exp ((↑(finiteLinearForm (fun i => a * t i) z.2) : ℂ) * Complex.I) := by
      rw [finiteLinearForm_affineGaussianMap, Complex.ofReal_add, add_mul, Complex.exp_add]
    simp_rw [heq]
    rw [integral_prod_mul
      (fun x : ι → ℝ => Complex.exp ((↑(finiteLinearForm (fun i => c * t i) x) : ℂ) * Complex.I))
      (fun x : ι → ℝ => Complex.exp ((↑(finiteLinearForm (fun i => a * t i) x) : ℂ) * Complex.I))]
    have hg := gaussianCovarianceLaw_characteristic C hC (fun i => a * t i)
    change characteristicIntegral (gaussianCovarianceLaw C hC) (fun i => a * t i) = _ at hg
    change characteristicIntegral μ (fun i => c * t i) *
      characteristicIntegral (gaussianCovarianceLaw C hC) (fun i => a * t i) = _
    rw [hg, finiteCovarianceQuadratic_smul]
    congr 2
    ring_nf
  · exact (linearCharacteristic t).continuous.measurable.aestronglyMeasurable

/-- Characteristic functions tend to one at vanishing scalar arguments.
The dominating function is one, so no moment assumption is used. -/
theorem characteristicIntegral_scale_tendsto_one {ι : Type*} [Fintype ι]
    (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    (s : ℕ → ℝ) (hs : Tendsto s atTop (𝓝 0)) (t : ι → ℝ) :
    Tendsto (fun n => characteristicIntegral μ (fun i => s n * t i)) atTop (𝓝 1) := by
  have h := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun n x => Complex.exp ((↑(finiteLinearForm (fun i => s n * t i) x) : ℂ) * Complex.I))
    (f := fun _ => (1 : ℂ)) (fun _ => (1 : ℝ))
    (fun n => (linearCharacteristic (fun i => s n * t i)).continuous.measurable.aestronglyMeasurable)
    (integrable_const 1) (fun n => Eventually.of_forall (fun x => by simp [Complex.norm_exp]))
    (Eventually.of_forall (fun x => by
      have hr : Tendsto (fun n => s n * finiteLinearForm t x) atTop (𝓝 0) := by
        simpa only [zero_mul] using hs.mul_const (finiteLinearForm t x)
      have hc := (Complex.continuous_ofReal.tendsto 0).comp hr
      have he := Complex.continuous_exp.continuousAt.tendsto.comp (hc.mul_const Complex.I)
      simpa only [finiteLinearForm_scale_coeff, Complex.ofReal_zero, zero_mul,
        Complex.exp_zero] using he))
  simpa only [characteristicIntegral, integral_const, measureReal_univ_eq_one, one_smul] using h

/-- A normalized OU step with prescribed Gaussian covariance. -/
def ouLaw {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (ι → ℝ)) (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (c : ℝ) :
    Measure (ι → ℝ) :=
  affineGaussianLaw μ C hC c (Real.sqrt (1 - c ^ 2))

instance ouLaw_isProbability {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (c : ℝ) :
    IsProbabilityMeasure (ouLaw μ C hC c) := by
  unfold ouLaw
  infer_instance

/-- Uniqueness of the actual OU stationary law, including singular covariance
and any finite channel count. This is the final root-law step of strictness;
the source score identities must still be used to establish stationarity. -/
theorem eq_gaussian_of_ou_stationary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (c : ℝ) (hc : |c| < 1)
    (hstationary : ouLaw μ C hC c = μ) :
    μ = gaussianCovarianceLaw C hC := by
  have hc2 : 0 < 1 - c ^ 2 := by
    obtain ⟨hlo, hhi⟩ := abs_lt.mp hc
    nlinarith
  have hsq : Real.sqrt (1 - c ^ 2) ^ 2 = 1 - c ^ 2 := Real.sq_sqrt hc2.le
  have hrec (t : ι → ℝ) :
      characteristicIntegral μ t = characteristicIntegral μ (fun i => c * t i) *
        Complex.exp (Complex.ofReal (-(1 / 2 : ℝ) * (1 - c ^ 2) * finiteCovarianceQuadratic C t)) := by
    calc
      _ = characteristicIntegral (ouLaw μ C hC c) t := by rw [hstationary]
      _ = _ := by rw [ouLaw, affineGaussianLaw_characteristic, hsq]
  apply eq_gaussianCovarianceLaw μ C hC
  intro t
  change characteristicIntegral μ t = _
  have hiter (n : ℕ) : characteristicIntegral μ t =
      characteristicIntegral μ (fun i => c ^ n * t i) *
        Complex.exp (Complex.ofReal (-(1 / 2 : ℝ) * (1 - (c ^ n) ^ 2) *
          finiteCovarianceQuadratic C t)) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hr := hrec (fun i => c ^ n * t i)
      have heq : (fun i => c * (c ^ n * t i)) = (fun i => c ^ (n + 1) * t i) := by
        funext i
        rw [pow_succ]
        ring_nf
      rw [heq, finiteCovarianceQuadratic_smul] at hr
      rw [ih, hr, mul_assoc, ← Complex.exp_add]
      congr 2
      rw [pow_succ]
      push_cast
      ring_nf
  have hpow : Tendsto (fun n : ℕ => c ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_iff.mpr hc
  have hp := characteristicIntegral_scale_tendsto_one μ (fun n => c ^ n) hpow t
  have hex : Tendsto (fun n : ℕ =>
      Complex.exp (Complex.ofReal (-(1 / 2 : ℝ) * (1 - (c ^ n) ^ 2) *
        finiteCovarianceQuadratic C t))) atTop
      (𝓝 (Complex.exp (Complex.ofReal (-(1 / 2 : ℝ) * finiteCovarianceQuadratic C t)))) := by
    have hbase : Tendsto (fun n : ℕ => (1 : ℝ) - (c ^ n) ^ 2) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
        (hpow.pow 2)
    have hr := (hbase.const_mul (-(1 / 2 : ℝ))).mul_const (finiteCovarianceQuadratic C t)
    have he := Complex.continuous_exp.continuousAt.tendsto.comp
      ((Complex.continuous_ofReal.continuousAt.tendsto).comp hr)
    simpa only [Function.comp_def, mul_one] using he
  have hh := hp.mul hex
  have heq : (fun n : ℕ => characteristicIntegral μ (fun i => c ^ n * t i) *
      Complex.exp (Complex.ofReal (-(1 / 2 : ℝ) * (1 - (c ^ n) ^ 2) *
        finiteCovarianceQuadratic C t))) = (fun _ : ℕ => characteristicIntegral μ t) :=
    funext (fun n => (hiter n).symm)
  rw [heq] at hh
  have hout := tendsto_nhds_unique tendsto_const_nhds hh
  simpa only [one_mul] using hout

/-- Gaussian convolution with a nonzero signal coefficient is injective on
actual probability laws. The Gaussian characteristic factor never vanishes. -/
theorem eq_of_affineGaussianLaw_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ ν : Measure (ι → ℝ)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (c a : ℝ) (hc : c ≠ 0)
    (h : affineGaussianLaw μ C hC c a = affineGaussianLaw ν C hC c a) : μ = ν := by
  apply measure_eq_of_linear_characteristic
  intro t
  change characteristicIntegral μ t = characteristicIntegral ν t
  let u : ι → ℝ := fun i => c⁻¹ * t i
  have hh := congrArg (fun ρ => characteristicIntegral ρ u) h
  change characteristicIntegral (affineGaussianLaw μ C hC c a) u =
    characteristicIntegral (affineGaussianLaw ν C hC c a) u at hh
  rw [affineGaussianLaw_characteristic, affineGaussianLaw_characteristic] at hh
  have hscale : (fun i => c * u i) = t := by
    funext i
    dsimp [u]
    rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  rw [hscale] at hh
  exact mul_right_cancel₀ (Complex.exp_ne_zero _) hh

/-- The canonical Gaussian law is preserved by a normalized OU step. -/
theorem ouLaw_gaussian_eq_self {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (c : ℝ) (hc : |c| ≤ 1) :
    ouLaw (gaussianCovarianceLaw C hC) C hC c = gaussianCovarianceLaw C hC := by
  have hc2 : 0 ≤ 1 - c ^ 2 := by
    nlinarith [abs_nonneg c, sq_abs c]
  have hsq : Real.sqrt (1 - c ^ 2) ^ 2 = 1 - c ^ 2 := Real.sq_sqrt hc2
  apply eq_gaussianCovarianceLaw _ C hC
  intro t
  change characteristicIntegral (ouLaw _ C hC c) t = _
  rw [ouLaw, affineGaussianLaw_characteristic, hsq]
  have hg := gaussianCovarianceLaw_characteristic C hC (fun i => c * t i)
  change characteristicIntegral (gaussianCovarianceLaw C hC) (fun i => c * t i) = _ at hg
  rw [hg, finiteCovarianceQuadratic_smul, ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf

/-- Gaussianity of a nontrivially smoothed OU law implies Gaussianity of the
original law by actual Gaussian-convolution injectivity. -/
theorem eq_gaussian_of_gaussian_ouLaw {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (c : ℝ)
    (hc0 : c ≠ 0) (hc : |c| ≤ 1)
    (h : ouLaw μ C hC c = gaussianCovarianceLaw C hC) :
    μ = gaussianCovarianceLaw C hC := by
  apply eq_of_affineGaussianLaw_eq μ (gaussianCovarianceLaw C hC) C hC c
    (Real.sqrt (1 - c ^ 2)) hc0
  exact h.trans (ouLaw_gaussian_eq_self C hC c hc).symm

end GaussianWave.BS
