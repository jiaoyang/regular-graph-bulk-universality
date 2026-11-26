import BourgadeHuang.CMS.TriangularEvolution

/-! Uniform exponential decay of the actual finite triangular backward evolution. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace BourgadeHuang.CMS
set_option maxHeartbeats 600000

lemma backwardIntegral_eq_integral (lam : ℂ) (f : ℝ → ℂ) (t s : ℝ) :
    backwardIntegral lam f t s =
      -(∫ u in t..s, Complex.exp (lam*((t-u:ℝ):ℂ))*f u) := by
  rw [backwardIntegral,neg_mul,← intervalIntegral.integral_const_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  dsimp only
  rw [← mul_assoc,← Complex.exp_add]
  congr 2
  push_cast
  ring

lemma integral_exp_decay_interval_le {a : ℝ} (ha : 0<a) (t s : ℝ) :
    (∫ u in t..s, Real.exp (-a*(u-t))) ≤ a⁻¹ := by
  have hd : ∀ u ∈ Set.uIcc t s, HasDerivAt
      (fun u : ℝ => -a⁻¹*Real.exp (-a*(u-t))) (Real.exp (-a*(u-t))) u := by
    intro u hu
    convert ((((hasDerivAt_id u).sub_const t).const_mul (-a)).exp).const_mul (-a⁻¹) using 1
    field_simp [ha.ne']
  have hc : Continuous (fun u : ℝ => Real.exp (-a*(u-t))) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable _ _)]
  simp only [sub_self,mul_zero,Real.exp_zero,mul_one]
  nlinarith [mul_nonneg (inv_nonneg.mpr ha.le) (Real.exp_nonneg (-a*(s-t)))]

/-- One backward convolution loses only the inverse half-gap. -/
lemma norm_backwardIntegral_le {lam : ℂ} {a B : ℝ} (ha : 0<a) (hB : 0≤B)
    (hlam : 2*a≤lam.re) {f : ℝ → ℂ} (hf : Continuous f) {t s : ℝ} (hts : t≤s)
    (hbound : ∀ u ∈ Icc t s, ‖f u‖≤B*Real.exp (-a*(s-u))) :
    ‖backwardIntegral lam f t s‖ ≤ (B*a⁻¹)*Real.exp (-a*(s-t)) := by
  rw [backwardIntegral_eq_integral,norm_neg]
  have hc : Continuous (fun u : ℝ => Complex.exp (lam*((t-u:ℝ):ℂ))*f u) := by fun_prop
  have hmajor : Continuous (fun u : ℝ =>
      (B*Real.exp (-a*(s-t)))*Real.exp (-a*(u-t))) := by fun_prop
  calc
    _ ≤ ∫ u in t..s, ‖Complex.exp (lam*((t-u:ℝ):ℂ))*f u‖ :=
      intervalIntegral.norm_integral_le_integral_norm hts
    _ ≤ ∫ u in t..s, (B*Real.exp (-a*(s-t)))*Real.exp (-a*(u-t)) := by
      apply intervalIntegral.integral_mono_on hts (hc.norm.intervalIntegrable _ _)
        (hmajor.intervalIntegrable _ _)
      intro u hu
      rw [norm_mul,Complex.norm_exp]
      have he : (lam*((t-u:ℝ):ℂ)).re ≤ -2*a*(u-t) := by
        simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
        nlinarith [mul_nonneg (sub_nonneg.mpr hlam) (sub_nonneg.mpr hu.1)]
      calc
        _ ≤ Real.exp (-2*a*(u-t)) * (B*Real.exp (-a*(s-u))) :=
          mul_le_mul (Real.exp_le_exp.mpr he) (hbound u hu) (norm_nonneg _) (Real.exp_nonneg _)
        _ = B*(Real.exp (-2*a*(u-t))*Real.exp (-a*(s-u))) := by ring
        _ = B*Real.exp (-2*a*(u-t)+ -a*(s-u)) := by rw [Real.exp_add]
        _ = B*(Real.exp (-a*(s-t))*Real.exp (-a*(u-t))) := by
          rw [← Real.exp_add]
          congr 2
          ring
        _ = _ := by ring
    _ = (B*Real.exp (-a*(s-t)))*(∫ u in t..s, Real.exp (-a*(u-t))) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ (B*Real.exp (-a*(s-t)))*a⁻¹ := mul_le_mul_of_nonneg_left
      (integral_exp_decay_interval_le ha t s) (mul_nonneg hB (Real.exp_nonneg _))
    _ = _ := by ring

variable {J : Type*} [Fintype J] [DecidableEq J]

lemma norm_triangularTerm_le (lam : J → ℂ) (N : ℝ → J → J → ℂ)
    (hNc : ∀ i j, Continuous (fun t => N t i j))
    {R a M : ℝ} (ha : 0<a) (hM : 0≤M)
    (hlam : ∀ i, 2*a≤(lam i).re)
    (hN : ∀ t, R≤t → ∀ i j, ‖N t i j‖≤M)
    (n : ℕ) {t s : ℝ} (ht : R≤t) (hts : t≤s) (i j : J) :
    ‖triangularTerm lam N n t s i j‖ ≤
      ((Fintype.card J:ℝ)*M*a⁻¹)^n * Real.exp (-a*(s-t)) := by
  induction n generalizing t s i j with
  | zero =>
    simp only [triangularTerm,pow_zero,one_mul]
    split_ifs
    · rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
      nlinarith [mul_nonneg (sub_nonneg.mpr (hlam i)) (sub_nonneg.mpr hts)]
    · simpa only [norm_zero] using Real.exp_nonneg (-a*(s-t))
  | succ n ih =>
    have hc : Continuous (fun u => ∑ k, N u i k*triangularTerm lam N n u s k j) := by
      apply continuous_finset_sum
      intro k hk
      exact (hNc i k).mul ((continuous_triangularTerm lam N hNc n k j).comp
        (continuous_id.prodMk continuous_const))
    have hbase : 0≤(Fintype.card J:ℝ)*M*a⁻¹ :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hM) (inv_nonneg.mpr ha.le)
    have hn := norm_backwardIntegral_le ha
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg (Fintype.card J)) hM) (pow_nonneg hbase n))
      (hlam i) hc hts (fun u hu => ?_)
    · simpa only [triangularTerm,pow_succ] using hn.trans_eq (by ring)
    · calc
        ‖∑ k, N u i k*triangularTerm lam N n u s k j‖ ≤
            ∑ k, ‖N u i k*triangularTerm lam N n u s k j‖ := norm_sum_le _ _
        _ ≤ ∑ k : J, M*(((Fintype.card J:ℝ)*M*a⁻¹)^n*Real.exp (-a*(s-u))) := by
          apply Finset.sum_le_sum
          intro k hk
          rw [norm_mul]
          exact mul_le_mul (hN u (ht.trans hu.1) i k)
            (ih (ht.trans hu.1) hu.2 k j) (norm_nonneg _) hM
        _ = ((Fintype.card J:ℝ)*M*((Fintype.card J:ℝ)*M*a⁻¹)^n)*Real.exp (-a*(s-u)) := by
          simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
          ring

/-- The actual evolution has uniform exponential backward decay. The finite
constant depends on the coefficient bound and degree cutoff, not on time. -/
theorem norm_triangularEvolution_le (lam : J → ℂ) (N : ℝ → J → J → ℂ)
    (hNc : ∀ i j, Continuous (fun t => N t i j))
    {R a M : ℝ} (ha : 0<a) (hM : 0≤M)
    (hlam : ∀ i, 2*a≤(lam i).re)
    (hN : ∀ t, R≤t → ∀ i j, ‖N t i j‖≤M)
    (H : ℕ) {t s : ℝ} (ht : R≤t) (hts : t≤s) (i j : J) :
    ‖triangularEvolution lam N H t s i j‖ ≤
      (∑ n ∈ Finset.range (H+1), ((Fintype.card J:ℝ)*M*a⁻¹)^n)*Real.exp (-a*(s-t)) := by
  apply (norm_sum_le _ _).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro n hn
  exact norm_triangularTerm_le lam N hNc ha hM hlam hN n ht hts i j

end BourgadeHuang.CMS
