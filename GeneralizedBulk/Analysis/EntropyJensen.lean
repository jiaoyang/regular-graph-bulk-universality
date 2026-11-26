import GeneralizedBulk.Entropy.LogSum

/-! The actual cellwise entropy gap and its symmetrized two-point bound. -/
noncomputable section
open MeasureTheory
namespace GeneralizedBulk.Analysis
open GeneralizedBulk.Entropy
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

theorem integral_log_le_log_integral (f : X → ℝ) (hpos : ∀ x, 0 < f x)
    (hf : Integrable f μ) (hlog : Integrable (fun x => Real.log (f x)) μ)
    (hmean : 0 < ∫ x, f x ∂μ) :
    (∫ x, Real.log (f x) ∂μ) ≤ Real.log (∫ x, f x ∂μ) := by
  let A := ∫ x, f x ∂μ
  have hh (x) : Real.log (f x) - Real.log A ≤ f x / A - 1 := by
    rw [← Real.log_div (ne_of_gt (hpos x)) (ne_of_gt hmean)]
    exact Real.log_le_sub_one_of_pos (div_pos (hpos x) hmean)
  have h := integral_mono (hlog.sub (integrable_const _)) ((hf.div_const A).sub (integrable_const 1)) hh
  simp only [Pi.sub_apply] at h
  rw [integral_sub hlog (integrable_const _), integral_sub (hf.div_const A) (integrable_const 1),
    integral_div, integral_const, integral_const] at h
  simp only [measureReal_univ_eq_one, smul_eq_mul, one_mul] at h
  change (∫ x, Real.log (f x) ∂μ) - Real.log A ≤ A / A - 1 at h
  rw [div_self (ne_of_gt hmean)] at h
  linarith

theorem entropy_gap_nonneg (f : X → ℝ) (hpos : ∀ x, 0 < f x)
    (hf : Integrable f μ) (hflog : Integrable (fun x => f x * Real.log (f x)) μ)
    (hmean : 0 < ∫ x, f x ∂μ) :
    0 ≤ (∫ x, f x * Real.log (f x) ∂μ) -
      (∫ x, f x ∂μ) * Real.log (∫ x, f x ∂μ) := by
  let A := ∫ x, f x ∂μ
  have hpoint (x) : 0 ≤ f x * Real.log (f x) - f x * Real.log A - f x + A := by
    have h := klIntegrand_nonneg (f x) A (hpos x) hmean
    unfold klIntegrand at h
    rw [Real.log_div (ne_of_gt (hpos x)) (ne_of_gt hmean)] at h
    nlinarith
  have hi : 0 ≤ ∫ x, f x * Real.log (f x) - f x * Real.log A - f x + A ∂μ :=
    integral_nonneg hpoint
  rw [integral_add (f := fun x => f x * Real.log (f x) - f x * Real.log A - f x)
      (g := fun _ => A) ((hflog.sub (hf.mul_const _)).sub hf) (integrable_const _),
    integral_sub (f := fun x => f x * Real.log (f x) - f x * Real.log A)
      (hflog.sub (hf.mul_const _)) hf,
    integral_sub hflog (hf.mul_const _), integral_mul_const, integral_const] at hi
  simp only [measureReal_univ_eq_one, smul_eq_mul, one_mul] at hi
  change 0 ≤ (∫ x, f x * Real.log (f x) ∂μ) - A * Real.log A - A + A at hi
  linarith

theorem entropy_gap_upper (f : X → ℝ) (hpos : ∀ x, 0 < f x)
    (hf : Integrable f μ) (hlog : Integrable (fun x => Real.log (f x)) μ)
    (hmean : 0 < ∫ x, f x ∂μ) :
    (∫ x, f x * Real.log (f x) ∂μ) -
      (∫ x, f x ∂μ) * Real.log (∫ x, f x ∂μ) ≤
    (∫ x, f x * Real.log (f x) ∂μ) -
      (∫ x, f x ∂μ) * ∫ x, Real.log (f x) ∂μ := by
  have h := mul_le_mul_of_nonneg_left (integral_log_le_log_integral μ f hpos hf hlog hmean) hmean.le
  linarith

theorem integral_symmetrized_entropy (f : X → ℝ)
    (hf : Integrable f μ) (hlog : Integrable (fun x => Real.log (f x)) μ)
    (hflog : Integrable (fun x => f x * Real.log (f x)) μ) :
    Integrable (fun z : X × X => (f z.1 - f z.2) * (Real.log (f z.1) - Real.log (f z.2))) (μ.prod μ) ∧
    (∫ z : X × X, (f z.1 - f z.2) * (Real.log (f z.1) - Real.log (f z.2)) ∂μ.prod μ) =
      2 * ((∫ x, f x * Real.log (f x) ∂μ) - (∫ x, f x ∂μ) * ∫ x, Real.log (f x) ∂μ) := by
  have h1 : Integrable (fun z : X × X => f z.1 * Real.log (f z.1)) (μ.prod μ) := by
    simpa only [mul_one] using hflog.prod_mul (integrable_const (1 : ℝ) (μ := μ))
  have h2 : Integrable (fun z : X × X => f z.2 * Real.log (f z.2)) (μ.prod μ) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ) (μ := μ)).prod_mul hflog
  have h3 := hf.prod_mul hlog
  have h4 := hlog.prod_mul hf
  have he (z : X × X) : (f z.1 - f z.2) * (Real.log (f z.1) - Real.log (f z.2)) =
      (f z.1 * Real.log (f z.1) + f z.2 * Real.log (f z.2)) -
        (f z.1 * Real.log (f z.2) + Real.log (f z.1) * f z.2) := by ring
  simp_rw [he]
  refine ⟨(h1.add h2).sub (h3.add h4), ?_⟩
  rw [integral_sub (f := fun z : X × X => f z.1 * Real.log (f z.1) + f z.2 * Real.log (f z.2))
    (g := fun z : X × X => f z.1 * Real.log (f z.2) + Real.log (f z.1) * f z.2) (h1.add h2) (h3.add h4),
    integral_add h1 h2, integral_add h3 h4,
    integral_fun_fst (fun x => f x * Real.log (f x)),
    integral_fun_snd (fun x => f x * Real.log (f x)),
    integral_prod_mul f (fun x => Real.log (f x)), integral_prod_mul (fun x => Real.log (f x)) f]
  simp only [measureReal_univ_eq_one, smul_eq_mul, one_mul]
  ring

theorem entropy_gap_symmetrized_bound (f : X → ℝ) (hpos : ∀ x, 0 < f x)
    (hf : Integrable f μ) (hlog : Integrable (fun x => Real.log (f x)) μ)
    (hflog : Integrable (fun x => f x * Real.log (f x)) μ) (hmean : 0 < ∫ x, f x ∂μ) :
    0 ≤ (∫ x, f x * Real.log (f x) ∂μ) -
      (∫ x, f x ∂μ) * Real.log (∫ x, f x ∂μ) ∧
    (∫ x, f x * Real.log (f x) ∂μ) - (∫ x, f x ∂μ) * Real.log (∫ x, f x ∂μ) ≤
      (∫ z : X × X, (f z.1 - f z.2) * (Real.log (f z.1) - Real.log (f z.2)) ∂μ.prod μ) / 2 := by
  refine ⟨entropy_gap_nonneg μ f hpos hf hflog hmean, ?_⟩
  rw [(integral_symmetrized_entropy μ f hf hlog hflog).2]
  linarith [entropy_gap_upper μ f hpos hf hlog hmean]

end GeneralizedBulk.Analysis
