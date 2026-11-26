import BourgadeHuang.BulkCompactSources
import BourgadeHuang.OrthogonalBulkExponential

/-! Actual orthogonal compact source bounds with a universal centered scale. -/
noncomputable section
open scoped Topology
open MeasureTheory Filter
namespace BourgadeHuang
variable {T : Type*} [TopologicalSpace T] [TopologicalSpace.MetrizableSpace T] [SecondCountableTopology T]
  [CompactSpace T] [MeasurableSpace T] [BorelSpace T]

/-- An explicit uniform exponential bound in terms of the integrated source's
relative size. The measure on parameters is a probability measure. -/
theorem orthogonal_compactCenteredSource_exp_bound
    (κ : Measure T) [IsProbabilityMeasure κ]
    (γ ρ : T → ℂ) (hγ : Continuous γ) (hρ : Continuous ρ) (hup : ∀ t, 0<(γ t).im)
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hh : ExactAnchoredHierarchy ν .one) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    {δ L : ℝ} (_hδ : 0≤δ) (hL : 0≤L) (hρδ : ∀ t, ‖ρ t‖ ≤ δ*(γ t).im) :
    Integrable (fun s => Real.exp (L*‖compactCenteredSource κ γ ρ s‖)) ν ∧
      (∫ s, Real.exp (L*‖compactCenteredSource κ γ ρ s‖) ∂ν) ≤
        2*Real.exp ((L*δ)^2/(4*orthogonalBulkExponentialScale)) := by
  let F := fun t => fun s : AnchoredCountingState => ρ t*(anchoredNevanlinna s (γ t)-Complex.I)
  let G := fun t => fun s : AnchoredCountingState => Real.exp (L*‖F t s‖)
  let C := 2*Real.exp ((L*δ)^2/(4*orthogonalBulkExponentialScale))
  have hFm : Measurable (Function.uncurry F) := measurable_centered_source_uncurry γ ρ hγ hρ hup
  have hGm : StronglyMeasurable (Function.uncurry G) :=
    (Real.continuous_exp.measurable.comp (measurable_const.mul hFm.norm)).stronglyMeasurable
  have hGi (t : T) : Integrable (G t) ν ∧ (∫ s, G t s ∂ν) ≤ C := by
    let l := L*‖ρ t‖/(γ t).im
    have hln : 0≤l := div_nonneg (mul_nonneg hL (norm_nonneg _)) (hup t).le
    have hld : l≤L*δ := by
      apply (div_le_iff₀ (hup t)).mpr
      have ht := mul_le_mul_of_nonneg_left (hρδ t) hL
      simpa only [mul_assoc] using ht
    have heq (s : AnchoredCountingState) : G t s =
        Real.exp (l*((γ t).im*‖anchoredNevanlinna s (γ t)-Complex.I‖)) := by
      dsimp [G,F,l]
      rw [norm_mul]
      congr 1
      field_simp [(hup t).ne']
      ring
    obtain ⟨hi,hb⟩ := orthogonal_bulk_centered_exp_linear ν hh ha he (hup t) l
    refine ⟨by convert hi using 1; exact funext heq, ?_⟩
    simp only [heq]
    apply hb.trans
    dsimp [C]
    gcongr
    exact mul_nonneg (by norm_num) orthogonalBulkExponentialScale_pos.le
  have hGp : Integrable (Function.uncurry G) (κ.prod ν) :=
    integrable_prod_of_uniform_fiber_norm κ ν hGm (fun t => (hGi t).1) C (fun t => by
      simpa only [G,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using (hGi t).2)
  have hJ (s : AnchoredCountingState) : Real.exp (L*‖compactCenteredSource κ γ ρ s‖) ≤ ∫ t, G t s ∂κ := by
    have hc := continuous_centered_source_parameter γ ρ hγ hρ hup s
    have hi : Integrable (fun t => L*‖F t s‖) κ :=
      (continuous_const.mul hc.norm).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hei : Integrable (fun t => G t s) κ :=
      (Real.continuous_exp.comp (continuous_const.mul hc.norm)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    calc
      _ ≤ Real.exp (∫ t, L*‖F t s‖ ∂κ) := by
        apply Real.exp_le_exp.mpr
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hL
      _ ≤ _ := exp_integral_le_integral_exp κ hi hei
  have htarget : Integrable (fun s => Real.exp (L*‖compactCenteredSource κ γ ρ s‖)) ν := by
    apply hGp.integral_prod_right.mono'
      (Real.continuous_exp.measurable.comp (measurable_const.mul
        (measurable_compactCenteredSource κ γ ρ hγ hρ hup).norm)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun s => by
      dsimp only [Function.comp_apply,Function.uncurry_apply_pair]
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact hJ s
  refine ⟨htarget, ?_⟩
  calc
    _ ≤ ∫ s, ∫ t, G t s ∂κ ∂ν := integral_mono htarget hGp.integral_prod_right hJ
    _ = ∫ t, ∫ s, G t s ∂ν ∂κ := (integral_integral_swap hGp).symm
    _ ≤ ∫ _ : T, C ∂κ := integral_mono hGp.integral_prod_left (integrable_const C) (fun t => (hGi t).2)
    _ = _ := by simp [C]


/-- The actual integrated source has a uniform second-moment bound. -/
theorem orthogonal_compactCenteredSource_second_moment
    (κ : Measure T) [IsProbabilityMeasure κ]
    (γ ρ : T → ℂ) (hγ : Continuous γ) (hρ : Continuous ρ) (hup : ∀ t, 0<(γ t).im)
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hh : ExactAnchoredHierarchy ν .one) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    {δ : ℝ} (_hδ : 0≤δ) (hρδ : ∀ t, ‖ρ t‖ ≤ δ*(γ t).im) :
    Integrable (fun s => ‖compactCenteredSource κ γ ρ s‖^2) ν ∧
      (∫ s, ‖compactCenteredSource κ γ ρ s‖^2 ∂ν) ≤ 384*δ^2 := by
  let F := fun t => fun s : AnchoredCountingState => ρ t*(anchoredNevanlinna s (γ t)-Complex.I)
  let G := fun t => fun s : AnchoredCountingState => ‖F t s‖^2
  have hFm : Measurable (Function.uncurry F) := measurable_centered_source_uncurry γ ρ hγ hρ hup
  have hGm : StronglyMeasurable (Function.uncurry G) := (hFm.norm.pow_const 2).stronglyMeasurable
  have hGi (t : T) : Integrable (G t) ν ∧ (∫ s, G t s ∂ν) ≤ 384*δ^2 := by
    have hi0 := (orthogonal_bulk_localLaw_even_moment ν hh ha he (hup t) 0).1
    have hb0 := (orthogonal_bulk_localLaw_even_moment ν hh ha he (hup t) 0).2
    norm_num only [Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul,pow_one,mul_one] at hi0 hb0
    have hnorm (s : AnchoredCountingState) : G t s = ‖ρ t‖^2*‖anchoredNevanlinna s (γ t)-Complex.I‖^2 := by
      simp only [G,F,norm_mul,mul_pow]
    refine ⟨by convert hi0.const_mul (‖ρ t‖^2) using 1; exact funext hnorm, ?_⟩
    simp only [hnorm,integral_const_mul]
    apply (mul_le_mul_of_nonneg_left hb0 (sq_nonneg _)).trans
    have ht := pow_le_pow_left₀ (norm_nonneg _) (hρδ t) 2
    rw [mul_pow] at ht
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (sq_pos_of_pos (hup t))).mpr
    nlinarith only [ht]
  have hGp : Integrable (Function.uncurry G) (κ.prod ν) :=
    integrable_prod_of_uniform_fiber_norm κ ν hGm (fun t => (hGi t).1) (384*δ^2) (fun t => by
      simpa only [G,Real.norm_eq_abs,abs_pow,abs_norm] using (hGi t).2)
  have hJ (s : AnchoredCountingState) : ‖compactCenteredSource κ γ ρ s‖^2 ≤ ∫ t, G t s ∂κ := by
    have hc := continuous_centered_source_parameter γ ρ hγ hρ hup s
    have hi : Integrable (fun t => ‖F t s‖) κ :=
      hc.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hi2 : Integrable (fun t => ‖F t s‖^2) κ :=
      (hc.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hcs := integral_le_sqrt_integral_sq κ hi hi2 (fun t => norm_nonneg _)
    have hn := (norm_integral_le_integral_norm (μ := κ) (fun t => F t s)).trans hcs
    have ht := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr hn
    rw [Real.sq_sqrt (integral_nonneg (fun t => sq_nonneg _))] at ht
    exact ht
  have htarget : Integrable (fun s => ‖compactCenteredSource κ γ ρ s‖^2) ν := by
    apply hGp.integral_prod_right.mono'
      ((measurable_compactCenteredSource κ γ ρ hγ hρ hup).norm.pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs,abs_pow,abs_norm]
      exact hJ s
  refine ⟨htarget, ?_⟩
  calc
    _ ≤ ∫ s, ∫ t, G t s ∂κ ∂ν := integral_mono htarget hGp.integral_prod_right hJ
    _ = ∫ t, ∫ s, G t s ∂ν ∂κ := (integral_integral_swap hGp).symm
    _ ≤ ∫ _ : T, 384*δ^2 ∂κ := integral_mono hGp.integral_prod_left (integrable_const _) (fun t => (hGi t).2)
    _ = _ := by simp

end BourgadeHuang
