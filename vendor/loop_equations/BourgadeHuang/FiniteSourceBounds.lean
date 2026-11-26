import BourgadeHuang.BulkSourceAsymptotics

/-! Finite families of genuine centered sources.  The estimates are derived
from the scalar bounds, with constants explicit in the number of sources. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang

theorem norm_sum_sq_le_card_sum_sq {q : ℕ} (x : Fin q → ℂ) :
    ‖∑ j, x j‖^2 ≤ (q:ℝ)*∑ j, ‖x j‖^2 := by
  have hn := norm_sum_le Finset.univ x
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : Fin q => (1:ℝ)) (fun j => ‖x j‖)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hc
  exact (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))).mpr hn |>.trans hc

theorem exp_norm_sum_le_sum_exp {q : ℕ} (hq : 0<q) (x : Fin q → ℂ)
    {L : ℝ} (hL : 0≤L) :
    Real.exp (L*‖∑ j, x j‖) ≤ ∑ j, Real.exp (L*(q:ℝ)*‖x j‖) := by
  have hne : (Finset.univ : Finset (Fin q)).Nonempty := ⟨⟨0,hq⟩,Finset.mem_univ _⟩
  obtain ⟨k,hk,hmax⟩ := Finset.exists_max_image Finset.univ (fun j => ‖x j‖) hne
  have hs := Finset.sum_le_card_nsmul Finset.univ (fun j => ‖x j‖) ‖x k‖ hmax
  simp only [Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  calc
    _ ≤ Real.exp (L*(q:ℝ)*‖x k‖) := by
      apply Real.exp_le_exp.mpr
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        ((norm_sum_le Finset.univ x).trans hs) hL
    _ ≤ _ := Finset.single_le_sum (f := fun j : Fin q => Real.exp (L*(q:ℝ)*‖x j‖))
      (fun j _ => (Real.exp_pos _).le) hk

section CompactSources
variable {T : Type*} [TopologicalSpace T] [TopologicalSpace.MetrizableSpace T]
  [SecondCountableTopology T] [CompactSpace T] [MeasurableSpace T] [BorelSpace T]

theorem finiteCompactCenteredSource_second_moment
    {q : ℕ} (κ : Measure T) [IsProbabilityMeasure κ]
    (γ ρ : Fin q → T → ℂ) (hγ : ∀ j, Continuous (γ j)) (hρ : ∀ j, Continuous (ρ j))
    (hup : ∀ j t, 0<(γ j t).im)
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hh : ExactAnchoredHierarchy ν .two) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    {δ : ℝ} (hδ : 0≤δ) (hb : ∀ j t, ‖ρ j t‖≤δ*(γ j t).im) :
    Integrable (fun s => ‖∑ j, compactCenteredSource κ (γ j) (ρ j) s‖^2) ν ∧
      (∫ s, ‖∑ j, compactCenteredSource κ (γ j) (ρ j) s‖^2 ∂ν) ≤ 128*((q:ℝ)*δ)^2 := by
  let X := fun j => compactCenteredSource κ (γ j) (ρ j)
  have hi j := compactCenteredSource_second_moment κ (γ j) (ρ j) (hγ j) (hρ j)
    (hup j) ν hh ha he hδ (hb j)
  have hm : Measurable (fun s => ‖∑ j, X j s‖^2) := by
    apply Measurable.pow_const
    apply Measurable.norm
    exact Finset.measurable_sum Finset.univ (fun j _ =>
      measurable_compactCenteredSource κ (γ j) (ρ j) (hγ j) (hρ j) (hup j))
  have hdom : Integrable (fun s => (q:ℝ)*∑ j, ‖X j s‖^2) ν :=
    (integrable_finset_sum Finset.univ (fun j _ => (hi j).1)).const_mul _
  have hpoint s := norm_sum_sq_le_card_sum_sq (fun j => X j s)
  have hXi : Integrable (fun s => ‖∑ j, X j s‖^2) ν :=
    hdom.mono' hm.aestronglyMeasurable (Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpoint s)
  refine ⟨hXi, ?_⟩
  calc
    _ ≤ ∫ s, (q:ℝ)*∑ j, ‖X j s‖^2 ∂ν := integral_mono hXi hdom hpoint
    _ = (q:ℝ)*∑ j, ∫ s, ‖X j s‖^2 ∂ν := by
      rw [integral_const_mul,integral_finset_sum _ (fun j _ => (hi j).1)]
    _ ≤ (q:ℝ)*∑ _j : Fin q, 128*δ^2 := by
      gcongr with j
      exact (hi j).2
    _ = _ := by simp; ring

theorem finiteCompactCenteredSource_exp_bound
    {q : ℕ} (hq : 0<q) (κ : Measure T) [IsProbabilityMeasure κ]
    (γ ρ : Fin q → T → ℂ) (hγ : ∀ j, Continuous (γ j)) (hρ : ∀ j, Continuous (ρ j))
    (hup : ∀ j t, 0<(γ j t).im)
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hh : ExactAnchoredHierarchy ν .two) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    {δ L : ℝ} (hδ : 0≤δ) (hL : 0≤L) (hb : ∀ j t, ‖ρ j t‖≤δ*(γ j t).im) :
    Integrable (fun s => Real.exp (L*‖∑ j, compactCenteredSource κ (γ j) (ρ j) s‖)) ν ∧
      (∫ s, Real.exp (L*‖∑ j, compactCenteredSource κ (γ j) (ρ j) s‖) ∂ν) ≤
        2*(q:ℝ)*Real.exp ((L*(q:ℝ)*δ)^2/(4*bulkExponentialScale)) := by
  let X := fun j => compactCenteredSource κ (γ j) (ρ j)
  have hi j := compactCenteredSource_exp_bound κ (γ j) (ρ j) (hγ j) (hρ j)
    (hup j) ν hh ha he hδ (mul_nonneg hL (Nat.cast_nonneg q)) (hb j)
  have hm : Measurable (fun s => Real.exp (L*‖∑ j, X j s‖)) := by
    apply Measurable.exp
    apply Measurable.const_mul
    apply Measurable.norm
    exact Finset.measurable_sum Finset.univ (fun j _ =>
      measurable_compactCenteredSource κ (γ j) (ρ j) (hγ j) (hρ j) (hup j))
  have hdom : Integrable (fun s => ∑ j, Real.exp (L*(q:ℝ)*‖X j s‖)) ν :=
    integrable_finset_sum Finset.univ (fun j _ => (hi j).1)
  have hpoint s := exp_norm_sum_le_sum_exp hq (fun j => X j s) hL
  have hXi : Integrable (fun s => Real.exp (L*‖∑ j, X j s‖)) ν :=
    hdom.mono' hm.aestronglyMeasurable (Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact hpoint s)
  refine ⟨hXi, ?_⟩
  calc
    _ ≤ ∫ s, ∑ j, Real.exp (L*(q:ℝ)*‖X j s‖) ∂ν := integral_mono hXi hdom hpoint
    _ = ∑ j, ∫ s, Real.exp (L*(q:ℝ)*‖X j s‖) ∂ν :=
      integral_finset_sum _ (fun j _ => (hi j).1)
    _ ≤ ∑ _j : Fin q, 2*Real.exp ((L*(q:ℝ)*δ)^2/(4*bulkExponentialScale)) :=
      Finset.sum_le_sum (fun j _ => (hi j).2)
    _ = _ := by simp; ring

/-- Every fixed finite product has the required quantitative normalization;
no independence between its sources is used. -/
theorem finiteCompactCenteredSource_exponential_close
    {q : ℕ} (hq : 0<q) (κ : Measure T) [IsProbabilityMeasure κ]
    (γ ρ : Fin q → T → ℂ) (hγ : ∀ j, Continuous (γ j)) (hρ : ∀ j, Continuous (ρ j))
    (hup : ∀ j t, 0<(γ j t).im)
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hh : ExactAnchoredHierarchy ν .two) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    {δ : ℝ} (hδ : 0<δ) (hb : ∀ j t, ‖ρ j t‖≤δ*(γ j t).im) :
    Integrable (fun s => Complex.exp (∑ j, compactCenteredSource κ (γ j) (ρ j) s)) ν ∧
      ‖(∫ s, Complex.exp (∑ j, compactCenteredSource κ (γ j) (ρ j) s) ∂ν)-1‖ ≤
        δ*(64*(q:ℝ)^2+(q:ℝ)*Real.exp (((q:ℝ)*δ)^2/bulkExponentialScale)) := by
  obtain ⟨h2i,h2b⟩ := finiteCompactCenteredSource_second_moment κ γ ρ hγ hρ hup ν hh ha he hδ.le hb
  obtain ⟨hei,heb⟩ := finiteCompactCenteredSource_exp_bound hq κ γ ρ hγ hρ hup ν hh ha he hδ.le
    (show (0:ℝ)≤2 by norm_num) hb
  have hm := Finset.measurable_sum Finset.univ (fun j _ =>
    measurable_compactCenteredSource κ (γ j) (ρ j) (hγ j) (hρ j) (hup j))
  obtain ⟨hi,hb'⟩ := exponential_expectation_close_of_second_moment ν
    (fun s => ∑ j, compactCenteredSource κ (γ j) (ρ j) s) hm h2i hei hδ
  refine ⟨hi,hb'.trans ?_⟩
  calc
    _ ≤ (128*((q:ℝ)*δ)^2)/(2*δ)+(δ/2)*
        (2*(q:ℝ)*Real.exp ((2*(q:ℝ)*δ)^2/(4*bulkExponentialScale))) :=
      add_le_add (div_le_div_of_nonneg_right h2b (by positivity))
        (mul_le_mul_of_nonneg_left heb (by positivity))
    _ = _ := by
      have heq : (2*(q:ℝ)*δ)^2/(4*bulkExponentialScale)=
          ((q:ℝ)*δ)^2/bulkExponentialScale := by ring
      rw [heq]
      field_simp
      ring

end CompactSources
end BourgadeHuang
