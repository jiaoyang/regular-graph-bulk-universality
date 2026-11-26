import GeneralizedBulk.Gaussian.WeakCharacteristic

/-! Independent finite-vector products preserve actual weak convergence. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators

namespace GeneralizedBulk.Gaussian

def mergeVectors {α β : Type*} (xy : (α → ℝ) × (β → ℝ)) : Sum α β → ℝ :=
  Sum.elim xy.1 xy.2

theorem continuous_mergeVectors {α β : Type*} : Continuous (mergeVectors (α := α) (β := β)) := by
  apply continuous_pi
  intro i
  cases i with
  | inl a => exact (continuous_apply a).comp continuous_fst
  | inr b => exact (continuous_apply b).comp continuous_snd

theorem finiteLinearForm_merge {α β : Type*} [Fintype α] [Fintype β]
    (t : Sum α β → ℝ) (xy : (α → ℝ) × (β → ℝ)) :
    finiteLinearForm t (mergeVectors xy) =
      finiteLinearForm (t ∘ Sum.inl) xy.1 + finiteLinearForm (t ∘ Sum.inr) xy.2 := by
  simp only [finiteLinearForm, Fintype.sum_sum_type, mergeVectors, Sum.elim_inl,
    Sum.elim_inr, Function.comp_apply]

def vectorProductLaw {α β : Type*} (μ : Measure (α → ℝ)) (ν : Measure (β → ℝ)) :
    Measure (Sum α β → ℝ) := Measure.map mergeVectors (μ.prod ν)

instance {α β : Type*} [Fintype α] [Fintype β] (μ : Measure (α → ℝ)) (ν : Measure (β → ℝ))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : IsProbabilityMeasure (vectorProductLaw μ ν) :=
  MeasureTheory.isProbabilityMeasure_map continuous_mergeVectors.measurable.aemeasurable

theorem vectorProductLaw_characteristic {α β : Type*} [Fintype α] [Fintype β]
    (μ : Measure (α → ℝ)) (ν : Measure (β → ℝ)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (t : Sum α β → ℝ) :
    (∫ x, Complex.exp ((↑(finiteLinearForm t x) : ℂ) * Complex.I) ∂vectorProductLaw μ ν) =
      (∫ x, Complex.exp ((↑(finiteLinearForm (t ∘ Sum.inl) x) : ℂ) * Complex.I) ∂μ) *
      (∫ y, Complex.exp ((↑(finiteLinearForm (t ∘ Sum.inr) y) : ℂ) * Complex.I) ∂ν) := by
  have hmeas : AEStronglyMeasurable
      (fun x => Complex.exp ((↑(finiteLinearForm t x) : ℂ) * Complex.I)) (vectorProductLaw μ ν) :=
    (linearCharacteristic t).continuous.aestronglyMeasurable
  rw [vectorProductLaw, integral_map continuous_mergeVectors.measurable.aemeasurable hmeas]
  simp_rw [finiteLinearForm_merge, Complex.ofReal_add, add_mul, Complex.exp_add]
  exact integral_prod_mul
    (fun x : α → ℝ => Complex.exp ((↑(finiteLinearForm (t ∘ Sum.inl) x) : ℂ) * Complex.I))
    (fun y : β → ℝ => Complex.exp ((↑(finiteLinearForm (t ∘ Sum.inr) y) : ℂ) * Complex.I))

theorem mergeVectors_norm_fourth_le {α β : Type*} [Fintype α] [Fintype β]
    (xy : (α → ℝ) × (β → ℝ)) :
    ‖mergeVectors xy‖ ^ 4 ≤ ‖xy.1‖ ^ 4 + ‖xy.2‖ ^ 4 := by
  have hm : ‖mergeVectors xy‖ ≤ max ‖xy.1‖ ‖xy.2‖ := by
    apply (pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg _))).mpr
    intro i
    cases i with
    | inl a => exact (norm_le_pi_norm xy.1 a).trans (le_max_left _ _)
    | inr b => exact (norm_le_pi_norm xy.2 b).trans (le_max_right _ _)
  calc
    _ ≤ (max ‖xy.1‖ ‖xy.2‖) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) hm _
    _ ≤ _ := by
      rcases le_total ‖xy.1‖ ‖xy.2‖ with h | h
      · rw [max_eq_right h]
        linarith [show 0 ≤ ‖xy.1‖ ^ 4 by positivity]
      · rw [max_eq_left h]
        linarith [show 0 ≤ ‖xy.2‖ ^ 4 by positivity]

theorem vectorProductLaw_integrable_norm_fourth {α β : Type*} [Fintype α] [Fintype β]
    (μ : Measure (α → ℝ)) (ν : Measure (β → ℝ)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x => ‖x‖ ^ 4) μ) (hν : Integrable (fun x => ‖x‖ ^ 4) ν) :
    Integrable (fun x => ‖x‖ ^ 4) (vectorProductLaw μ ν) := by
  have h1 : Integrable (fun xy : (α → ℝ) × (β → ℝ) => ‖xy.1‖ ^ 4) (μ.prod ν) := by
    simpa only [mul_one] using hμ.mul_prod (integrable_const (1 : ℝ))
  have h2 : Integrable (fun xy : (α → ℝ) × (β → ℝ) => ‖xy.2‖ ^ 4) (μ.prod ν) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ)).mul_prod hν
  apply (integrable_map_measure (continuous_norm.pow 4).aestronglyMeasurable
    continuous_mergeVectors.measurable.aemeasurable).mpr
  apply (h1.add h2).mono' ((continuous_mergeVectors.norm.pow 4).measurable.aestronglyMeasurable)
  filter_upwards [] with xy
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mergeVectors_norm_fourth_le xy

theorem vectorProductLaw_norm_fourth_bound {α β : Type*} [Fintype α] [Fintype β]
    (μ : Measure (α → ℝ)) (ν : Measure (β → ℝ)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x => ‖x‖ ^ 4) μ) (hν : Integrable (fun x => ‖x‖ ^ 4) ν) :
    (∫ x, ‖x‖ ^ 4 ∂vectorProductLaw μ ν) ≤ (∫ x, ‖x‖ ^ 4 ∂μ) + ∫ y, ‖y‖ ^ 4 ∂ν := by
  have h1 : Integrable (fun xy : (α → ℝ) × (β → ℝ) => ‖xy.1‖ ^ 4) (μ.prod ν) := by
    simpa only [mul_one] using hμ.mul_prod (integrable_const (1 : ℝ))
  have h2 : Integrable (fun xy : (α → ℝ) × (β → ℝ) => ‖xy.2‖ ^ 4) (μ.prod ν) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ)).mul_prod hν
  have hm := vectorProductLaw_integrable_norm_fourth μ ν hμ hν
  have hm' := (integrable_map_measure (continuous_norm.pow 4).aestronglyMeasurable
    continuous_mergeVectors.measurable.aemeasurable).mp hm
  rw [vectorProductLaw, integral_map continuous_mergeVectors.measurable.aemeasurable
    (continuous_norm.pow 4).aestronglyMeasurable]
  calc
    _ ≤ ∫ xy : (α → ℝ) × (β → ℝ), ‖xy.1‖ ^ 4 + ‖xy.2‖ ^ 4 ∂μ.prod ν :=
      integral_mono hm' (h1.add h2) mergeVectors_norm_fourth_le
    _ = _ := by
      rw [integral_add h1 h2]
      have he1 := integral_prod_mul (μ := μ) (ν := ν) (fun x : α → ℝ => ‖x‖ ^ 4) (fun _ : β → ℝ => (1 : ℝ))
      have he2 := integral_prod_mul (μ := μ) (ν := ν) (fun _ : α → ℝ => (1 : ℝ)) (fun y : β → ℝ => ‖y‖ ^ 4)
      simpa only [mul_one, one_mul, integral_const, measureReal_univ_eq_one, one_smul] using congrArg₂ (· + ·) he1 he2

theorem vectorProductLaw_weakConverges {α β : Type*} [Fintype α] [Fintype β]
    (μ : ℕ → Measure (α → ℝ)) (ν : Measure (α → ℝ))
    (η : ℕ → Measure (β → ℝ)) (θ : Measure (β → ℝ))
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    [∀ n, IsProbabilityMeasure (η n)] [IsProbabilityMeasure θ]
    (hμ : External.WeakLawConverges μ ν) (hη : External.WeakLawConverges η θ)
    (hiμ : ∀ n, Integrable (fun x => ‖x‖ ^ 4) (μ n))
    (hiη : ∀ n, Integrable (fun x => ‖x‖ ^ 4) (η n))
    (M L : ℝ) (hM : ∀ n, (∫ x, ‖x‖ ^ 4 ∂μ n) ≤ M) (hL : ∀ n, (∫ x, ‖x‖ ^ 4 ∂η n) ≤ L) :
    External.WeakLawConverges (fun n => vectorProductLaw (μ n) (η n)) (vectorProductLaw ν θ) := by
  apply weakLaw_of_characteristic_of_norm_fourth _ _
    (fun n => vectorProductLaw_integrable_norm_fourth (μ n) (η n) (hiμ n) (hiη n)) (M + L)
    (fun n => (vectorProductLaw_norm_fourth_bound (μ n) (η n) (hiμ n) (hiη n)).trans
      (add_le_add (hM n) (hL n)))
  intro t
  simp_rw [vectorProductLaw_characteristic]
  exact (weakLaw_characteristic μ ν hμ (t ∘ Sum.inl)).mul
    (weakLaw_characteristic η θ hη (t ∘ Sum.inr))

end GeneralizedBulk.Gaussian
