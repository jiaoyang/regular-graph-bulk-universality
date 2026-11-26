import BourgadeHuang.FiniteSourceBounds
import BourgadeHuang.EntireRatioExpectation

/-! The true multipair characteristic observable has the deterministic bulk
normalization when its paired displacements are small relative to height. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang

theorem anchoredCharacteristicRatios_centered {q : ℕ} (s : AnchoredCountingState)
    (u v : Fin q → ℂ) (hu : ∀j, 0<(u j).im) (hv : ∀j, 0<(v j).im) :
    anchoredCharacteristicRatios s u v =
      Complex.exp (-(∑j, (u j-v j)*Complex.I)) *
        Complex.exp (∑j, compactCenteredSource ratioIntervalMeasure
          (fun t : RatioInterval => ratioPath (u j) (v j) t) (fun _ => -(u j-v j)) s) := by
  unfold anchoredCharacteristicRatios
  simp_rw [anchoredCharacteristicRatio_centered s (hu _) (hv _)]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, ← Complex.exp_sum]
  congr 2
  simp only [neg_mul, Finset.sum_neg_distrib]

/-- Quantitative normalization, including the empty product. -/
theorem expectedCharacteristicRatios_normalized_bound {q : ℕ}
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hh : ExactAnchoredHierarchy ν .two) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (u v : Fin q → ℂ) {η δ : ℝ} (hη : 0<η)
    (hu : ∀j, η≤(u j).im) (hv : ∀j, η≤(v j).im)
    (hδ : 0<δ) (hd : ∀j, ‖u j-v j‖≤δ*η) :
    Integrable (fun s => anchoredCharacteristicRatios s u v) ν ∧
      ‖Complex.exp (∑j, (u j-v j)*Complex.I)*
        (∫ s, anchoredCharacteristicRatios s u v ∂ν)-1‖ ≤
          δ*(64*(q:ℝ)^2+(q:ℝ)*Real.exp (((q:ℝ)*δ)^2/bulkExponentialScale)) := by
  by_cases hq : q=0
  · subst q
    simp [anchoredCharacteristicRatios,integrable_const]
  have hqp : 0<q := Nat.pos_of_ne_zero hq
  let γ := fun j => fun t : RatioInterval => ratioPath (u j) (v j) t
  let ρ := fun j => fun _t : RatioInterval => -(u j-v j)
  have hγ j : Continuous (γ j) := (continuous_ratioPath _ _).comp continuous_subtype_val
  have hρ j : Continuous (ρ j) := continuous_const
  have hup : ∀j t, 0<(γ j t).im := fun j t => hη.trans_le (ratioPath_im_lower (hu j) (hv j) t)
  have hr : ∀j t, ‖ρ j t‖≤δ*(γ j t).im := by
    intro j t
    dsimp [ρ,γ]
    rw [norm_neg]
    exact (hd j).trans (mul_le_mul_of_nonneg_left (ratioPath_im_lower (hu j) (hv j) t) hδ.le)
  obtain ⟨hi,hb⟩ := finiteCompactCenteredSource_exponential_close hqp ratioIntervalMeasure
    γ ρ hγ hρ hup ν hh ha he hδ hr
  have heq s := anchoredCharacteristicRatios_centered s u v
    (fun j => hη.trans_le (hu j)) (fun j => hη.trans_le (hv j))
  have hRi : Integrable (fun s => anchoredCharacteristicRatios s u v) ν := by
    simpa only [heq,γ,ρ] using hi.const_mul (Complex.exp (-(∑j, (u j-v j)*Complex.I)))
  refine ⟨hRi, ?_⟩
  simp only [heq,integral_const_mul]
  rw [← mul_assoc,← Complex.exp_add,add_neg_cancel,Complex.exp_zero,one_mul]
  exact hb

/-- The same normalization is proved for the actual entire ratio expectation. -/
theorem expectedEntireCharacteristicRatios_normalized_bound {q : ℕ}
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hh : ExactAnchoredHierarchy ν .two) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (u v : Fin q → ℂ) {η δ : ℝ} (hη : 0<η)
    (hu : ∀j, η≤(u j).im) (hv : ∀j, η≤(v j).im)
    (hδ : 0<δ) (hd : ∀j, ‖u j-v j‖≤δ*η) :
    ‖Complex.exp (∑j, (u j-v j)*Complex.I)*expectedEntireCharacteristicRatios ν u v-1‖ ≤
      δ*(64*(q:ℝ)^2+(q:ℝ)*Real.exp (((q:ℝ)*δ)^2/bulkExponentialScale)) := by
  have heq s := entireCharacteristicRatios_eq_anchored s u v
    (fun j => Or.inl ⟨hη.trans_le (hu j),hη.trans_le (hv j)⟩)
  simpa only [expectedEntireCharacteristicRatios,heq] using
    (expectedCharacteristicRatios_normalized_bound ν hh ha he u v hη hu hv hδ hd).2

/-- A filter-level normalization theorem with the geometric smallness
conditions verified pointwise, rather than an assumed observable limit. -/
theorem tendsto_expectedEntireCharacteristicRatios_normalized
    {A : Type*} {l : Filter A} {q : ℕ}
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hh : ExactAnchoredHierarchy ν .two) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (u v : A → Fin q → ℂ) (η δ : A → ℝ) (hδ : Tendsto δ l (𝓝 0))
    (hgeom : ∀ᶠ t in l, 0<η t ∧ 0<δ t ∧
      (∀j, η t≤(u t j).im) ∧ (∀j, η t≤(v t j).im) ∧
      ∀j, ‖u t j-v t j‖≤δ t*η t) :
    Tendsto (fun t => Complex.exp (∑j, (u t j-v t j)*Complex.I)*
      expectedEntireCharacteristicRatios ν (u t) (v t)) l (𝓝 1) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hb : Tendsto (fun t => δ t*(64*(q:ℝ)^2+
      (q:ℝ)*Real.exp (((q:ℝ)*δ t)^2/bulkExponentialScale))) l (𝓝 0) := by
    have hc : Continuous (fun r : ℝ => r*(64*(q:ℝ)^2+
        (q:ℝ)*Real.exp (((q:ℝ)*r)^2/bulkExponentialScale))) := by fun_prop
    simpa using hc.continuousAt.tendsto.comp hδ
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hb
  filter_upwards [hgeom] with t ht
  exact expectedEntireCharacteristicRatios_normalized_bound ν hh ha he (u t) (v t)
    ht.1 ht.2.2.1 ht.2.2.2.1 ht.2.1 ht.2.2.2.2

end BourgadeHuang
