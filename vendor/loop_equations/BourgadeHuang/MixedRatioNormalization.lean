import BourgadeHuang.FiniteObservableBounds
import BourgadeHuang.MultipairSourceAsymptotics

/-! Quantitative normalization for mixed upper and lower half-plane blocks.
Conjugation is applied separately to each source; their joint law is retained. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang

theorem finiteReflectedCompactSource_exponential_close
    {T : Type*} [TopologicalSpace T] [TopologicalSpace.MetrizableSpace T]
    [SecondCountableTopology T] [CompactSpace T] [MeasurableSpace T] [BorelSpace T]
    {q : ℕ} (hq : 0<q) (κ : Measure T) [IsProbabilityMeasure κ]
    (ε : Fin q → Bool) (γ ρ : Fin q → T → ℂ)
    (hγ : ∀j, Continuous (γ j)) (hρ : ∀j, Continuous (ρ j)) (hup : ∀j t, 0<(γ j t).im)
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hh : ExactAnchoredHierarchy ν .two) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    {δ : ℝ} (hδ : 0<δ) (hb : ∀j t, ‖ρ j t‖≤δ*(γ j t).im) :
    Integrable (fun s => Complex.exp (∑j, reflectComplex (ε j)
      (compactCenteredSource κ (γ j) (ρ j) s))) ν ∧
    ‖(∫ s, Complex.exp (∑j, reflectComplex (ε j)
      (compactCenteredSource κ (γ j) (ρ j) s)) ∂ν)-1‖ ≤
      δ*(64*(q:ℝ)^2+(q:ℝ)*Real.exp (((q:ℝ)*δ)^2/bulkExponentialScale)) := by
  let X := fun j s => reflectComplex (ε j) (compactCenteredSource κ (γ j) (ρ j) s)
  have hm j : Measurable (X j) := (continuous_reflectComplex (ε j)).measurable.comp
    (measurable_compactCenteredSource κ (γ j) (ρ j) (hγ j) (hρ j) (hup j))
  have h2 j := compactCenteredSource_second_moment κ (γ j) (ρ j) (hγ j) (hρ j) (hup j)
    ν hh ha he hδ.le (hb j)
  have h2i j : Integrable (fun s => ‖X j s‖^2) ν := by
    simpa only [X,norm_reflectComplex] using (h2 j).1
  have h2b j : (∫s, ‖X j s‖^2 ∂ν)≤128*δ^2 := by
    simpa only [X,norm_reflectComplex] using (h2 j).2
  obtain ⟨hXi2,hXb2⟩ := finite_sum_second_moment_bound ν X hm h2i (128*δ^2) h2b
  have hE j := compactCenteredSource_exp_bound κ (γ j) (ρ j) (hγ j) (hρ j) (hup j)
    ν hh ha he hδ.le (show 0≤2*(q:ℝ) by positivity) (hb j)
  have hEi j : Integrable (fun s => Real.exp (2*(q:ℝ)*‖X j s‖)) ν := by
    simpa only [X,norm_reflectComplex] using (hE j).1
  have hEb j : (∫s, Real.exp (2*(q:ℝ)*‖X j s‖) ∂ν)≤
      2*Real.exp ((2*(q:ℝ)*δ)^2/(4*bulkExponentialScale)) := by
    simpa only [X,norm_reflectComplex] using (hE j).2
  obtain ⟨hXiE,hXbE⟩ := finite_sum_exp_moment_bound hq ν X hm (by norm_num : (0:ℝ)≤2)
    hEi _ hEb
  obtain ⟨hi,hb'⟩ := exponential_expectation_close_of_second_moment ν
    (fun s => ∑j, X j s) (Finset.measurable_sum _ (fun j _ => hm j)) hXi2 hXiE hδ
  refine ⟨hi,hb'.trans ?_⟩
  calc
    _ ≤ ((q:ℝ)^2*(128*δ^2))/(2*δ)+(δ/2)*
        ((q:ℝ)*(2*Real.exp ((2*(q:ℝ)*δ)^2/(4*bulkExponentialScale)))) :=
      add_le_add (div_le_div_of_nonneg_right hXb2 (by positivity))
        (mul_le_mul_of_nonneg_left hXbE (by positivity))
    _ = _ := by
      have heq : (2*(q:ℝ)*δ)^2/(4*bulkExponentialScale)=
          ((q:ℝ)*δ)^2/bulkExponentialScale := by ring
      rw [heq]
      field_simp
      ring

def signedRatioPhase (upper : Bool) (u v : ℂ) : ℂ :=
  if upper then (u-v)*Complex.I else -((u-v)*Complex.I)

theorem anchoredCharacteristicRatio_signed_centered (s : AnchoredCountingState)
    (upper : Bool) {u v : ℂ}
    (hu : 0<(reflectComplex upper u).im) (hv : 0<(reflectComplex upper v).im) :
    anchoredCharacteristicRatio s u v = Complex.exp (-signedRatioPhase upper u v)*
      Complex.exp (reflectComplex upper (compactCenteredSource ratioIntervalMeasure
        (fun t : RatioInterval => ratioPath (reflectComplex upper u) (reflectComplex upper v) t)
        (fun _ => -(reflectComplex upper u-reflectComplex upper v)) s)) := by
  cases upper with
  | true => simpa only [reflectComplex,signedRatioPhase,if_true,neg_mul] using
      anchoredCharacteristicRatio_centered s hu hv
  | false =>
    have h := congrArg (starRingEnd ℂ) (anchoredCharacteristicRatio_centered s hu hv)
    simp only [reflectComplex,Bool.false_eq_true,if_false,anchoredCharacteristicRatio_conj,
      Complex.conj_conj,map_mul,← Complex.exp_conj,map_neg,map_sub,Complex.conj_I] at h
    simpa only [reflectComplex,Bool.false_eq_true,if_false,signedRatioPhase,neg_neg,neg_mul,mul_neg,neg_neg] using h

@[simp] theorem reflectComplex_sub (upper : Bool) (u v : ℂ) :
    reflectComplex upper (u-v) = reflectComplex upper u-reflectComplex upper v := by
  cases upper <;> simp [reflectComplex]

theorem expectedEntireCharacteristicRatios_signed_normalized_bound {q : ℕ}
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hh : ExactAnchoredHierarchy ν .two) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (ε : Fin q → Bool) (u v : Fin q → ℂ) {η δ : ℝ} (hη : 0<η)
    (hu : ∀j, η≤(reflectComplex (ε j) (u j)).im)
    (hv : ∀j, η≤(reflectComplex (ε j) (v j)).im)
    (hδ : 0<δ) (hd : ∀j, ‖u j-v j‖≤δ*η) :
    ‖Complex.exp (∑j, signedRatioPhase (ε j) (u j) (v j))*
      expectedEntireCharacteristicRatios ν u v-1‖ ≤
      δ*(64*(q:ℝ)^2+(q:ℝ)*Real.exp (((q:ℝ)*δ)^2/bulkExponentialScale)) := by
  by_cases hq : q=0
  · subst q
    simp [expectedEntireCharacteristicRatios,entireCharacteristicRatios]
  have hqp : 0<q := Nat.pos_of_ne_zero hq
  let U := fun j => reflectComplex (ε j) (u j)
  let V := fun j => reflectComplex (ε j) (v j)
  let γ := fun j => fun t : RatioInterval => ratioPath (U j) (V j) t
  let ρ := fun j => fun _t : RatioInterval => -(U j-V j)
  have hγ j : Continuous (γ j) := (continuous_ratioPath _ _).comp continuous_subtype_val
  have hρ j : Continuous (ρ j) := continuous_const
  have hup : ∀j t, 0<(γ j t).im := fun j t => hη.trans_le (ratioPath_im_lower (hu j) (hv j) t)
  have hr : ∀j t, ‖ρ j t‖≤δ*(γ j t).im := by
    intro j t
    dsimp [ρ,γ,U,V]
    rw [norm_neg,← reflectComplex_sub,norm_reflectComplex]
    exact (hd j).trans (mul_le_mul_of_nonneg_left (ratioPath_im_lower (hu j) (hv j) t) hδ.le)
  obtain ⟨_,hb⟩ := finiteReflectedCompactSource_exponential_close hqp ratioIntervalMeasure
    ε γ ρ hγ hρ hup ν hh ha he hδ hr
  have huv j : SameOpenHalfPlane (u j) (v j) := by
    have huj := hη.trans_le (hu j)
    have hvj := hη.trans_le (hv j)
    cases hε : ε j with
    | true => exact Or.inl (by simpa [reflectComplex,hε] using And.intro huj hvj)
    | false => exact Or.inr (by simpa [reflectComplex,hε] using And.intro huj hvj)
  have heq s : entireCharacteristicRatios s u v =
      Complex.exp (-(∑j, signedRatioPhase (ε j) (u j) (v j)))*
        Complex.exp (∑j, reflectComplex (ε j) (compactCenteredSource ratioIntervalMeasure (γ j) (ρ j) s)) := by
    rw [entireCharacteristicRatios_eq_anchored s u v huv]
    unfold anchoredCharacteristicRatios
    simp_rw [anchoredCharacteristicRatio_signed_centered s _
      (hη.trans_le (hu _)) (hη.trans_le (hv _))]
    rw [Finset.prod_mul_distrib,← Complex.exp_sum,← Complex.exp_sum,Finset.sum_neg_distrib]
  simp only [expectedEntireCharacteristicRatios,heq,integral_const_mul]
  rw [← mul_assoc,← Complex.exp_add,add_neg_cancel,Complex.exp_zero,one_mul]
  exact hb

/-- Mixed-sign normalization along any geometry with vanishing relative
pair displacement. -/
theorem tendsto_expectedEntireCharacteristicRatios_signed_normalized
    {A : Type*} {l : Filter A} {q : ℕ}
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hh : ExactAnchoredHierarchy ν .two) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (ε : Fin q → Bool) (u v : A → Fin q → ℂ) (η δ : A → ℝ)
    (hδ : Tendsto δ l (𝓝 0))
    (hgeom : ∀ᶠ t in l, 0<η t ∧ 0<δ t ∧
      (∀j, η t≤(reflectComplex (ε j) (u t j)).im) ∧
      (∀j, η t≤(reflectComplex (ε j) (v t j)).im) ∧
      ∀j, ‖u t j-v t j‖≤δ t*η t) :
    Tendsto (fun t => Complex.exp (∑j, signedRatioPhase (ε j) (u t j) (v t j))*
      expectedEntireCharacteristicRatios ν (u t) (v t)) l (𝓝 1) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hb : Tendsto (fun t => δ t*(64*(q:ℝ)^2+
      (q:ℝ)*Real.exp (((q:ℝ)*δ t)^2/bulkExponentialScale))) l (𝓝 0) := by
    have hc : Continuous (fun r : ℝ => r*(64*(q:ℝ)^2+
        (q:ℝ)*Real.exp (((q:ℝ)*r)^2/bulkExponentialScale))) := by fun_prop
    simpa using hc.continuousAt.tendsto.comp hδ
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hb
  filter_upwards [hgeom] with t ht
  exact expectedEntireCharacteristicRatios_signed_normalized_bound ν hh ha he ε (u t) (v t)
    ht.1 ht.2.2.1 ht.2.2.2.1 ht.2.1 ht.2.2.2.2

end BourgadeHuang
