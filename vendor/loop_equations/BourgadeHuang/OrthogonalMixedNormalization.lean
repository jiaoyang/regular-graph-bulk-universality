import BourgadeHuang.OrthogonalCompactSources
import BourgadeHuang.MixedRatioNormalization
import BourgadeHuang.OrthogonalRatioAnalytic

/-! Small relative sources normalize actual orthogonal characteristic ratios. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang

theorem orthogonal_finiteReflectedCompactSource_exponential_close
    {T : Type*} [TopologicalSpace T] [TopologicalSpace.MetrizableSpace T]
    [SecondCountableTopology T] [CompactSpace T] [MeasurableSpace T] [BorelSpace T]
    {q : ℕ} (hq : 0<q) (κ : Measure T) [IsProbabilityMeasure κ]
    (ε : Fin q → Bool) (γ ρ : Fin q → T → ℂ)
    (hγ : ∀j, Continuous (γ j)) (hρ : ∀j, Continuous (ρ j)) (hup : ∀j t, 0<(γ j t).im)
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hh : ExactAnchoredHierarchy ν .one) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    {δ : ℝ} (hδ : 0<δ) (hb : ∀j t, ‖ρ j t‖≤δ*(γ j t).im) :
    Integrable (fun s => Complex.exp (∑j, reflectComplex (ε j)
      (compactCenteredSource κ (γ j) (ρ j) s))) ν ∧
    ‖(∫ s, Complex.exp (∑j, reflectComplex (ε j)
      (compactCenteredSource κ (γ j) (ρ j) s)) ∂ν)-1‖ ≤
      δ*(192*(q:ℝ)^2+(q:ℝ)*Real.exp (((q:ℝ)*δ)^2/orthogonalBulkExponentialScale)) := by
  let X := fun j s => reflectComplex (ε j) (compactCenteredSource κ (γ j) (ρ j) s)
  have hm j : Measurable (X j) := (continuous_reflectComplex (ε j)).measurable.comp
    (measurable_compactCenteredSource κ (γ j) (ρ j) (hγ j) (hρ j) (hup j))
  have h2 j := orthogonal_compactCenteredSource_second_moment κ (γ j) (ρ j) (hγ j) (hρ j) (hup j)
    ν hh ha he hδ.le (hb j)
  have h2i j : Integrable (fun s => ‖X j s‖^2) ν := by
    simpa only [X,norm_reflectComplex] using (h2 j).1
  have h2b j : (∫s, ‖X j s‖^2 ∂ν)≤384*δ^2 := by
    simpa only [X,norm_reflectComplex] using (h2 j).2
  obtain ⟨hXi2,hXb2⟩ := finite_sum_second_moment_bound ν X hm h2i (384*δ^2) h2b
  have hE j := orthogonal_compactCenteredSource_exp_bound κ (γ j) (ρ j) (hγ j) (hρ j) (hup j)
    ν hh ha he hδ.le (show 0≤2*(q:ℝ) by positivity) (hb j)
  have hEi j : Integrable (fun s => Real.exp (2*(q:ℝ)*‖X j s‖)) ν := by
    simpa only [X,norm_reflectComplex] using (hE j).1
  have hEb j : (∫s, Real.exp (2*(q:ℝ)*‖X j s‖) ∂ν)≤
      2*Real.exp ((2*(q:ℝ)*δ)^2/(4*orthogonalBulkExponentialScale)) := by
    simpa only [X,norm_reflectComplex] using (hE j).2
  obtain ⟨hXiE,hXbE⟩ := finite_sum_exp_moment_bound hq ν X hm (by norm_num : (0:ℝ)≤2)
    hEi _ hEb
  obtain ⟨hi,hb'⟩ := exponential_expectation_close_of_second_moment ν
    (fun s => ∑j, X j s) (Finset.measurable_sum _ (fun j _ => hm j)) hXi2 hXiE hδ
  refine ⟨hi,hb'.trans ?_⟩
  calc
    _ ≤ ((q:ℝ)^2*(384*δ^2))/(2*δ)+(δ/2)*
        ((q:ℝ)*(2*Real.exp ((2*(q:ℝ)*δ)^2/(4*orthogonalBulkExponentialScale)))) :=
      add_le_add (div_le_div_of_nonneg_right hXb2 (by positivity))
        (mul_le_mul_of_nonneg_left hXbE (by positivity))
    _ = _ := by
      have heq : (2*(q:ℝ)*δ)^2/(4*orthogonalBulkExponentialScale)=
          ((q:ℝ)*δ)^2/orthogonalBulkExponentialScale := by ring
      rw [heq]
      field_simp
      ring

@[simp] theorem nevanlinnaPathPrimitive_conj (s : AnchoredCountingState) (u v : ℂ) :
    nevanlinnaPathPrimitive s (starRingEnd ℂ u) (starRingEnd ℂ v)=
      starRingEnd ℂ (nevanlinnaPathPrimitive s u v) := by
  unfold nevanlinnaPathPrimitive
  simp_rw [ratioPath_conj,anchoredNevanlinna_conj]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with t
  simp

/-- The straight-path primitive has an exact centered decomposition, before
exponentiation, so the coherent square-root branch is retained. -/
theorem nevanlinnaPathPrimitive_centered (s : AnchoredCountingState) {u v : ℂ}
    (hu : 0<u.im) (hv : 0<v.im) :
    nevanlinnaPathPrimitive s u v=(u-v)*Complex.I-
      compactCenteredSource ratioIntervalMeasure
        (fun t : RatioInterval=>ratioPath u v t) (fun _=>-(u-v)) s := by
  have hi : Integrable (fun t : RatioInterval=>-(u-v)*anchoredNevanlinna s (ratioPath u v t))
      ratioIntervalMeasure :=
    (continuous_const.mul (continuous_nevanlinna_ratioPath s (Or.inl ⟨hu,hv⟩))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp only [compactCenteredSource,mul_sub]
  rw [integral_sub hi (integrable_const _)]
  simp only [neg_mul,integral_neg]
  simp [nevanlinnaPathPrimitive]

theorem nevanlinnaPathPrimitive_signed_centered (s : AnchoredCountingState)
    (ε : Bool) {u v : ℂ}
    (hu : 0<(reflectComplex ε u).im) (hv : 0<(reflectComplex ε v).im) :
    nevanlinnaPathPrimitive s u v=signedRatioPhase ε u v-
      reflectComplex ε (compactCenteredSource ratioIntervalMeasure
        (fun t : RatioInterval=>ratioPath (reflectComplex ε u) (reflectComplex ε v) t)
        (fun _=>-(reflectComplex ε u-reflectComplex ε v)) s) := by
  cases ε with
  | true => simpa only [reflectComplex,if_true,signedRatioPhase] using
      nevanlinnaPathPrimitive_centered s hu hv
  | false =>
    have h := congrArg (starRingEnd ℂ) (nevanlinnaPathPrimitive_centered s hu hv)
    simpa only [reflectComplex,Bool.false_eq_true,if_false,signedRatioPhase,
      nevanlinnaPathPrimitive_conj,Complex.conj_conj,map_sub,map_mul,Complex.conj_I,mul_neg]
      using h

theorem orthogonalCharacteristicRatio_exp_average (s : AnchoredCountingState) {u v w : ℂ}
    (huv : SameOpenHalfPlane u v) (hwv : SameOpenHalfPlane w v) :
    orthogonalCharacteristicRatio s u v w=
      Complex.exp (-(1/2:ℂ)*(nevanlinnaPathPrimitive s u v+nevanlinnaPathPrimitive s u w)) := by
  rw [orthogonalCharacteristicRatio_eq_exp s huv,nevanlinnaPathPrimitive_cocycle s huv hwv]
  congr 1
  ring

/-- Halving a source commutes with both its genuine integral and reflection. -/
theorem reflected_halfCenteredSource (ε : Bool) (γ ρ : RatioInterval→ℂ) (s : AnchoredCountingState) :
    reflectComplex ε (compactCenteredSource ratioIntervalMeasure γ (fun t=>(1/2:ℂ)*ρ t) s)=
      (1/2:ℂ)*reflectComplex ε (compactCenteredSource ratioIntervalMeasure γ ρ s) := by
  have h : compactCenteredSource ratioIntervalMeasure γ (fun t=>(1/2:ℂ)*ρ t) s=
      (1/2:ℂ)*compactCenteredSource ratioIntervalMeasure γ ρ s := by
    simp only [compactCenteredSource,mul_assoc,integral_const_mul]
  rw [h]
  cases ε with
  | true => rfl
  | false =>
    change starRingEnd ℂ ((1/2:ℂ)*_)=(1/2:ℂ)*starRingEnd ℂ _
    rw [map_mul]
    congr 1
    apply Complex.ext <;> norm_num


def signedOrthogonalRatioPhase (ε : Bool) (u v w : ℂ) : ℂ :=
  (1/2:ℂ)*(signedRatioPhase ε u v+signedRatioPhase ε u w)

theorem sameOpenHalfPlane_of_reflect_pos (ε : Bool) {u v : ℂ}
    (hu : 0<(reflectComplex ε u).im) (hv : 0<(reflectComplex ε v).im) :
    SameOpenHalfPlane u v := by
  cases ε with
  | true => exact Or.inl (by simpa [reflectComplex] using And.intro hu hv)
  | false => exact Or.inr (by simpa [reflectComplex] using And.intro hu hv)

/-- True mixed orthogonal ratios approach their deterministic phase whenever
both paired endpoint displacements are small compared with their common height. -/
theorem expectedOrthogonalCharacteristicRatios_signed_normalized_bound {q : ℕ}
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hh : ExactAnchoredHierarchy ν .one) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState=>Real.exp (a*‖s.val.2‖^2)) ν)
    (ε : Fin q → Bool) (u v w : Fin q → ℂ) {η δ : ℝ} (hη : 0<η)
    (hu : ∀j,η≤(reflectComplex (ε j) (u j)).im)
    (hv : ∀j,η≤(reflectComplex (ε j) (v j)).im)
    (hw : ∀j,η≤(reflectComplex (ε j) (w j)).im)
    (hδ : 0<δ) (hdv : ∀j,‖u j-v j‖≤δ*η) (hdw : ∀j,‖u j-w j‖≤δ*η) :
    ‖Complex.exp (∑j,signedOrthogonalRatioPhase (ε j) (u j) (v j) (w j))*
      expectedOrthogonalCharacteristicRatios ν u v w-1‖≤
      δ*(192*((q+q:ℕ):ℝ)^2+((q+q:ℕ):ℝ)*
        Real.exp ((((q+q:ℕ):ℝ)*δ)^2 / orthogonalBulkExponentialScale)) := by
  by_cases hq : q=0
  · subst q
    simp [expectedOrthogonalCharacteristicRatios,orthogonalCharacteristicRatios]
  have hqp : 0<q+q := by omega
  let U := fun j=>reflectComplex (ε j) (u j)
  let V := fun j=>reflectComplex (ε j) (v j)
  let W := fun j=>reflectComplex (ε j) (w j)
  let γv := fun j=>fun t : RatioInterval=>ratioPath (U j) (V j) t
  let γw := fun j=>fun t : RatioInterval=>ratioPath (U j) (W j) t
  let ρv := fun j=>fun _ : RatioInterval=>(1/2:ℂ)*(-(U j-V j))
  let ρw := fun j=>fun _ : RatioInterval=>(1/2:ℂ)*(-(U j-W j))
  let γ := Fin.append γv γw
  let ρ := Fin.append ρv ρw
  have hγ j : Continuous (γ j) := by
    refine Fin.addCases (fun j=>?_) (fun j=>?_) j <;>
      simp only [γ,Fin.append_left,Fin.append_right] <;>
      exact (continuous_ratioPath _ _).comp continuous_subtype_val
  have hρ j : Continuous (ρ j) := by
    refine Fin.addCases (fun j=>?_) (fun j=>?_) j <;>
      simp only [ρ,Fin.append_left,Fin.append_right] <;> exact continuous_const
  have hup : ∀j t,0<(γ j t).im := by
    intro j
    refine Fin.addCases (fun j t=>?_) (fun j t=>?_) j
    · simpa only [γ,Fin.append_left,γv,U,V] using hη.trans_le (ratioPath_im_lower (hu j) (hv j) t)
    · simpa only [γ,Fin.append_right,γw,U,W] using hη.trans_le (ratioPath_im_lower (hu j) (hw j) t)
  have hr : ∀j t,‖ρ j t‖≤δ*(γ j t).im := by
    intro j
    refine Fin.addCases (fun j t=>?_) (fun j t=>?_) j
    · simp only [ρ,γ,Fin.append_left]
      change ‖(1/2:ℂ)*(-(U j-V j))‖≤δ*(ratioPath (U j) (V j) t).im
      rw [norm_mul,norm_neg]
      norm_num only [norm_div,norm_one,Complex.norm_ofNat]
      have hn : ‖U j-V j‖=‖u j-v j‖ := by
        dsimp [U,V]; rw [← reflectComplex_sub,norm_reflectComplex]
      rw [hn]
      have hb := (hdv j).trans (mul_le_mul_of_nonneg_left (ratioPath_im_lower (hu j) (hv j) t) hδ.le)
      nlinarith [norm_nonneg (u j-v j)]
    · simp only [ρ,γ,Fin.append_right]
      change ‖(1/2:ℂ)*(-(U j-W j))‖≤δ*(ratioPath (U j) (W j) t).im
      rw [norm_mul,norm_neg]
      norm_num only [norm_div,norm_one,Complex.norm_ofNat]
      have hn : ‖U j-W j‖=‖u j-w j‖ := by
        dsimp [U,W]; rw [← reflectComplex_sub,norm_reflectComplex]
      rw [hn]
      have hb := (hdw j).trans (mul_le_mul_of_nonneg_left (ratioPath_im_lower (hu j) (hw j) t) hδ.le)
      nlinarith [norm_nonneg (u j-w j)]
  obtain ⟨_,hb⟩ := orthogonal_finiteReflectedCompactSource_exponential_close hqp ratioIntervalMeasure
    (Fin.append ε ε) γ ρ hγ hρ hup ν hh ha he hδ hr
  have huv j := sameOpenHalfPlane_of_reflect_pos (ε j) (hη.trans_le (hu j)) (hη.trans_le (hv j))
  have hwv j := sameOpenHalfPlane_of_reflect_pos (ε j) (hη.trans_le (hw j)) (hη.trans_le (hv j))
  have heq s : orthogonalCharacteristicRatios s u v w=
      Complex.exp (-(∑j,signedOrthogonalRatioPhase (ε j) (u j) (v j) (w j)))*
        Complex.exp (∑j,reflectComplex (Fin.append ε ε j)
          (compactCenteredSource ratioIntervalMeasure (γ j) (ρ j) s)) := by
    unfold orthogonalCharacteristicRatios
    simp_rw [orthogonalCharacteristicRatio_exp_average s (huv _) (hwv _)]
    rw [← Complex.exp_sum,← Complex.exp_add]
    congr 1
    simp only [Fin.sum_univ_add,γ,ρ,Fin.append_left,Fin.append_right]
    rw [← Finset.sum_add_distrib,← Finset.sum_neg_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [γv,γw,ρv,ρw,U,V,W]
    rw [reflected_halfCenteredSource,reflected_halfCenteredSource,
      nevanlinnaPathPrimitive_signed_centered s (ε j) (hη.trans_le (hu j)) (hη.trans_le (hv j)),
      nevanlinnaPathPrimitive_signed_centered s (ε j) (hη.trans_le (hu j)) (hη.trans_le (hw j))]
    dsimp [signedOrthogonalRatioPhase]
    ring
  simp only [expectedOrthogonalCharacteristicRatios,heq,integral_const_mul]
  rw [← mul_assoc,← Complex.exp_add,add_neg_cancel,Complex.exp_zero,one_mul]
  exact hb

/-- Vanishing relative displacement gives an actual expectation limit, including
all correlated signs and the coherent orthogonal square-root branches. -/
theorem tendsto_expectedOrthogonalCharacteristicRatios_signed_normalized
    {A : Type*} {l : Filter A} {q : ℕ}
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hh : ExactAnchoredHierarchy ν .one) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState=>Real.exp (a*‖s.val.2‖^2)) ν)
    (ε : Fin q → Bool) (u v w : A → Fin q → ℂ) (η δ : A → ℝ)
    (hδ : Tendsto δ l (𝓝 0))
    (hgeom : ∀ᶠt in l,0<η t ∧ 0<δ t ∧
      (∀j,η t≤(reflectComplex (ε j) (u t j)).im) ∧
      (∀j,η t≤(reflectComplex (ε j) (v t j)).im) ∧
      (∀j,η t≤(reflectComplex (ε j) (w t j)).im) ∧
      (∀j,‖u t j-v t j‖≤δ t*η t) ∧ ∀j,‖u t j-w t j‖≤δ t*η t) :
    Tendsto (fun t=>Complex.exp (∑j,signedOrthogonalRatioPhase (ε j) (u t j) (v t j) (w t j))*
      expectedOrthogonalCharacteristicRatios ν (u t) (v t) (w t)) l (𝓝 1) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hb : Tendsto (fun t=>δ t*(192*((q+q:ℕ):ℝ)^2+((q+q:ℕ):ℝ)*
      Real.exp ((((q+q:ℕ):ℝ)*δ t)^2/orthogonalBulkExponentialScale))) l (𝓝 0) := by
    have hc : Continuous (fun r : ℝ=>r*(192*((q+q:ℕ):ℝ)^2+((q+q:ℕ):ℝ)*
        Real.exp ((((q+q:ℕ):ℝ)*r)^2/orthogonalBulkExponentialScale))) := by fun_prop
    simpa using hc.continuousAt.tendsto.comp hδ
  apply squeeze_zero' (Eventually.of_forall (fun _=>norm_nonneg _)) _ hb
  filter_upwards [hgeom] with t ht
  exact expectedOrthogonalCharacteristicRatios_signed_normalized_bound ν hh ha he ε (u t) (v t) (w t)
    ht.1 ht.2.2.1 ht.2.2.2.1 ht.2.2.2.2.1 ht.2.1 ht.2.2.2.2.2.1 ht.2.2.2.2.2.2

end BourgadeHuang
