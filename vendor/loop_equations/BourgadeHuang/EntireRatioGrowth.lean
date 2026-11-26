import BourgadeHuang.HyperbolicRatioGrowth
import BourgadeHuang.EntireRatioExpectation

/-! Global off-real characteristic-ratio growth, with only logarithmic
vertical costs, derived from the actual limiting hierarchy. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang

/-- Reflection into the upper half-plane preserves the real coordinate. -/
def upperRepresentative (z : ℂ) : ℂ := z.re+Complex.I*|z.im|

@[simp] theorem upperRepresentative_im (z : ℂ) : (upperRepresentative z).im=|z.im| := by
  simp [upperRepresentative]

@[simp] theorem upperRepresentative_re (z : ℂ) : (upperRepresentative z).re=z.re := by
  simp [upperRepresentative]

theorem upperRepresentative_eq (z : ℂ) (hz : 0≤z.im) : upperRepresentative z=z := by
  rw [upperRepresentative,abs_of_nonneg hz,mul_comm Complex.I]
  exact Complex.re_add_im z

theorem upperRepresentative_eq_conj (z : ℂ) (hz : z.im≤0) :
    upperRepresentative z=starRingEnd ℂ z := by
  apply Complex.ext <;> simp [upperRepresentative,abs_of_nonpos hz]

theorem norm_entireCharacteristicRatio_upper (s : AnchoredCountingState) (u v : ℂ) :
    ‖entireCharacteristicRatio s (upperRepresentative u) (upperRepresentative v)‖=
      ‖entireCharacteristicRatio s u v‖ := by
  by_cases hu : 0≤u.im <;> by_cases hv : 0≤v.im
  · rw [upperRepresentative_eq u hu,upperRepresentative_eq v hv]
  · rw [upperRepresentative_eq u hu,upperRepresentative_eq_conj v (le_of_not_ge hv),
      norm_entireCharacteristicRatio_conj_denominator]
  · rw [upperRepresentative_eq_conj u (le_of_not_ge hu),upperRepresentative_eq v hv,
      norm_entireCharacteristicRatio_conj_numerator]
  · rw [upperRepresentative_eq_conj u (le_of_not_ge hu),upperRepresentative_eq_conj v (le_of_not_ge hv),
      norm_entireCharacteristicRatio_conj_numerator,norm_entireCharacteristicRatio_conj_denominator]

theorem norm_anchoredCharacteristicRatio_normalized (s : AnchoredCountingState) (u v : ℂ) :
    ‖anchoredCharacteristicRatio s u v‖=
      Real.exp (u.im-v.im)*‖normalizedUpperRatio s u v‖ := by
  rw [normalizedUpperRatio,norm_mul,Complex.norm_exp,← mul_assoc,← Real.exp_add]
  have hzero : u.im-v.im+(Complex.I*(u-v)).re=0 := by
    simp only [Complex.mul_re,Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_sub,Complex.sub_im]
    ring
  rw [hzero,Real.exp_zero,one_mul]

theorem norm_entireCharacteristicRatio_normalized_upper (s : AnchoredCountingState)
    {u v : ℂ} (hu : u.im≠0) (hv : v.im≠0) :
    ‖entireCharacteristicRatio s u v‖=Real.exp (|u.im|-|v.im|)*
      ‖normalizedUpperRatio s (upperRepresentative u) (upperRepresentative v)‖ := by
  rw [← norm_entireCharacteristicRatio_upper s u v,
    entireCharacteristicRatio_eq_anchored s (Or.inl ⟨by simpa using abs_pos.mpr hu,by simpa using abs_pos.mpr hv⟩),
    norm_anchoredCharacteristicRatio_normalized,upperRepresentative_im,upperRepresentative_im]

/-- The expected entire ratio has the exact deterministic exponential rate,
up to a bound quadratic in the logarithmic path costs. -/
theorem expectedEntireCharacteristicRatios_growth {q : ℕ} (hq : 0<q)
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hh : ExactAnchoredHierarchy ν .two) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (u v : Fin q → ℂ) (hu : ∀j, (u j).im≠0) (hv : ∀j, (v j).im≠0)
    (H : Fin q → ℝ) (hH : ∀j, 0<H j) {D : ℝ} (_hD : 0≤D)
    (hcost : ∀j, ratioHeightCost (upperRepresentative (u j)) (upperRepresentative (v j)) (H j)≤D) :
    ‖expectedEntireCharacteristicRatios ν u v‖≤6*(q:ℝ)*
      Real.exp ((∑j, (|(u j).im|-|(v j).im|))+(3*(q:ℝ)*D)^2/(4*bulkExponentialScale)) := by
  let U := fun j => upperRepresentative (u j)
  let V := fun j => upperRepresentative (v j)
  have hU j : 0<(U j).im := by simpa [U] using abs_pos.mpr (hu j)
  have hV j : 0<(V j).im := by simpa [V] using abs_pos.mpr (hv j)
  let f := fun j s => ‖normalizedUpperRatio s (U j) (V j)‖
  have hm j : Measurable (f j) := (measurable_normalizedUpperRatio (Or.inl ⟨hU j,hV j⟩)).norm
  have hscalar j := normalizedUpperRatio_rpow_bound ν hh ha he (hU j) (hV j) (hH j)
    (show (0:ℝ)≤(q:ℝ) by positivity)
  have hi j : Integrable (fun s => (f j s)^q) ν := by
    simpa only [f,Real.rpow_natCast] using (hscalar j).1
  have hb j : (∫s, (f j s)^q ∂ν)≤6*Real.exp ((3*(q:ℝ)*D)^2/(4*bulkExponentialScale)) := by
    have h := (hscalar j).2
    simp only [Real.rpow_natCast] at h
    apply h.trans
    have hcn := ratioHeightCost_nonneg (U j) (V j) (hH j)
    have hcl : ratioHeightCost (U j) (V j) (H j)≤D := hcost j
    gcongr
    exact mul_nonneg (by norm_num) bulkExponentialScale_pos.le
  obtain ⟨hpi,hpb⟩ := finite_product_integral_bound hq ν f hm (fun _ _ => norm_nonneg _) hi _ hb
  have heq s : ‖entireCharacteristicRatios s u v‖=
      Real.exp (∑j, (|(u j).im|-|(v j).im|))*(∏j, f j s) := by
    unfold entireCharacteristicRatios
    rw [norm_prod]
    simp_rw [norm_entireCharacteristicRatio_normalized_upper s (hu _) (hv _)]
    rw [Finset.prod_mul_distrib,← Real.exp_sum]
  have hnorm : Integrable (fun s => ‖entireCharacteristicRatios s u v‖) ν := by
    simpa only [heq] using hpi.const_mul (Real.exp (∑j, (|(u j).im|-|(v j).im|)))
  calc
    _ ≤ ∫s, ‖entireCharacteristicRatios s u v‖ ∂ν := norm_integral_le_integral_norm _
    _ = Real.exp (∑j, (|(u j).im|-|(v j).im|))*(∫s, ∏j, f j s ∂ν) := by
      simp only [heq,integral_const_mul]
    _ ≤ Real.exp (∑j, (|(u j).im|-|(v j).im|))*
        ((q:ℝ)*(6*Real.exp ((3*(q:ℝ)*D)^2/(4*bulkExponentialScale)))) :=
      mul_le_mul_of_nonneg_left hpb (Real.exp_pos _).le
    _ = _ := by rw [Real.exp_add]; ring

end BourgadeHuang
