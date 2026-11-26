import BourgadeHuang.HyperbolicRatioPaths
import BourgadeHuang.FiniteProductBounds

/-! Logarithmic path costs for arbitrary upper-half-plane endpoint ratios,
obtained by composing two exponential vertical paths and a horizontal path. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang

def normalizedUpperRatio (s : AnchoredCountingState) (u v : ℂ) : ℂ :=
  Complex.exp (Complex.I*(u-v))*anchoredCharacteristicRatio s u v

theorem normalizedUpperRatio_cocycle (s : AnchoredCountingState) {u v b : ℂ}
    (hub : SameOpenHalfPlane u b) (hvb : SameOpenHalfPlane v b) :
    normalizedUpperRatio s u v = normalizedUpperRatio s u b*normalizedUpperRatio s b v := by
  unfold normalizedUpperRatio
  rw [anchoredCharacteristicRatio_cocycle s hub hvb]
  have he : Complex.exp (Complex.I*(u-v))=
      Complex.exp (Complex.I*(u-b))*Complex.exp (Complex.I*(b-v)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [he]
  ring

theorem measurable_normalizedUpperRatio {u v : ℂ} (huv : SameOpenHalfPlane u v) :
    Measurable (fun s => normalizedUpperRatio s u v) :=
  measurable_const.mul (measurable_anchoredCharacteristicRatio huv)

def ratioHeightCost (u v : ℂ) (H : ℝ) : ℝ :=
  |Real.log (u.im/H)|+|u.re-v.re|/H+|Real.log (H/v.im)|

theorem ratioHeightCost_nonneg (u v : ℂ) {H : ℝ} (hH : 0<H) :
    0≤ratioHeightCost u v H := by unfold ratioHeightCost; positivity

/-- A bound uniform in the locations and heights, with a logarithmic cost
for vertical displacement.  All nonnegative real moments are controlled. -/
theorem normalizedUpperRatio_rpow_bound
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hh : ExactAnchoredHierarchy ν .two) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    {u v : ℂ} (hu : 0<u.im) (hv : 0<v.im) {H L : ℝ} (hH : 0<H) (hL : 0≤L) :
    Integrable (fun s => ‖normalizedUpperRatio s u v‖^L) ν ∧
      (∫s, ‖normalizedUpperRatio s u v‖^L ∂ν)≤
        6*Real.exp ((3*L*ratioHeightCost u v H)^2/(4*bulkExponentialScale)) := by
  let U : ℂ := u.re+Complex.I*H
  let V : ℂ := v.re+Complex.I*H
  have hU : 0<U.im := by simpa [U] using hH
  have hV : 0<V.im := by simpa [V] using hH
  let A : Fin 3 → ℂ := ![u,U,V]
  let B : Fin 3 → ℂ := ![U,V,v]
  have hAB (j : Fin 3) : SameOpenHalfPlane (A j) (B j) := by
    fin_cases j <;> exact Or.inl ⟨by assumption,by assumption⟩
  let X := fun j s => normalizedUpperRatio s (A j) (B j)
  have hmeas j : Measurable (X j) := measurable_normalizedUpperRatio (hAB j)
  have hL3 : 0≤3*L := mul_nonneg (by norm_num) hL
  have hu_eq : (u.re:ℂ)+Complex.I*u.im=u := by simpa only [mul_comm Complex.I] using Complex.re_add_im u
  have hv_eq : (v.re:ℂ)+Complex.I*v.im=v := by simpa only [mul_comm Complex.I] using Complex.re_add_im v
  have hscalar (j : Fin 3) : Integrable (fun s => ‖X j s‖^(3*L)) ν ∧
      (∫s, ‖X j s‖^(3*L) ∂ν)≤
        2*Real.exp ((3*L*ratioHeightCost u v H)^2/(4*bulkExponentialScale)) := by
    have hcost0 : |Real.log (u.im/H)|≤ratioHeightCost u v H := by
      unfold ratioHeightCost
      have := div_nonneg (abs_nonneg (u.re-v.re)) hH.le
      have := abs_nonneg (Real.log (H/v.im))
      linarith
    have hcost1 : |u.re-v.re|/H≤ratioHeightCost u v H := by
      unfold ratioHeightCost
      have := abs_nonneg (Real.log (u.im/H))
      have := abs_nonneg (Real.log (H/v.im))
      linarith
    have hcost2 : |Real.log (H/v.im)|≤ratioHeightCost u v H := by
      unfold ratioHeightCost
      have := div_nonneg (abs_nonneg (u.re-v.re)) hH.le
      have := abs_nonneg (Real.log (u.im/H))
      linarith
    fin_cases j
    · have ht := normalized_vertical_ratio_rpow_bound ν hh ha he u.re hH hu hL3
      simp only [hu_eq] at ht
      refine ⟨ht.1,ht.2.trans ?_⟩
      gcongr
      exact mul_nonneg (by norm_num) bulkExponentialScale_pos.le
    · have ht := normalized_horizontal_ratio_rpow_bound ν hh ha he v.re u.re hH hL3
      refine ⟨ht.1,ht.2.trans ?_⟩
      gcongr
      exact mul_nonneg (by norm_num) bulkExponentialScale_pos.le
    · have ht := normalized_vertical_ratio_rpow_bound ν hh ha he v.re hv hH hL3
      simp only [hv_eq] at ht
      refine ⟨ht.1,ht.2.trans ?_⟩
      gcongr
      exact mul_nonneg (by norm_num) bulkExponentialScale_pos.le
  have hp (j : Fin 3) (s : AnchoredCountingState) : (‖X j s‖^L)^3=‖X j s‖^(3*L) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (norm_nonneg _)]
    congr 1
    norm_num
    ring
  have hi j : Integrable (fun s => (‖X j s‖^L)^3) ν := by
    simpa only [hp] using (hscalar j).1
  have hb j : (∫s, (‖X j s‖^L)^3 ∂ν)≤
      2*Real.exp ((3*L*ratioHeightCost u v H)^2/(4*bulkExponentialScale)) := by
    simpa only [hp] using (hscalar j).2
  obtain ⟨hpi,hpb⟩ := finite_product_integral_bound (by norm_num : 0<3) ν
    (fun j s => ‖X j s‖^L) (fun j => (hmeas j).norm.pow_const L)
    (fun j s => Real.rpow_nonneg (norm_nonneg _) _) hi _ hb
  have hprod (s : AnchoredCountingState) : (∏j, ‖X j s‖^L)=‖normalizedUpperRatio s u v‖^L := by
    rw [Fin.prod_univ_three]
    change ‖normalizedUpperRatio s u U‖^L*‖normalizedUpperRatio s U V‖^L*
      ‖normalizedUpperRatio s V v‖^L=‖normalizedUpperRatio s u v‖^L
    rw [← Real.mul_rpow (norm_nonneg _) (norm_nonneg _),← Real.mul_rpow (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _),← norm_mul,← norm_mul]
    rw [← normalizedUpperRatio_cocycle s (Or.inl ⟨hu,hU⟩) (Or.inl ⟨hV,hU⟩),
      ← normalizedUpperRatio_cocycle s (Or.inl ⟨hu,hV⟩) (Or.inl ⟨hv,hV⟩)]
  refine ⟨by simpa only [hprod] using hpi, ?_⟩
  simpa only [hprod] using (show (∫s, ∏j, ‖X j s‖^L ∂ν)≤
      6*Real.exp ((3*L*ratioHeightCost u v H)^2/(4*bulkExponentialScale)) by
    convert hpb using 1 <;> norm_num <;> ring)

end BourgadeHuang
