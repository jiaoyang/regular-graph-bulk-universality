import BourgadeHuang.RationalBulk.CompactSources
import BourgadeHuang.EntireRatioGrowth

/-! General-beta ratio estimates along true paths and homogeneous rays. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalBulk

/-- All positive real moments of the normalized genuine ratio are controlled by
relative path speed, with the constant independent of the location of the path. -/
theorem normalized_ratio_rpow_bound_along_path
    (γ γ' : ℝ → ℂ) (hγ : Continuous γ) (hγ' : Continuous γ')
    (hd : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt γ (γ' t) t)
    (hup : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 < (γ t).im)
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν] (β : ℝ)
    (hh : ExactHierarchy ν β) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    {δ L : ℝ} (hδ : 0≤δ) (hL : 0≤L)
    (hspeed : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖γ' t‖≤δ*(γ t).im) :
    Integrable (fun s => ‖Complex.exp (Complex.I*(γ 1-γ 0))*
      anchoredCharacteristicRatio s (γ 1) (γ 0)‖^L) ν ∧
    (∫ s, ‖Complex.exp (Complex.I*(γ 1-γ 0))*
      anchoredCharacteristicRatio s (γ 1) (γ 0)‖^L ∂ν) ≤
        2*Real.exp ((L*δ)^2/(4*bulkExponentialScale β)) := by
  let Y := compactCenteredSource ratioIntervalMeasure
    (fun t : RatioInterval => γ t) (fun t => -γ' t)
  have hγc : Continuous (fun t : RatioInterval => γ t) := hγ.comp continuous_subtype_val
  have hρc : Continuous (fun t : RatioInterval => -γ' t) := (hγ'.comp continuous_subtype_val).neg
  have hupc := fun t : RatioInterval => hup t t.property
  have hρδ (t : RatioInterval) : ‖-γ' t‖≤δ*(γ t).im := by
    simpa only [norm_neg] using hspeed t t.property
  obtain ⟨hi,hb⟩ := compactCenteredSource_exp_bound ratioIntervalMeasure
    (fun t : RatioInterval => γ t) (fun t => -γ' t) hγc hρc hupc
    ν β hh ha he hδ hL hρδ
  have hm : Measurable Y := measurable_compactCenteredSource
    ratioIntervalMeasure _ _ hγc hρc hupc
  have heq (s : AnchoredCountingState) :
      ‖Complex.exp (Complex.I*(γ 1-γ 0))*
        anchoredCharacteristicRatio s (γ 1) (γ 0)‖^L = Real.exp (L*(Y s).re) := by
    rw [normalized_ratio_eq_exp_path_source s γ γ' hγ hγ' hd hup,
      Complex.norm_exp,← Real.exp_mul]
    congr 1
    ring
  have hbpoint (s : AnchoredCountingState) : Real.exp (L*(Y s).re)≤Real.exp (L*‖Y s‖) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Complex.re_le_norm _) hL)
  have hi' : Integrable (fun s => Real.exp (L*(Y s).re)) ν := by
    apply hi.mono' (Real.continuous_exp.measurable.comp
      (measurable_const.mul (Complex.continuous_re.measurable.comp hm))).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun s => by
      simpa only [Function.comp_apply,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hbpoint s
  simp only [heq]
  exact ⟨hi',(integral_mono hi' hi hbpoint).trans hb⟩


/-- Straight upper-half-plane paths give a bound invariant under common positive scaling. -/
theorem normalizedUpperRatio_rpow_bound
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν] (β : ℝ)
    (hh : ExactHierarchy ν β) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    {u v : ℂ} (hu : 0<u.im) (hv : 0<v.im) {D L : ℝ}
    (hD : 0≤D) (hL : 0≤L) (hcost : ‖u-v‖≤D*min u.im v.im) :
    Integrable (fun s => ‖normalizedUpperRatio s u v‖^L) ν ∧
    (∫s, ‖normalizedUpperRatio s u v‖^L ∂ν)≤
      2*Real.exp ((L*D)^2/(4*bulkExponentialScale β)) := by
  have hd (t : ℝ) : HasDerivAt (ratioPath u v) (u-v) t := by
    change HasDerivAt (fun x : ℝ=>v+(x:ℂ)*(u-v)) (u-v) t
    simpa only [id_eq,Complex.ofReal_one,one_mul] using
      (((hasDerivAt_id t).ofReal_comp).mul_const (u-v)).const_add v
  have hlow (t : ℝ) (ht : t∈Set.Icc (0:ℝ) 1) :
      min u.im v.im ≤ (ratioPath u v t).im := by
    have heq : (ratioPath u v t).im=(1-t)*v.im+t*u.im := by simp [ratioPath]; ring
    rw [heq]
    nlinarith [mul_le_mul_of_nonneg_left (min_le_left u.im v.im) ht.1,
      mul_le_mul_of_nonneg_left (min_le_right u.im v.im) (sub_nonneg.mpr ht.2)]
  have hpath := normalized_ratio_rpow_bound_along_path
    (ratioPath u v) (fun _=>u-v) (continuous_ratioPath u v) continuous_const
    (fun t _=>hd t) (fun t ht=>(lt_min hu hv).trans_le (hlow t ht))
    ν β hh ha he hD hL (fun t ht=>hcost.trans (mul_le_mul_of_nonneg_left (hlow t ht) hD))
  simpa [ratioPath,normalizedUpperRatio] using hpath

end BourgadeHuang.RationalBulk
