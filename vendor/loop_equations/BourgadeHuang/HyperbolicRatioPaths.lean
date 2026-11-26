import BourgadeHuang.BulkCompactSources
import BourgadeHuang.CharacteristicRatioAnalytic
import Mathlib.Analysis.Complex.RealDeriv

/-! Genuine ratio sources along differentiable upper-half-plane paths.
Exponential height parametrization gives logarithmic relative speed. -/
noncomputable section
open scoped Topology
open MeasureTheory Filter
namespace BourgadeHuang

theorem integral_nevanlinna_along_path (s : AnchoredCountingState)
    (γ γ' : ℝ → ℂ) (hγ : Continuous γ) (hγ' : Continuous γ')
    (hd : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt γ (γ' t) t)
    (hup : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 < (γ t).im) :
    (∫ t : RatioInterval, γ' t*anchoredNevanlinna s (γ t) ∂ratioIntervalMeasure) =
      ∫ t : RatioInterval, (γ 1-γ 0)*anchoredNevanlinna s
        (ratioPath (γ 1) (γ 0) t) ∂ratioIntervalMeasure := by
  let P := fun z => ∫ t : RatioInterval, (z-γ 0)*anchoredNevanlinna s
    (ratioPath z (γ 0) t) ∂ratioIntervalMeasure
  have hdP (t : ℝ) (ht : t ∈ Set.uIcc (0:ℝ) 1) :
      HasDerivAt (fun t => P (γ t)) (γ' t*anchoredNevanlinna s (γ t)) t := by
    have ht' : t ∈ Set.Icc (0:ℝ) 1 := by simpa using ht
    have hp := hasDerivAt_integrated_nevanlinna_ratioPath s
      (Or.inl ⟨hup t ht',hup 0 (by simp)⟩)
    have hh := hp.complexToReal_fderiv.comp_hasDerivAt t (hd t ht')
    simpa [P,mul_comm] using hh
  have hc : ContinuousOn (fun t => γ' t*anchoredNevanlinna s (γ t)) (Set.uIcc (0:ℝ) 1) := by
    apply hγ'.continuousOn.mul
    intro t ht
    have ht' : t ∈ Set.Icc (0:ℝ) 1 := by simpa using ht
    exact ((hasDerivAt_anchoredNevanlinna s (hup t ht').ne').continuousAt.comp
      hγ.continuousAt).continuousWithinAt
  rw [integral_ratioInterval (fun t => γ' t*anchoredNevanlinna s (γ t))]
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hdP hc.intervalIntegrable
  simpa [P] using hh

theorem normalized_ratio_eq_exp_path_source (s : AnchoredCountingState)
    (γ γ' : ℝ → ℂ) (hγ : Continuous γ) (hγ' : Continuous γ')
    (hd : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt γ (γ' t) t)
    (hup : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 < (γ t).im) :
    Complex.exp (Complex.I*(γ 1-γ 0))*anchoredCharacteristicRatio s (γ 1) (γ 0) =
      Complex.exp (compactCenteredSource ratioIntervalMeasure
        (fun t : RatioInterval => γ t) (fun t => -γ' t) s) := by
  have hiS : Integrable (fun t : RatioInterval => γ' t*anchoredNevanlinna s (γ t)) ratioIntervalMeasure := by
    have hc : Continuous (fun t : RatioInterval => γ' t*anchoredNevanlinna s (γ t)) := by
      apply (hγ'.comp continuous_subtype_val).mul
      apply continuous_iff_continuousAt.mpr
      intro t
      have hh : ContinuousAt (fun t : RatioInterval => γ t) t :=
        (hγ.comp continuous_subtype_val).continuousAt
      exact (hasDerivAt_anchoredNevanlinna s (hup t t.property).ne').continuousAt.comp (f := fun t : RatioInterval => γ t) hh
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiD : Integrable (fun t : RatioInterval => γ' t*Complex.I) ratioIntervalMeasure :=
    ((hγ'.comp continuous_subtype_val).mul continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hD : (∫ t : RatioInterval, γ' t ∂ratioIntervalMeasure)=γ 1-γ 0 := by
    rw [integral_ratioInterval]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hd t (by simpa using ht)) hγ'.continuousOn.intervalIntegrable
  rw [anchoredCharacteristicRatio,← Complex.exp_add]
  congr 1
  have hfun : (fun t : RatioInterval => -γ' t*(anchoredNevanlinna s (γ t)-Complex.I)) =
      fun t : RatioInterval => γ' t*Complex.I-γ' t*anchoredNevanlinna s (γ t) := by
    funext t
    ring
  rw [compactCenteredSource,hfun,integral_sub hiD hiS,integral_mul_const,hD,
    integral_nevanlinna_along_path s γ γ' hγ hγ' hd hup]
  simp only [neg_mul,integral_neg]
  ring

/-- All positive real moments of the normalized genuine ratio are controlled by
relative path speed, with the constant independent of the location of the path. -/
theorem normalized_ratio_rpow_bound_along_path
    (γ γ' : ℝ → ℂ) (hγ : Continuous γ) (hγ' : Continuous γ')
    (hd : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt γ (γ' t) t)
    (hup : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 < (γ t).im)
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hh : ExactAnchoredHierarchy ν .two) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    {δ L : ℝ} (hδ : 0≤δ) (hL : 0≤L)
    (hspeed : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖γ' t‖≤δ*(γ t).im) :
    Integrable (fun s => ‖Complex.exp (Complex.I*(γ 1-γ 0))*
      anchoredCharacteristicRatio s (γ 1) (γ 0)‖^L) ν ∧
    (∫ s, ‖Complex.exp (Complex.I*(γ 1-γ 0))*
      anchoredCharacteristicRatio s (γ 1) (γ 0)‖^L ∂ν) ≤
        2*Real.exp ((L*δ)^2/(4*bulkExponentialScale)) := by
  let Y := compactCenteredSource ratioIntervalMeasure
    (fun t : RatioInterval => γ t) (fun t => -γ' t)
  have hγc : Continuous (fun t : RatioInterval => γ t) := hγ.comp continuous_subtype_val
  have hρc : Continuous (fun t : RatioInterval => -γ' t) := (hγ'.comp continuous_subtype_val).neg
  have hupc := fun t : RatioInterval => hup t t.property
  have hρδ (t : RatioInterval) : ‖-γ' t‖≤δ*(γ t).im := by
    simpa only [norm_neg] using hspeed t t.property
  obtain ⟨hi,hb⟩ := compactCenteredSource_exp_bound ratioIntervalMeasure
    (fun t : RatioInterval => γ t) (fun t => -γ' t) hγc hρc hupc
    ν hh ha he hδ hL hρδ
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

/-- Exponentially parametrized vertical paths have constant relative speed. -/
def verticalExpPath (x y l t : ℝ) : ℂ := (x:ℂ)+Complex.I*(y*Real.exp (t*l):ℝ)
def verticalExpVelocity (y l t : ℝ) : ℂ := Complex.I*(y*Real.exp (t*l)*l:ℝ)

@[simp] theorem verticalExpPath_im (x y l t : ℝ) :
    (verticalExpPath x y l t).im=y*Real.exp (t*l) := by
  simp only [verticalExpPath,Complex.add_im,Complex.ofReal_im,Complex.mul_im,
    Complex.I_re,Complex.I_im,Complex.ofReal_re,zero_mul,one_mul,zero_add]

theorem continuous_verticalExpPath (x y l : ℝ) : Continuous (verticalExpPath x y l) := by
  exact continuous_const.add (continuous_const.mul
    (Complex.continuous_ofReal.comp (continuous_const.mul
      (Real.continuous_exp.comp (continuous_id.mul continuous_const)))))

theorem continuous_verticalExpVelocity (y l : ℝ) : Continuous (verticalExpVelocity y l) := by
  exact continuous_const.mul (Complex.continuous_ofReal.comp
    ((continuous_const.mul (Real.continuous_exp.comp
      (continuous_id.mul continuous_const))).mul continuous_const))

theorem hasDerivAt_verticalExpPath (x y l t : ℝ) :
    HasDerivAt (verticalExpPath x y l) (verticalExpVelocity y l t) t := by
  have he := (((hasDerivAt_id t).mul_const l).exp.const_mul y).ofReal_comp
  convert (he.const_mul Complex.I).const_add (x:ℂ) using 1 <;>
    simp [verticalExpPath,verticalExpVelocity,mul_assoc]

theorem norm_verticalExpVelocity (x l t : ℝ) {y : ℝ} (hy : 0<y) :
    ‖verticalExpVelocity y l t‖ = |l| * (verticalExpPath x y l t).im := by
  simp only [verticalExpVelocity,norm_mul,Complex.norm_I,Complex.norm_real,one_mul,
    Real.norm_eq_abs,abs_mul,abs_of_pos hy,abs_of_pos (Real.exp_pos _),verticalExpPath_im]
  ring

@[simp] theorem verticalExpPath_zero (x y l : ℝ) :
    verticalExpPath x y l 0=(x:ℂ)+Complex.I*y := by simp [verticalExpPath]

@[simp] theorem verticalExpPath_log_one (x : ℝ) {y Y : ℝ} (hy : 0<y) (hY : 0<Y) :
    verticalExpPath x y (Real.log (Y/y)) 1=(x:ℂ)+Complex.I*Y := by
  simp only [verticalExpPath,one_mul,Real.exp_log (div_pos hY hy)]
  congr 2
  exact_mod_cast mul_div_cancel₀ Y hy.ne'

/-- The genuine vertical ratio has log-height, rather than height-ratio, growth. -/
theorem normalized_vertical_ratio_rpow_bound
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hh : ExactAnchoredHierarchy ν .two) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (x : ℝ) {y Y L : ℝ} (hy : 0<y) (hY : 0<Y) (hL : 0≤L) :
    Integrable (fun s => ‖Complex.exp (Complex.I*((x+Complex.I*Y)-(x+Complex.I*y)))*
      anchoredCharacteristicRatio s (x+Complex.I*Y) (x+Complex.I*y)‖^L) ν ∧
    (∫ s, ‖Complex.exp (Complex.I*((x+Complex.I*Y)-(x+Complex.I*y)))*
      anchoredCharacteristicRatio s (x+Complex.I*Y) (x+Complex.I*y)‖^L ∂ν) ≤
        2*Real.exp ((L*|Real.log (Y/y)|)^2/(4*bulkExponentialScale)) := by
  have hp := normalized_ratio_rpow_bound_along_path
    (verticalExpPath x y (Real.log (Y/y))) (verticalExpVelocity y (Real.log (Y/y)))
    (continuous_verticalExpPath _ _ _) (continuous_verticalExpVelocity _ _)
    (fun t _ => hasDerivAt_verticalExpPath _ _ _ t)
    (fun t _ => by rw [verticalExpPath_im]; exact mul_pos hy (Real.exp_pos _))
    ν hh ha he (abs_nonneg _) hL
    (fun t _ => (norm_verticalExpVelocity x (Real.log (Y/y)) t hy).le)
  simpa only [verticalExpPath_zero,verticalExpPath_log_one x hy hY] using hp

def horizontalPath (x X y t : ℝ) : ℂ := ((x+t*(X-x):ℝ):ℂ)+Complex.I*y

theorem normalized_horizontal_ratio_rpow_bound
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hh : ExactAnchoredHierarchy ν .two) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (x X : ℝ) {y L : ℝ} (hy : 0<y) (hL : 0≤L) :
    Integrable (fun s => ‖Complex.exp (Complex.I*((X+Complex.I*y)-(x+Complex.I*y)))*
      anchoredCharacteristicRatio s (X+Complex.I*y) (x+Complex.I*y)‖^L) ν ∧
    (∫ s, ‖Complex.exp (Complex.I*((X+Complex.I*y)-(x+Complex.I*y)))*
      anchoredCharacteristicRatio s (X+Complex.I*y) (x+Complex.I*y)‖^L ∂ν) ≤
        2*Real.exp ((L*(|X-x|/y))^2/(4*bulkExponentialScale)) := by
  have hc : Continuous (horizontalPath x X y) :=
    (Complex.continuous_ofReal.comp (continuous_const.add
      (continuous_id.mul continuous_const))).add continuous_const
  have hd (t : ℝ) : HasDerivAt (horizontalPath x X y) ((X-x:ℝ):ℂ) t := by
    have hh := (((hasDerivAt_id t).mul_const (X-x)).const_add x).ofReal_comp
    simpa only [horizontalPath,id_eq,one_mul] using hh.add_const (Complex.I*y)
  have him (t : ℝ) : (horizontalPath x X y t).im=y := by
    simp only [horizontalPath,Complex.add_im,Complex.ofReal_im,Complex.mul_im,
      Complex.I_re,Complex.I_im,Complex.ofReal_re,zero_mul,one_mul,zero_add]
  have hs (t : ℝ) : ‖((X-x:ℝ):ℂ)‖≤(|X-x|/y)*(horizontalPath x X y t).im := by
    rw [him,div_mul_cancel₀ _ hy.ne',Complex.norm_real,Real.norm_eq_abs]
  have hp := normalized_ratio_rpow_bound_along_path
    (horizontalPath x X y) (fun _ => ((X-x:ℝ):ℂ)) hc continuous_const
    (fun t _ => hd t) (fun t _ => by rw [him]; exact hy)
    ν hh ha he (div_nonneg (abs_nonneg _) hy.le) hL (fun t _ => hs t)
  simpa [horizontalPath] using hp

end BourgadeHuang
