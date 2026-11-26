import GeneralizedBulk.Graph.MicroscopicScalarState
import GeneralizedBulk.Graph.SpectralGoodImage
import GeneralizedBulk.Graph.ProposalFiberVariance

/-! Actual microscopic vertical scalars are bounded by an affine function
of the physical graph scalar, with constants uniform in the vertical height. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped Topology
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Graph
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

def verticalMicroscopicPoint (Y : ℕ) : GraphNonreal :=
  ⟨(((Y : ℝ)+1 : ℝ) : ℂ)*Complex.I,by simp; positivity⟩

def verticalMicroscopicEta (D : RegularSpectralData d N Ω) (n : ℕ) (sigma : ℝ) (Y : ℕ) : ℝ :=
  microscopicStep (N n) sigma*((Y : ℝ)+1)

theorem verticalMicroscopicEta_pos (n : ℕ) (sigma : ℝ) (hsigma : 0 < sigma) (Y : ℕ) :
    0 < D.verticalMicroscopicEta n sigma Y :=
  mul_pos (microscopicStep_pos _ (D.size_pos n) sigma hsigma) (by positivity)

theorem size_mul_verticalMicroscopicEta (n : ℕ) (sigma : ℝ) (hsigma : 0 < sigma) (Y : ℕ) :
    (N n : ℝ)*D.verticalMicroscopicEta n sigma Y=((Y : ℝ)+1)/sigma := by
  unfold verticalMicroscopicEta microscopicStep
  have hN : (N n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (D.size_pos n).ne'
  field_simp [hN,hsigma.ne']
  <;> ring

theorem verticalMicroscopicEta_tendsto_zero (sigma : ℝ) (hsigma : 0 < sigma) (Y : ℕ) :
    Tendsto (fun n => D.verticalMicroscopicEta n sigma Y) atTop (nhds 0) := by
  have hN : Tendsto (fun n => (N n : ℝ)*sigma) atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp D.size_tendsto).atTop_mul_const hsigma
  have hh := tendsto_inv_atTop_zero.comp hN
  simpa only [verticalMicroscopicEta,microscopicStep,zero_mul] using hh.mul_const ((Y : ℝ)+1)

theorem microscopicParameter_vertical (n : ℕ) (E sigma : ℝ) (hsigma : 0 < sigma) (Y : ℕ) :
    (microscopicParameter (N n) (D.size_pos n) E sigma hsigma (verticalMicroscopicPoint Y)).1=
      spectralParameter E (D.verticalMicroscopicEta n sigma Y) := by
  simp only [microscopicParameter,verticalMicroscopicPoint,spectralParameter,verticalMicroscopicEta]
  push_cast
  ring

def microscopicVerticalNorm (n : ℕ) (ω : Ω) (E sigma a : ℝ) (Y : ℕ) : ℝ :=
  ‖anchoredNevanlinna (D.microscopicCountingState n ω E sigma a) ((((Y : ℝ)+1 : ℝ) : ℂ)*Complex.I)‖

theorem measurable_microscopicVerticalNorm (n : ℕ) (E sigma a : ℝ) (Y : ℕ) :
    Measurable (fun ω => D.microscopicVerticalNorm n ω E sigma a Y) := by
  have hw : (((((Y : ℝ)+1 : ℝ) : ℂ)*Complex.I)).im ≠ 0 := by simp; positivity
  exact ((continuous_anchoredNevanlinna hw).measurable.comp (D.measurable_microscopicCountingState n E sigma a)).norm

theorem microscopicVerticalNorm_affine_bound (n : ℕ) (ω : Ω) (E sigma a : ℝ)
    (hsigma : 0 < sigma) (Y : ℕ) :
    D.microscopicVerticalNorm n ω E sigma a Y ≤ |a|/sigma+(1/sigma)*
      graphHeight (D.spectralRegularGraph n ω) (spectralParameter E (D.verticalMicroscopicEta n sigma Y)) := by
  have he := D.microscopicCountingState_scalar n ω E sigma a hsigma (verticalMicroscopicPoint Y)
  change anchoredNevanlinna (D.microscopicCountingState n ω E sigma a) _= _ at he
  unfold microscopicVerticalNorm
  change ‖anchoredNevanlinna (D.microscopicCountingState n ω E sigma a) (verticalMicroscopicPoint Y).1‖ ≤ _
  rw [he,microscopicScalar,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hsigma,
    D.microscopicParameter_vertical n E sigma hsigma Y]
  have hh := norm_sub_le (D.scalarResolvent n ω (spectralParameter E (D.verticalMicroscopicEta n sigma Y))) (a : ℂ)
  simp only [Complex.norm_real,Real.norm_eq_abs] at hh
  refine (div_le_div_of_nonneg_right hh hsigma.le).trans_eq ?_
  change (‖D.scalarResolvent n ω _‖+|a|)/sigma=|a|/sigma+(1/sigma)*‖graphNormalizedScalar (D.simpleGraph n ω) _‖
  rw [D.graphNormalizedScalar_simpleGraph n ω]
  ring

theorem microscopicVerticalNorm_zero_anchor (n : ℕ) (ω : Ω) (E sigma a : ℝ) :
    D.microscopicVerticalNorm n ω E sigma a 0=‖(D.microscopicCountingState n ω E sigma a).val.2‖ := by
  simp only [microscopicVerticalNorm,Nat.cast_zero,zero_add,Complex.ofReal_one,one_mul,anchoredNevanlinna_I]

end GeneralizedBulk.External.RegularSpectralData
