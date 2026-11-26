import GeneralizedBulk.Graph.MicroscopicHeightBounds
import GeneralizedBulk.Graph.BulkTruncationVariance

/-! A larger cutoff Poisson trace is controlled by an integer-height trace.
This allows the actual capped scalar estimates at integer heights to control
arbitrary atom-free window radii. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped Topology BigOperators
namespace GeneralizedBulk.External.RegularSpectralData
open Graph
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

theorem realPoissonKernel_div_height_antitone (E x step Y R : ℝ)
    (hstep : 0 < step) (hY : 0 < Y) (hYR : Y ≤ R) :
    realPoissonKernel E (step*R) x/R ≤ realPoissonKernel E (step*Y) x/Y := by
  have hR : 0 < R := hY.trans_le hYR
  have hdy : 0 < (x-E)^2+(step*Y)^2 := by positivity
  have hdr : (x-E)^2+(step*Y)^2 ≤ (x-E)^2+(step*R)^2 := by
    have hm := mul_le_mul_of_nonneg_left hYR hstep.le
    nlinarith [mul_pos hstep hY,mul_pos hstep hR]
  have heq (t : ℝ) (ht : t ≠ 0) : realPoissonKernel E (step*t) x/t =
      step/((x-E)^2+(step*t)^2) := by
    dsimp [realPoissonKernel]
    calc
      _ = (step/((x-E)^2+(step*t)^2))*(t/t) := by ring
      _ = _ := by rw [div_self ht,mul_one]
  rw [heq R hR.ne',heq Y hY.ne']
  exact div_le_div_of_nonneg_left hstep.le hdy hdr

theorem scalarPoissonTrace_div_cutoff_le (n : ℕ) (ω : Ω) (E step Y R : ℝ)
    (hstep : 0 < step) (hY : 0 < Y) (hYR : Y ≤ R) :
    (D.scalarResolvent n ω (spectralParameter E (step*R))).im/R ≤
      (D.scalarResolvent n ω (spectralParameter E (step*Y))).im/Y := by
  have hR : 0 < R := hY.trans_le hYR
  rw [D.scalarResolvent_poisson n ω E (step*R) (mul_pos hstep hR).ne',
    D.scalarResolvent_poisson n ω E (step*Y) (mul_pos hstep hY).ne']
  calc
    _ = (N n : ℝ)⁻¹ * ∑ k,realPoissonKernel E (step*R) (D.eigenvalue n ω k)/R := by
      rw [← Finset.sum_div]
      ring
    _ ≤ (N n : ℝ)⁻¹ * ∑ k,realPoissonKernel E (step*Y) (D.eigenvalue n ω k)/Y := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
      exact Finset.sum_le_sum (fun k _ => realPoissonKernel_div_height_antitone E _ step Y R hstep hY hYR)
    _ = _ := by rw [← Finset.sum_div]; ring

/-- The first term in the actual truncation variance is bounded by the
actual microscopic scalar norm at integer height Y+1, uniformly in every
larger real cutoff R. The real centering drops out of the imaginary part. -/
theorem cutoffPoissonTrace_le_verticalNorm (n : ℕ) (ω : Ω) (E sigma center R : ℝ)
    (hsigma : 0 < sigma) (Y : ℕ) (hYR : (Y:ℝ)+1 ≤ R) :
    (32*sigma/R)*(D.scalarResolvent n ω
      (spectralParameter E (microscopicStep (N n) sigma*R))).im ≤
      (32*sigma^2/((Y:ℝ)+1))*D.microscopicVerticalNorm n ω E sigma center Y := by
  have hY : 0 < (Y:ℝ)+1 := by positivity
  have ht := D.scalarPoissonTrace_div_cutoff_le n ω E (microscopicStep (N n) sigma)
    ((Y:ℝ)+1) R (microscopicStep_pos (N n) (D.size_pos n) sigma hsigma) hY hYR
  have hs : D.scalarResolvent n ω
      (spectralParameter E (microscopicStep (N n) sigma*((Y:ℝ)+1))) =
      (center:ℂ)+(sigma:ℂ)*anchoredNevanlinna
        (D.microscopicCountingState n ω E sigma center) (verticalMicroscopicPoint Y).val := by
    rw [D.microscopicCountingState_scalar n ω E sigma center hsigma (verticalMicroscopicPoint Y),
      microscopicScalar,D.microscopicParameter_vertical n E sigma hsigma Y]
    have he : D.verticalMicroscopicEta n sigma Y = microscopicStep (N n) sigma*((Y:ℝ)+1) := by
      dsimp [verticalMicroscopicEta,microscopicStep]
    rw [he]
    field_simp [Complex.ofReal_ne_zero.mpr hsigma.ne']
  have hnorm : (D.scalarResolvent n ω
      (spectralParameter E (microscopicStep (N n) sigma*((Y:ℝ)+1)))).im ≤
      sigma*D.microscopicVerticalNorm n ω E sigma center Y := by
    rw [hs]
    simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
      zero_mul,zero_add,add_zero]
    exact mul_le_mul_of_nonneg_left (Complex.im_le_norm _) hsigma.le
  have hh := mul_le_mul_of_nonneg_left
    (ht.trans (div_le_div_of_nonneg_right hnorm hY.le)) (show 0 ≤ 32*sigma by positivity)
  convert hh using 1 <;> ring

end GeneralizedBulk.External.RegularSpectralData
