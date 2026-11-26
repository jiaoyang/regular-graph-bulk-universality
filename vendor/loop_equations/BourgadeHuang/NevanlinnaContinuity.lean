import BourgadeHuang.NevanlinnaState

/-!
# Continuity of anchored Nevanlinna reconstruction

Compact cutoff kernels are vague-continuous. Their omitted tails are bounded
by the imaginary anchor times `2/R`, uniformly on bounded sets of anchors.
Consequently the actual reconstructed resolvent is continuous on the closed
state space at each off-real parameter.
-/
noncomputable section
open scoped BigOperators Topology CompactlySupported
open MeasureTheory Filter
namespace BourgadeHuang

/-- Complex compact statistics are continuous by their real and imaginary parts. -/
theorem continuous_complexLinearStatistic (f : ℝ →C_c ℂ) :
    Continuous (fun ξ : LocalCountingMeasure => ∫ a, f a ∂ξ.measure) := by
  let fr : ℝ →C_c ℝ := ⟨⟨fun a => (f a).re, Complex.continuous_re.comp f.continuous⟩,
    HasCompactSupport.intro' f.hasCompactSupport (isClosed_tsupport f)
      (fun a ha => by simp [image_eq_zero_of_nmem_tsupport ha])⟩
  let fi : ℝ →C_c ℝ := ⟨⟨fun a => (f a).im, Complex.continuous_im.comp f.continuous⟩,
    HasCompactSupport.intro' f.hasCompactSupport (isClosed_tsupport f)
      (fun a ha => by simp [image_eq_zero_of_nmem_tsupport ha])⟩
  have h := (Complex.continuous_ofReal.comp (continuous_linearStatistic fr)).add
    ((Complex.continuous_ofReal.comp (continuous_linearStatistic fi)).mul
      (continuous_const : Continuous (fun _ : LocalCountingMeasure => Complex.I)))
  convert h using 1
  funext ξ
  exact (integral_re_add_im
    (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport)).symm

/-- Far from a bounded complex parameter, the reciprocal has its `1/|a|` decay. -/
theorem norm_reciprocal_le_two_div_of_large_real (a : ℝ) (z : ℂ)
    {R : ℝ} (hR : 0 < R) (hzR : 2 * ‖z‖ ≤ R) (ha : R ≤ |a|) :
    ‖((a : ℂ) - z)⁻¹‖ ≤ 2 / R := by
  have hn := norm_sub_norm_le (a : ℂ) z
  rw [Complex.norm_real, Real.norm_eq_abs] at hn
  have hl : R / 2 ≤ ‖(a : ℂ) - z‖ := by linarith
  have hh := one_div_le_one_div_of_le (half_pos hR) hl
  rw [norm_inv]
  calc
    _ = 1 / ‖(a : ℂ) - z‖ := (one_div _).symm
    _ ≤ 1 / (R / 2) := hh
    _ = 2 / R := by ring

/-- A compactly supported complex kernel for vague testing. -/
def anchoredKernelCutoff (z : ℂ) (hz : z.im ≠ 0) (R : ℝ) : ℝ →C_c ℂ :=
  ⟨⟨fun a => (compactIntervalCutoff R a : ℂ) * anchoredResolventKernel z a,
    (Complex.continuous_ofReal.comp (compactIntervalCutoff R).continuous).mul
      (continuous_anchoredResolventKernel hz)⟩,
    HasCompactSupport.intro' isCompact_Icc isClosed_Icc (fun a ha => by
      change (intervalCutoff R a : ℂ) * anchoredResolventKernel z a = 0
      rw [intervalCutoff_eq_zero ha, Complex.ofReal_zero, zero_mul])⟩

/-- The omitted tail is dominated by a vanishing multiple of the Nevanlinna weight. -/
theorem norm_anchoredKernel_sub_cutoff_le (z : ℂ) (hz : z.im ≠ 0)
    {R : ℝ} (hR : 0 < R) (hzR : 2 * ‖z‖ ≤ R) (a : ℝ) :
    ‖anchoredResolventKernel z a - anchoredKernelCutoff z hz R a‖ ≤
      (2 / R) * nevanlinnaWeight a := by
  by_cases ha : a ∈ Set.Icc (-R) R
  · change ‖anchoredResolventKernel z a -
      (intervalCutoff R a : ℂ) * anchoredResolventKernel z a‖ ≤ _
    rw [intervalCutoff_eq_one ha]
    simp only [Complex.ofReal_one, one_mul, sub_self, norm_zero]
    exact mul_nonneg (by positivity) (nevanlinnaWeight_nonneg a)
  · have hlarge : R ≤ |a| := (lt_of_not_ge (fun hh => ha (abs_le.mp hh))).le
    have hcut : |1 - intervalCutoff R a| ≤ 1 := by
      rw [abs_of_nonneg (sub_nonneg.mpr (intervalCutoff_mem_Icc R a).2)]
      linarith [(intervalCutoff_mem_Icc R a).1]
    have hEq : anchoredResolventKernel z a - anchoredKernelCutoff z hz R a =
        ((1 - intervalCutoff R a : ℝ) : ℂ) * anchoredResolventKernel z a := by
      simp only [anchoredKernelCutoff, CompactlySupportedContinuousMap.coe_mk,
        ContinuousMap.coe_mk, Complex.ofReal_sub, Complex.ofReal_one, compactIntervalCutoff]
      ring
    rw [hEq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ 1 * ‖anchoredResolventKernel z a‖ :=
        mul_le_mul_of_nonneg_right hcut (norm_nonneg _)
      _ ≤ (2 / R) * nevanlinnaWeight a := by
        simp only [one_mul, anchoredResolventKernel, div_eq_mul_inv, norm_mul,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (nevanlinnaWeight_nonneg a)]
        exact (mul_le_mul_of_nonneg_left
          (norm_reciprocal_le_two_div_of_large_real a z hR hzR hlarge)
          (nevanlinnaWeight_nonneg a)).trans_eq (by ring)

/-- The integral tail is controlled by the anchor, uniformly over valid states. -/
theorem norm_integral_anchoredKernel_sub_cutoff_le (s : AnchoredCountingState)
    (z : ℂ) (hz : z.im ≠ 0) {R : ℝ} (hR : 0 < R) (hzR : 2 * ‖z‖ ≤ R) :
    ‖(∫ a, anchoredResolventKernel z a ∂s.val.1.measure) -
      ∫ a, anchoredKernelCutoff z hz R a ∂s.val.1.measure‖ ≤ (2 / R) * s.val.2.im := by
  have hi := integrable_anchoredResolventKernel s.val.1.measure s.integrable_weight hz
  have hc : Integrable (fun a => anchoredKernelCutoff z hz R a) s.val.1.measure :=
    (anchoredKernelCutoff z hz R).continuous.integrable_of_hasCompactSupport
      (anchoredKernelCutoff z hz R).hasCompactSupport
  rw [← integral_sub hi hc]
  calc
    _ ≤ ∫ a, ‖anchoredResolventKernel z a - anchoredKernelCutoff z hz R a‖ ∂s.val.1.measure :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ a, (2 / R) * nevanlinnaWeight a ∂s.val.1.measure :=
      integral_mono (hi.sub hc).norm (s.integrable_weight.const_mul _)
        (norm_anchoredKernel_sub_cutoff_le z hz hR hzR)
    _ = (2 / R) * ∫ a, nevanlinnaWeight a ∂s.val.1.measure := integral_const_mul _ _
    _ ≤ (2 / R) * s.val.2.im :=
      mul_le_mul_of_nonneg_left s.integral_weight_le_im (by positivity)

/-- The decaying-kernel integral is continuous on the full closed state space. -/
theorem continuous_integral_anchoredResolventKernel {z : ℂ} (hz : z.im ≠ 0) :
    Continuous (fun s : AnchoredCountingState =>
      ∫ a, anchoredResolventKernel z a ∂s.val.1.measure) := by
  rw [continuous_iff_continuousAt]
  intro s
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let M : ℝ := ‖s.val.2‖ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  let R : ℝ := max (2 * ‖z‖ + 1) (12 * M / ε + 1)
  have hR : 0 < R := lt_of_lt_of_le (by positivity : 0 < 2 * ‖z‖ + 1) (le_max_left _ _)
  have hzR : 2 * ‖z‖ ≤ R := by dsimp [R]; linarith [le_max_left (2 * ‖z‖ + 1) (12 * M / ε + 1)]
  have hsmall : (2 / R) * M < ε / 3 := by
    have hRR := le_max_right (2 * ‖z‖ + 1) (12 * M / ε + 1)
    change 12 * M / ε + 1 ≤ R at hRR
    have hεR : 12 * M + ε ≤ R * ε := by
      have hh := (div_le_iff₀ hε).mp (by linarith : 12 * M / ε ≤ R - 1)
      nlinarith only [hh]
    rw [div_mul_eq_mul_div, div_lt_iff₀ hR]
    have hh : 6 * M < R * ε := by linarith
    calc
      2 * M = (6 * M) / 3 := by ring
      _ < (R * ε) / 3 := div_lt_div_of_pos_right hh (by norm_num)
      _ = _ := by ring
  have hanchor : ∀ᶠ t : AnchoredCountingState in 𝓝 s, ‖t.val.2‖ < M :=
    (continuous_norm.comp (continuous_snd.comp continuous_subtype_val)).continuousAt
      (gt_mem_nhds (by dsimp [M]; linarith))
  have hc : Continuous (fun t : AnchoredCountingState =>
      ∫ a, anchoredKernelCutoff z hz R a ∂t.val.1.measure) :=
    (continuous_complexLinearStatistic _).comp (continuous_fst.comp continuous_subtype_val)
  have hnear := Metric.tendsto_nhds.mp (hc.continuousAt (x := s)) (ε / 3) (by positivity)
  filter_upwards [hanchor, hnear] with t ht hdist
  have hta := norm_integral_anchoredKernel_sub_cutoff_le t z hz hR hzR
  have hsa := norm_integral_anchoredKernel_sub_cutoff_le s z hz hR hzR
  have htim : t.val.2.im ≤ M := (Complex.im_le_norm _).trans ht.le
  have hsim : s.val.2.im ≤ M := (Complex.im_le_norm _).trans (by dsimp [M]; linarith)
  have hta' := hta.trans (mul_le_mul_of_nonneg_left htim (by positivity : 0 ≤ 2 / R))
  have hsa' := hsa.trans (mul_le_mul_of_nonneg_left hsim (by positivity : 0 ≤ 2 / R))
  have htri := dist_triangle4
    (∫ a, anchoredResolventKernel z a ∂t.val.1.measure)
    (∫ a, anchoredKernelCutoff z hz R a ∂t.val.1.measure)
    (∫ a, anchoredKernelCutoff z hz R a ∂s.val.1.measure)
    (∫ a, anchoredResolventKernel z a ∂s.val.1.measure)
  rw [dist_eq_norm] at hdist ⊢
  simp only [dist_eq_norm] at htri
  rw [norm_sub_rev (∫ a, anchoredKernelCutoff z hz R a ∂s.val.1.measure)] at htri
  linarith

/-- The reconstructed resolvent is a genuine continuous observable of the anchored
counting state, so it can be passed through the joint weak limit. -/
theorem continuous_anchoredNevanlinna {z : ℂ} (hz : z.im ≠ 0) :
    Continuous (fun s : AnchoredCountingState => anchoredNevanlinna s z) := by
  unfold anchoredNevanlinna
  exact ((Complex.continuous_ofReal.comp (Complex.continuous_re.comp
    (continuous_snd.comp continuous_subtype_val))).add
    (continuous_const.mul (Complex.continuous_ofReal.comp (Complex.continuous_im.comp
      (continuous_snd.comp continuous_subtype_val))))).add
    (continuous_const.mul (continuous_integral_anchoredResolventKernel hz))

end BourgadeHuang
