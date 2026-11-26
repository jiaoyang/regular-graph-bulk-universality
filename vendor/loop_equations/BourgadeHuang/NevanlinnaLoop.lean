import BourgadeHuang.NevanlinnaContinuity
import BourgadeHuang.NevanlinnaAnalytic

/-!
# Continuous loop observables of anchored counting states

Weighted inverse powers have uniformly negligible tails on bounded sets of anchors.
This gives genuine continuous derivatives and repeated-parameter interactions,
with exact agreement on every finite particle configuration.
-/
noncomputable section
open scoped BigOperators Topology CompactlySupported
open MeasureTheory Filter
namespace BourgadeHuang

private def weightedKernelCutoff (f : ℝ → ℂ) (hf : Continuous f) (R : ℝ) : ℝ →C_c ℂ :=
  ⟨⟨fun a => (compactIntervalCutoff R a : ℂ) * f a,
    (Complex.continuous_ofReal.comp (compactIntervalCutoff R).continuous).mul hf⟩,
    HasCompactSupport.intro' isCompact_Icc isClosed_Icc (fun a ha => by
      change (intervalCutoff R a : ℂ) * f a = 0
      rw [intervalCutoff_eq_zero ha, Complex.ofReal_zero, zero_mul])⟩

/-- Continuous kernels which decay relative to the Nevanlinna weight give
continuous statistics on the valid anchored state space. -/
theorem continuous_integral_of_weighted_decay (f : ℝ → ℂ) (hf : Continuous f)
    (hbound : ∃ C : ℝ, ∀ a, ‖f a‖ ≤ C * nevanlinnaWeight a)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
      ∀ a, R ≤ |a| → ‖f a‖ ≤ ε * nevanlinnaWeight a) :
    Continuous (fun s : AnchoredCountingState => ∫ a, f a ∂s.val.1.measure) := by
  obtain ⟨C, hC⟩ := hbound
  have hi (s : AnchoredCountingState) : Integrable f s.val.1.measure :=
    Integrable.mono' (s.integrable_weight.const_mul C) hf.aestronglyMeasurable
      (Filter.Eventually.of_forall hC)
  have hcut (ε R : ℝ) (hε : 0 ≤ ε)
      (hR : ∀ a, R ≤ |a| → ‖f a‖ ≤ ε * nevanlinnaWeight a)
      (s : AnchoredCountingState) :
      ‖(∫ a, f a ∂s.val.1.measure) -
        ∫ a, weightedKernelCutoff f hf R a ∂s.val.1.measure‖ ≤ ε * s.val.2.im := by
    have hc : Integrable (fun a => weightedKernelCutoff f hf R a) s.val.1.measure :=
      (weightedKernelCutoff f hf R).continuous.integrable_of_hasCompactSupport
        (weightedKernelCutoff f hf R).hasCompactSupport
    have hb (a : ℝ) : ‖f a - weightedKernelCutoff f hf R a‖ ≤ ε * nevanlinnaWeight a := by
      by_cases ha : a ∈ Set.Icc (-R) R
      · change ‖f a - (intervalCutoff R a : ℂ) * f a‖ ≤ _
        rw [intervalCutoff_eq_one ha]
        simp only [Complex.ofReal_one, one_mul, sub_self, norm_zero]
        exact mul_nonneg hε (nevanlinnaWeight_nonneg a)
      · have hlarge : R ≤ |a| := (lt_of_not_ge (fun hh => ha (abs_le.mp hh))).le
        have hsmall : |1 - intervalCutoff R a| ≤ 1 := by
          rw [abs_of_nonneg (sub_nonneg.mpr (intervalCutoff_mem_Icc R a).2)]
          linarith [(intervalCutoff_mem_Icc R a).1]
        have heq : f a - weightedKernelCutoff f hf R a =
            ((1 - intervalCutoff R a : ℝ) : ℂ) * f a := by
          simp only [weightedKernelCutoff, CompactlySupportedContinuousMap.coe_mk,
            ContinuousMap.coe_mk, compactIntervalCutoff, Complex.ofReal_sub, Complex.ofReal_one]
          ring
        rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact (mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)).trans
          (by simpa only [one_mul] using hR a hlarge)
    rw [← integral_sub (hi s) hc]
    calc
      _ ≤ ∫ a, ‖f a - weightedKernelCutoff f hf R a‖ ∂s.val.1.measure := norm_integral_le_integral_norm _
      _ ≤ ∫ a, ε * nevanlinnaWeight a ∂s.val.1.measure :=
        integral_mono ((hi s).sub hc).norm (s.integrable_weight.const_mul ε) hb
      _ = ε * ∫ a, nevanlinnaWeight a ∂s.val.1.measure := integral_const_mul _ _
      _ ≤ ε * s.val.2.im := mul_le_mul_of_nonneg_left s.integral_weight_le_im hε
  rw [continuous_iff_continuousAt]
  intro s
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let M : ℝ := ‖s.val.2‖ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  let δ : ℝ := ε / (6 * M)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨R, _, hR⟩ := htail δ hδ
  have hsmall : δ * M = ε / 6 := by dsimp [δ]; field_simp; ring
  have hanchor : ∀ᶠ t : AnchoredCountingState in 𝓝 s, ‖t.val.2‖ < M :=
    (continuous_norm.comp (continuous_snd.comp continuous_subtype_val)).continuousAt
      (gt_mem_nhds (by dsimp [M]; linarith))
  have hc : Continuous (fun t : AnchoredCountingState =>
      ∫ a, weightedKernelCutoff f hf R a ∂t.val.1.measure) :=
    (continuous_complexLinearStatistic _).comp (continuous_fst.comp continuous_subtype_val)
  have hnear := Metric.tendsto_nhds.mp (hc.continuousAt (x := s)) (ε / 3) (by positivity)
  filter_upwards [hanchor, hnear] with t ht hdist
  have hta := (hcut δ R hδ.le hR t).trans
    (mul_le_mul_of_nonneg_left ((Complex.im_le_norm _).trans ht.le) hδ.le)
  have hsa := (hcut δ R hδ.le hR s).trans
    (mul_le_mul_of_nonneg_left ((Complex.im_le_norm _).trans
      (by dsimp [M]; linarith : ‖s.val.2‖ ≤ M)) hδ.le)
  have htri := dist_triangle4
    (∫ a, f a ∂t.val.1.measure)
    (∫ a, weightedKernelCutoff f hf R a ∂t.val.1.measure)
    (∫ a, weightedKernelCutoff f hf R a ∂s.val.1.measure)
    (∫ a, f a ∂s.val.1.measure)
  rw [dist_eq_norm] at hdist ⊢
  simp only [dist_eq_norm] at htri
  rw [norm_sub_rev (∫ a, weightedKernelCutoff f hf R a ∂s.val.1.measure)] at htri
  rw [hsmall] at hta hsa
  linarith only [hta, hsa, htri, hdist, hε]

/-- The weighted inverse power of order `q+1`. -/
def anchoredPowerKernel (q : ℕ) (z : ℂ) (a : ℝ) : ℂ :=
  (nevanlinnaWeight a : ℂ) * (((a : ℂ) - z)⁻¹) ^ (q + 1)

def anchoredPowerIntegral (q : ℕ) (s : AnchoredCountingState) (z : ℂ) : ℂ :=
  ∫ a, anchoredPowerKernel q z a ∂s.val.1.measure

theorem continuous_anchoredPowerKernel (q : ℕ) {z : ℂ} (hz : z.im ≠ 0) :
    Continuous (anchoredPowerKernel q z) :=
  (Complex.continuous_ofReal.comp continuous_nevanlinnaWeight).mul
    (((Complex.continuous_ofReal.sub continuous_const).inv₀
      (fun a => real_sub_ne_zero a hz)).pow (q + 1))

theorem norm_anchoredPowerKernel_le (q : ℕ) {z : ℂ} (hz : z.im ≠ 0) (a : ℝ) :
    ‖anchoredPowerKernel q z a‖ ≤ (1 / |z.im|) ^ (q + 1) * nevanlinnaWeight a := by
  simp only [anchoredPowerKernel, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (nevanlinnaWeight_nonneg a)]
  exact (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (norm_reciprocal_le_im a hz) (q + 1))
    (nevanlinnaWeight_nonneg a)).trans_eq (by ring)

theorem integrable_anchoredPowerKernel (q : ℕ) (s : AnchoredCountingState)
    {z : ℂ} (hz : z.im ≠ 0) : Integrable (anchoredPowerKernel q z) s.val.1.measure :=
  Integrable.mono' (s.integrable_weight.const_mul _) (continuous_anchoredPowerKernel q hz).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_anchoredPowerKernel_le q hz))

theorem norm_anchoredPowerIntegral_le (q : ℕ) (s : AnchoredCountingState)
    {z : ℂ} (hz : z.im ≠ 0) :
    ‖anchoredPowerIntegral q s z‖ ≤ (1 / |z.im|) ^ (q + 1) * ‖s.val.2‖ := by
  calc
    _ ≤ ∫ a, ‖anchoredPowerKernel q z a‖ ∂s.val.1.measure := norm_integral_le_integral_norm _
    _ ≤ ∫ a, (1 / |z.im|) ^ (q + 1) * nevanlinnaWeight a ∂s.val.1.measure :=
      integral_mono (integrable_anchoredPowerKernel q s hz).norm
        (s.integrable_weight.const_mul _) (norm_anchoredPowerKernel_le q hz)
    _ = (1 / |z.im|) ^ (q + 1) * ∫ a, nevanlinnaWeight a ∂s.val.1.measure := integral_const_mul _ _
    _ ≤ (1 / |z.im|) ^ (q + 1) * ‖s.val.2‖ :=
      mul_le_mul_of_nonneg_left (s.integral_weight_le_im.trans (Complex.im_le_norm _)) (by positivity)

theorem continuous_anchoredPowerIntegral (q : ℕ) {z : ℂ} (hz : z.im ≠ 0) :
    Continuous (fun s : AnchoredCountingState => anchoredPowerIntegral q s z) := by
  apply continuous_integral_of_weighted_decay _ (continuous_anchoredPowerKernel q hz)
    ⟨_, norm_anchoredPowerKernel_le q hz⟩
  intro ε hε
  let D : ℝ := (1 / |z.im|) ^ q
  have hD : 0 < D := by dsimp [D]; positivity
  let R := max (2 * ‖z‖ + 1) (2 * D / ε + 1)
  have hR : 0 < R := lt_of_lt_of_le (by positivity : 0 < 2 * ‖z‖ + 1) (le_max_left _ _)
  have hzR : 2 * ‖z‖ ≤ R := by dsimp [R]; linarith [le_max_left (2 * ‖z‖ + 1) (2 * D / ε + 1)]
  have hsmall : (2 / R) * D ≤ ε := by
    have hh : 2 * D / ε ≤ R := (le_add_of_nonneg_right (by norm_num : (0:ℝ) ≤ 1)).trans (le_max_right _ _)
    have hh' := (div_le_iff₀ hε).mp hh
    rw [div_mul_eq_mul_div, div_le_iff₀ hR]
    nlinarith only [hh']
  refine ⟨R, hR, ?_⟩
  intro a ha
  have hinv := norm_reciprocal_le_two_div_of_large_real a z hR hzR ha
  have hpow := pow_le_pow_left₀ (norm_nonneg _) (norm_reciprocal_le_im a hz) q
  have hb : ‖((a : ℂ) - z)⁻¹‖ ^ (q + 1) ≤ ε := by
    rw [pow_succ]
    exact (mul_le_mul hpow hinv (norm_nonneg _) (by dsimp [D] at hD; positivity)).trans
      (by simpa only [mul_comm] using hsmall)
  simp only [anchoredPowerKernel, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (nevanlinnaWeight_nonneg a)]
  exact (mul_le_mul_of_nonneg_left hb (nevanlinnaWeight_nonneg a)).trans_eq (by ring)

/-- First derivative of the reconstructed function. -/
def anchoredDerivative (s : AnchoredCountingState) (z : ℂ) : ℂ :=
  (s.val.2.im : ℂ) + 2 * z * anchoredPowerIntegral 0 s z +
    (1 + z ^ 2) * anchoredPowerIntegral 1 s z

/-- Half the second derivative, which also represents the diagonal interaction. -/
def anchoredSecondHalf (s : AnchoredCountingState) (z : ℂ) : ℂ :=
  anchoredPowerIntegral 0 s z + 2 * z * anchoredPowerIntegral 1 s z +
    (1 + z ^ 2) * anchoredPowerIntegral 2 s z

/-- Analytically extended interaction, including repeated parameters. -/
def anchoredInteraction (s : AnchoredCountingState) (w v : ℂ) : ℂ :=
  if w = v then anchoredSecondHalf s w else
    ((anchoredNevanlinna s w - anchoredNevanlinna s v) -
      (w - v) * anchoredDerivative s v) / (w - v) ^ 2

theorem continuous_anchoredDerivative {z : ℂ} (hz : z.im ≠ 0) :
    Continuous (fun s : AnchoredCountingState => anchoredDerivative s z) := by
  exact ((Complex.continuous_ofReal.comp (Complex.continuous_im.comp
    (continuous_snd.comp continuous_subtype_val))).add
    (continuous_const.mul (continuous_anchoredPowerIntegral 0 hz))).add
    (continuous_const.mul (continuous_anchoredPowerIntegral 1 hz))

theorem continuous_anchoredSecondHalf {z : ℂ} (hz : z.im ≠ 0) :
    Continuous (fun s : AnchoredCountingState => anchoredSecondHalf s z) := by
  exact ((continuous_anchoredPowerIntegral 0 hz).add
    (continuous_const.mul (continuous_anchoredPowerIntegral 1 hz))).add
    (continuous_const.mul (continuous_anchoredPowerIntegral 2 hz))

theorem continuous_anchoredInteraction {w v : ℂ} (hw : w.im ≠ 0) (hv : v.im ≠ 0) :
    Continuous (fun s : AnchoredCountingState => anchoredInteraction s w v) := by
  unfold anchoredInteraction
  split_ifs
  · exact continuous_anchoredSecondHalf hw
  · exact (((continuous_anchoredNevanlinna hw).sub (continuous_anchoredNevanlinna hv)).sub
      (continuous_const.mul (continuous_anchoredDerivative hv))).div_const _


/-- The explicit reconstructed derivative is the complex derivative. -/
theorem hasDerivAt_anchoredNevanlinna (s : AnchoredCountingState)
    {z : ℂ} (hz : z.im ≠ 0) :
    HasDerivAt (anchoredNevanlinna s) (anchoredDerivative s z) z := by
  have hh := ((hasDerivAt_const z (s.val.2.re : ℂ)).add
    ((hasDerivAt_id z).mul_const (s.val.2.im : ℂ))).add
    (((hasDerivAt_const z (1 : ℂ)).add ((hasDerivAt_id z).pow 2)).mul
      (hasDerivAt_integral_anchoredResolventKernel s hz))
  convert hh using 1
  simp only [anchoredDerivative, anchoredPowerIntegral, anchoredPowerKernel,
    anchoredResolventDerivativeKernel, anchoredResolventKernel, zero_add, mul_one,
    pow_one, Nat.cast_ofNat, div_eq_mul_inv, id_eq]
  ring

private theorem reciprocal_sq_anchor (a : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    (((a : ℂ) - z)⁻¹) ^ 2 = (nevanlinnaWeight a : ℂ) +
      2 * z * anchoredPowerKernel 0 z a + (1 + z ^ 2) * anchoredPowerKernel 1 z a := by
  have ha : (1 + a ^ 2 : ℝ) ≠ 0 := by positivity
  have ha' : (1 + (a : ℂ) ^ 2) ≠ 0 := by exact_mod_cast ha
  simp only [anchoredPowerKernel, nevanlinnaWeight, Complex.ofReal_inv,
    Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_pow]
  field_simp [ha', real_sub_ne_zero a hz]
  <;> ring

private theorem reciprocal_cube_anchor (a : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    (((a : ℂ) - z)⁻¹) ^ 3 = anchoredPowerKernel 0 z a +
      2 * z * anchoredPowerKernel 1 z a + (1 + z ^ 2) * anchoredPowerKernel 2 z a := by
  have ha : (1 + a ^ 2 : ℝ) ≠ 0 := by positivity
  have ha' : (1 + (a : ℂ) ^ 2) ≠ 0 := by exact_mod_cast ha
  simp only [anchoredPowerKernel, nevanlinnaWeight, Complex.ofReal_inv,
    Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_pow]
  field_simp [ha', real_sub_ne_zero a hz]
  <;> ring

theorem anchoredPowerIntegral_eq_finite (q : ℕ) {N : ℕ} (x : Fin N → ℝ) (center : ℝ)
    (ξ : LocalCountingMeasure) (hξ : ξ.measure = ∑ i, Measure.dirac (x i)) (z : ℂ) :
    anchoredPowerIntegral q
      ⟨(ξ, microscopicResolvent x center Complex.I), validAnchoredCountingState_finite x center ξ hξ⟩ z =
      ∑ i, anchoredPowerKernel q z (x i) := by
  rw [anchoredPowerIntegral, hξ, integral_finset_sum_measure (fun _ _ => integrable_dirac)]
  simp only [integral_dirac]

theorem anchoredDerivative_eq_finite {N : ℕ} (x : Fin N → ℝ) (center : ℝ)
    (ξ : LocalCountingMeasure) (hξ : ξ.measure = ∑ i, Measure.dirac (x i))
    {z : ℂ} (hz : z.im ≠ 0) :
    anchoredDerivative
      ⟨(ξ, microscopicResolvent x center Complex.I), validAnchoredCountingState_finite x center ξ hξ⟩ z =
      resolventDerivative x z := by
  simp only [anchoredDerivative, anchoredPowerIntegral_eq_finite 0 x center ξ hξ,
    anchoredPowerIntegral_eq_finite 1 x center ξ hξ,
    microscopicResolvent_im_I_eq_weight, Complex.ofReal_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib, resolventDerivative]
  exact Finset.sum_congr rfl (fun i _ => (reciprocal_sq_anchor (x i) hz).symm)

theorem anchoredSecondHalf_eq_finite {N : ℕ} (x : Fin N → ℝ) (center : ℝ)
    (ξ : LocalCountingMeasure) (hξ : ξ.measure = ∑ i, Measure.dirac (x i))
    {z : ℂ} (hz : z.im ≠ 0) :
    anchoredSecondHalf
      ⟨(ξ, microscopicResolvent x center Complex.I), validAnchoredCountingState_finite x center ξ hξ⟩ z =
      interaction x z z := by
  simp only [anchoredSecondHalf, anchoredPowerIntegral_eq_finite 0 x center ξ hξ,
    anchoredPowerIntegral_eq_finite 1 x center ξ hξ, anchoredPowerIntegral_eq_finite 2 x center ξ hξ,
    Finset.mul_sum, ← Finset.sum_add_distrib, interaction_diagonal]
  exact Finset.sum_congr rfl (fun i _ => (reciprocal_cube_anchor (x i) hz).symm)

theorem anchoredInteraction_eq_finite {N : ℕ} (x : Fin N → ℝ) (center : ℝ)
    (ξ : LocalCountingMeasure) (hξ : ξ.measure = ∑ i, Measure.dirac (x i))
    {w v : ℂ} (hw : w.im ≠ 0) (hv : v.im ≠ 0) :
    anchoredInteraction
      ⟨(ξ, microscopicResolvent x center Complex.I), validAnchoredCountingState_finite x center ξ hξ⟩ w v =
      interaction x w v := by
  unfold anchoredInteraction
  split_ifs with he
  · subst v
    exact anchoredSecondHalf_eq_finite x center ξ hξ hw
  · rw [anchoredNevanlinna_eq_finite x center ξ hξ hw,
      anchoredNevanlinna_eq_finite x center ξ hξ hv,
      anchoredDerivative_eq_finite x center ξ hξ hv]
    exact (interaction_eq_quotient x center hw hv he).symm

/-- The actual reconstructed loop polynomial, including coincident parameters. -/
def anchoredLoopIntegrand {n : ℕ} (β : Beta) (s : AnchoredCountingState)
    (w : ℂ) (aux : Fin n → ℂ) : ℂ :=
  (((2 - β.value) / β.value) * anchoredDerivative s w +
      anchoredNevanlinna s w ^ 2 + 1) *
    (∏ a, anchoredNevanlinna s (aux a)) +
    (2 / β.value) * ∑ a, anchoredInteraction s w (aux a) *
      excludedProduct (fun b => anchoredNevanlinna s (aux b)) a

theorem continuous_anchoredLoopIntegrand {n : ℕ} (β : Beta)
    {w : ℂ} {aux : Fin n → ℂ} (hw : w.im ≠ 0) (haux : ∀ a, (aux a).im ≠ 0) :
    Continuous (fun s : AnchoredCountingState => anchoredLoopIntegrand β s w aux) := by
  unfold anchoredLoopIntegrand excludedProduct
  exact ((((continuous_const.mul (continuous_anchoredDerivative hw)).add
    ((continuous_anchoredNevanlinna hw).pow 2)).add continuous_const).mul
    (continuous_finset_prod _ (fun a _ => continuous_anchoredNevanlinna (haux a)))).add
    (continuous_const.mul (continuous_finset_sum _ (fun a _ =>
      (continuous_anchoredInteraction hw (haux a)).mul
        (continuous_finset_prod _ (fun b _ => continuous_anchoredNevanlinna (haux b))))))

theorem anchoredLoopIntegrand_eq_finite {n N : ℕ} (β : Beta) (x : Fin N → ℝ) (center : ℝ)
    (ξ : LocalCountingMeasure) (hξ : ξ.measure = ∑ i, Measure.dirac (x i))
    {w : ℂ} {aux : Fin n → ℂ} (hw : w.im ≠ 0) (haux : ∀ a, (aux a).im ≠ 0) :
    anchoredLoopIntegrand β
      ⟨(ξ, microscopicResolvent x center Complex.I), validAnchoredCountingState_finite x center ξ hξ⟩ w aux =
      loopIntegrand β x center w aux := by
  unfold anchoredLoopIntegrand loopIntegrand excludedProduct
  simp only [anchoredNevanlinna_eq_finite x center ξ hξ hw,
    anchoredNevanlinna_eq_finite x center ξ hξ (haux _),
    anchoredDerivative_eq_finite x center ξ hξ hw,
    anchoredInteraction_eq_finite x center ξ hξ hw (haux _)]

end BourgadeHuang
