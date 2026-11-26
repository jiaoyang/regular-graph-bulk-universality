import BourgadeHuang.CharacteristicRatioSource

/-! Genuine complex derivatives of the integrated-resolvent characteristic ratio. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang

theorem SameOpenHalfPlane.left_offReal {u v : ℂ} (h : SameOpenHalfPlane u v) : u.im ≠ 0 := by
  rcases h with ⟨h, _⟩ | ⟨h, _⟩
  · exact ne_of_gt h
  · exact ne_of_lt h

theorem SameOpenHalfPlane.right_offReal {u v : ℂ} (h : SameOpenHalfPlane u v) : v.im ≠ 0 := by
  rcases h with ⟨_, h⟩ | ⟨_, h⟩
  · exact ne_of_gt h
  · exact ne_of_lt h

theorem sameOpenHalfPlane_nhds {u v : ℂ} (h : SameOpenHalfPlane u v) :
    {z | SameOpenHalfPlane z v} ∈ 𝓝 u := by
  rcases h with ⟨hu,hv⟩ | ⟨hu,hv⟩
  · apply Filter.mem_of_superset ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hu)
    exact fun z hz => Or.inl ⟨hz,hv⟩
  · apply Filter.mem_of_superset ((isOpen_lt Complex.continuous_im continuous_const).mem_nhds hu)
    exact fun z hz => Or.inr ⟨hz,hv⟩

theorem continuous_nevanlinna_ratioPath (s : AnchoredCountingState)
    {u v : ℂ} (huv : SameOpenHalfPlane u v) :
    Continuous (fun t : RatioInterval => anchoredNevanlinna s (ratioPath u v t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (hasDerivAt_anchoredNevanlinna s (ratioPath_offReal huv t.property)).continuousAt.comp (f := fun t : RatioInterval => ratioPath u v t)
    ((continuous_ratioPath u v).comp continuous_subtype_val).continuousAt

theorem continuous_derivative_ratioPath (s : AnchoredCountingState)
    {u v : ℂ} (huv : SameOpenHalfPlane u v) :
    Continuous (fun t : RatioInterval => anchoredDerivative s (ratioPath u v t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (hasDerivAt_anchoredDerivative s (ratioPath_offReal huv t.property)).continuousAt.comp (f := fun t : RatioInterval => ratioPath u v t)
    ((continuous_ratioPath u v).comp continuous_subtype_val).continuousAt

/-- The fundamental theorem converts the derivative of the straight-path integral
into evaluation at its moving endpoint. -/
theorem integral_ratioPath_endpoint (s : AnchoredCountingState)
    {u v : ℂ} (huv : SameOpenHalfPlane u v) :
    (∫ t : RatioInterval, anchoredNevanlinna s (ratioPath u v t) +
      (u-v)*(t:ℂ)*anchoredDerivative s (ratioPath u v t) ∂ratioIntervalMeasure) =
      anchoredNevanlinna s u := by
  have hd (t : ℝ) (ht : t ∈ Set.uIcc (0:ℝ) 1) :
      HasDerivAt (fun t : ℝ => (t:ℂ)*anchoredNevanlinna s (ratioPath u v t))
        (anchoredNevanlinna s (ratioPath u v t) +
          (u-v)*(t:ℂ)*anchoredDerivative s (ratioPath u v t)) t := by
    have hoff := ratioPath_offReal huv (Set.uIcc_of_le (by norm_num : (0:ℝ)≤1) ▸ ht)
    have hp := (hasDerivAt_const (t:ℂ) v).add ((hasDerivAt_id (t:ℂ)).mul_const (u-v))
    have hf := (hasDerivAt_id (t:ℂ)).mul ((hasDerivAt_anchoredNevanlinna s hoff).comp (t:ℂ) hp)
    convert hf.comp_ofReal using 1
    simp only [Function.comp_apply, zero_add, one_mul, id_eq, ratioPath]
    ring
  have hc : ContinuousOn (fun t : ℝ => anchoredNevanlinna s (ratioPath u v t) +
      (u-v)*(t:ℂ)*anchoredDerivative s (ratioPath u v t)) (Set.uIcc (0:ℝ) 1) := by
    apply ContinuousOn.add
    · intro t ht
      have hoff := ratioPath_offReal huv (Set.uIcc_of_le (by norm_num : (0:ℝ)≤1) ▸ ht)
      exact ((hasDerivAt_anchoredNevanlinna s hoff).continuousAt.comp
        (continuous_ratioPath u v).continuousAt).continuousWithinAt
    · apply ContinuousOn.mul (continuous_const.mul Complex.continuous_ofReal).continuousOn
      intro t ht
      have hoff := ratioPath_offReal huv (Set.uIcc_of_le (by norm_num : (0:ℝ)≤1) ▸ ht)
      exact ((hasDerivAt_anchoredDerivative s hoff).continuousAt.comp
        (continuous_ratioPath u v).continuousAt).continuousWithinAt
  rw [integral_ratioInterval (fun t : ℝ => anchoredNevanlinna s (ratioPath u v t) +
      (u-v)*(t:ℂ)*anchoredDerivative s (ratioPath u v t))]
  simpa [ratioPath] using intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable

/-- Differentiation under the compact path integral is justified by a bound on a
compact tube around the path; the fundamental theorem supplies its derivative. -/
theorem hasDerivAt_integrated_nevanlinna_ratioPath (s : AnchoredCountingState)
    {u v : ℂ} (huv : SameOpenHalfPlane u v) :
    HasDerivAt (fun z => ∫ t : RatioInterval,
      (z-v)*anchoredNevanlinna s (ratioPath z v t) ∂ratioIntervalMeasure)
      (anchoredNevanlinna s u) u := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (sameOpenHalfPlane_nhds huv)
  let R : ℝ := ε/2
  have hR : 0 < R := by dsimp [R]; positivity
  have hclosed (z : ℂ) (hz : z ∈ Metric.closedBall u R) : SameOpenHalfPlane z v :=
    hball (Metric.closedBall_subset_ball (by dsimp [R]; linarith) hz)
  letI : CompactSpace (Metric.closedBall u R) := isCompact_iff_compactSpace.mp (isCompact_closedBall u R)
  let Q := Metric.closedBall u R × RatioInterval
  let P : Q → ℂ := fun p => ratioPath p.1.val v p.2.val
  have hP : Continuous P := by
    exact continuous_const.add ((Complex.continuous_ofReal.comp
      (continuous_subtype_val.comp continuous_snd)).mul
      ((continuous_subtype_val.comp continuous_fst).sub continuous_const))
  have hPoff (p : Q) : (P p).im ≠ 0 := ratioPath_offReal (hclosed _ p.1.property) p.2.property
  have hS : Continuous (fun p : Q => anchoredNevanlinna s (P p)) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (hasDerivAt_anchoredNevanlinna s (hPoff p)).continuousAt.comp hP.continuousAt
  have hD : Continuous (fun p : Q => anchoredDerivative s (P p)) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (hasDerivAt_anchoredDerivative s (hPoff p)).continuousAt.comp hP.continuousAt
  let F := fun z : ℂ => fun t : RatioInterval =>
    (z-v)*anchoredNevanlinna s (ratioPath z v t)
  let F' := fun z : ℂ => fun t : RatioInterval =>
    anchoredNevanlinna s (ratioPath z v t) +
      (z-v)*(t:ℂ)*anchoredDerivative s (ratioPath z v t)
  have hc : Continuous (fun p : Q => F' p.1.val p.2) :=
    hS.add ((((continuous_subtype_val.comp continuous_fst).sub continuous_const).mul
      (Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_snd))).mul hD)
  obtain ⟨C, hC⟩ := isCompact_univ.bddAbove_image hc.norm.continuousOn
  have hFc (z : ℂ) (hz : SameOpenHalfPlane z v) : Continuous (F z) :=
    continuous_const.mul (continuous_nevanlinna_ratioPath s hz)
  have hFdc : Continuous (F' u) := (continuous_nevanlinna_ratioPath s huv).add
    ((continuous_const.mul (Complex.continuous_ofReal.comp continuous_subtype_val)).mul
      (continuous_derivative_ratioPath s huv))
  have hd (z : ℂ) (hz : z ∈ Metric.ball u R) (t : RatioInterval) :
      HasDerivAt (fun z => F z t) (F' z t) z := by
    have hp := (hasDerivAt_const z v).add (((hasDerivAt_id z).sub_const v).const_mul (t:ℂ))
    have hs := (hasDerivAt_anchoredNevanlinna s
      (ratioPath_offReal (hclosed z (Metric.ball_subset_closedBall hz)) t.property)).comp z hp
    convert ((hasDerivAt_id z).sub_const v).mul hs using 1
    simp only [F, F', ratioPath, zero_add, mul_one, one_mul, id_eq, Function.comp_apply]
    ring
  have hh := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ratioIntervalMeasure)
    (F := F) (F' := F') (bound := fun _ : RatioInterval => C) hR
    (Filter.eventually_of_mem (Metric.ball_mem_nhds u hR) (fun z hz =>
      (hFc z (hclosed z (Metric.ball_subset_closedBall hz))).aestronglyMeasurable))
    ((hFc u huv).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    hFdc.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun t z hz =>
      hC ⟨(⟨z, Metric.ball_subset_closedBall hz⟩, t), Set.mem_univ _, rfl⟩))
    (integrable_const C) (Filter.Eventually.of_forall (fun t z hz => hd z hz t))).2
  convert hh using 1
  exact (integral_ratioPath_endpoint s huv).symm

/-- The numerator derivative of the actual limiting ratio inserts the negative
reconstructed resolvent, just as for finite characteristic polynomials. -/
theorem hasDerivAt_anchoredCharacteristicRatio (s : AnchoredCountingState)
    {u v : ℂ} (huv : SameOpenHalfPlane u v) :
    HasDerivAt (fun z => anchoredCharacteristicRatio s z v)
      (-anchoredNevanlinna s u * anchoredCharacteristicRatio s u v) u := by
  have h := (hasDerivAt_integrated_nevanlinna_ratioPath s huv).neg.cexp
  have heq (z : ℂ) : anchoredCharacteristicRatio s z v =
      Complex.exp (-(∫ t : RatioInterval, (z-v)*anchoredNevanlinna s (ratioPath z v t)
        ∂ratioIntervalMeasure)) := by
    simp only [anchoredCharacteristicRatio, neg_mul, integral_neg]
  simp only [← heq] at h
  simpa only [mul_comm] using h

theorem SameOpenHalfPlane.symm {u v : ℂ} (h : SameOpenHalfPlane u v) : SameOpenHalfPlane v u := by
  rcases h with ⟨hu,hv⟩ | ⟨hu,hv⟩
  · exact Or.inl ⟨hv,hu⟩
  · exact Or.inr ⟨hv,hu⟩

theorem anchoredCharacteristicRatio_ne_zero (s : AnchoredCountingState) (u v : ℂ) :
    anchoredCharacteristicRatio s u v ≠ 0 := Complex.exp_ne_zero _

/-- Path reversal identifies denominator differentiation with numerator
 differentiation of the reciprocal ratio. -/
theorem anchoredCharacteristicRatio_swap (s : AnchoredCountingState) (u v : ℂ) :
    anchoredCharacteristicRatio s u v = (anchoredCharacteristicRatio s v u)⁻¹ := by
  have hp (t : ℝ) : ratioPath u v (1-t) = ratioPath v u t := by
    simp only [ratioPath, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  have hi : (∫ t : RatioInterval, anchoredNevanlinna s (ratioPath v u t) ∂ratioIntervalMeasure) =
      ∫ t : RatioInterval, anchoredNevanlinna s (ratioPath u v t) ∂ratioIntervalMeasure := by
    rw [integral_ratioInterval (fun t => anchoredNevanlinna s (ratioPath v u t)),
      integral_ratioInterval (fun t => anchoredNevanlinna s (ratioPath u v t))]
    have h := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := 1)
      (fun t => anchoredNevanlinna s (ratioPath u v t)) 1
    simpa only [hp, sub_self, sub_zero] using h
  simp only [anchoredCharacteristicRatio, integral_const_mul, hi]
  rw [← Complex.exp_neg]
  congr 1
  ring

theorem hasDerivAt_anchoredCharacteristicRatio_denominator (s : AnchoredCountingState)
    {u v : ℂ} (huv : SameOpenHalfPlane u v) :
    HasDerivAt (fun z => anchoredCharacteristicRatio s u z)
      (anchoredNevanlinna s v * anchoredCharacteristicRatio s u v) v := by
  have h := (hasDerivAt_anchoredCharacteristicRatio s huv.symm).inv
    (anchoredCharacteristicRatio_ne_zero s v u)
  have heq : (fun z => anchoredCharacteristicRatio s u z) =
      (fun z => (anchoredCharacteristicRatio s z u)⁻¹) := by
    funext z
    exact anchoredCharacteristicRatio_swap s u z
  rw [heq, anchoredCharacteristicRatio_swap s u v]
  convert h using 1
  field_simp [anchoredCharacteristicRatio_ne_zero s v u]
  ring

/-- The true second numerator derivative has the quadratic resolvent insertion. -/
theorem hasDerivAt_deriv_anchoredCharacteristicRatio (s : AnchoredCountingState)
    {u v : ℂ} (huv : SameOpenHalfPlane u v) :
    HasDerivAt (deriv (fun z => anchoredCharacteristicRatio s z v))
      ((anchoredNevanlinna s u ^ 2 - anchoredDerivative s u) * anchoredCharacteristicRatio s u v) u := by
  have h := (hasDerivAt_anchoredNevanlinna s huv.left_offReal).neg.mul
    (hasDerivAt_anchoredCharacteristicRatio s huv)
  have hh : HasDerivAt (fun z => -anchoredNevanlinna s z * anchoredCharacteristicRatio s z v)
      ((anchoredNevanlinna s u ^ 2 - anchoredDerivative s u) * anchoredCharacteristicRatio s u v) u := by
    convert h using 1
    ring
  apply hh.congr_of_eventuallyEq
  filter_upwards [sameOpenHalfPlane_nhds huv] with z hz
  exact (hasDerivAt_anchoredCharacteristicRatio s hz).deriv

end BourgadeHuang
