import BourgadeHuang.CharacteristicRatioDerivatives

/-! Differentiation of genuine expected characteristic-ratio observables. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang

theorem exists_ratioPath_compact_tube {u v : ℂ} (huv : SameOpenHalfPlane u v) :
    ∃ R : ℝ, 0 < R ∧ ∃ K : Set ℂ, IsCompact K ∧
      (∀ z ∈ K, z.im ≠ 0) ∧
      (∀ z ∈ Metric.closedBall u R, SameOpenHalfPlane z v) ∧
      (∀ z ∈ Metric.closedBall u R, ∀ t : RatioInterval, ratioPath z v t ∈ K) := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (sameOpenHalfPlane_nhds huv)
  let R : ℝ := ε/2
  have hR : 0 < R := by dsimp [R]; positivity
  have hclosed (z : ℂ) (hz : z ∈ Metric.closedBall u R) : SameOpenHalfPlane z v :=
    hball (Metric.closedBall_subset_ball (by dsimp [R]; linarith) hz)
  letI : CompactSpace (Metric.closedBall u R) := isCompact_iff_compactSpace.mp (isCompact_closedBall u R)
  let Q := Metric.closedBall u R × RatioInterval
  let P : Q → ℂ := fun p => ratioPath p.1.val v p.2.val
  have hP : Continuous P :=
    continuous_const.add ((Complex.continuous_ofReal.comp
      (continuous_subtype_val.comp continuous_snd)).mul
      ((continuous_subtype_val.comp continuous_fst).sub continuous_const))
  refine ⟨R, hR, Set.range P, isCompact_range hP, ?_, hclosed, ?_⟩
  · rintro z ⟨p, rfl⟩
    exact ratioPath_offReal (hclosed _ p.1.property) p.2.property
  · intro z hz t
    exact ⟨(⟨z,hz⟩,t), rfl⟩

/-- A pathwise exponential bound whose constant depends on the path, and not on
any finite particle number. -/
theorem norm_anchoredCharacteristicRatio_le_of_bound (s : AnchoredCountingState)
    (u v : ℂ) (C : ℝ)
    (hb : ∀ t : RatioInterval, ‖anchoredNevanlinna s (ratioPath u v t)‖ ≤ C*‖s.val.2‖) :
    ‖anchoredCharacteristicRatio s u v‖ ≤ Real.exp ((‖u-v‖*C)*‖s.val.2‖) := by
  apply (Complex.norm_exp_le_exp_norm _).trans
  apply Real.exp_le_exp.mpr
  have h := norm_integral_le_of_norm_le_const (μ := ratioIntervalMeasure)
    (C := (‖u-v‖*C)*‖s.val.2‖)
    (f := fun t : RatioInterval => -(u-v)*anchoredNevanlinna s (ratioPath u v t))
    (Filter.Eventually.of_forall (fun t => by
      rw [norm_mul, norm_neg]
      exact (mul_le_mul_of_nonneg_left (hb t) (norm_nonneg _)).trans_eq (by ring)))
  simpa using h

/-- Expected characteristic ratios may be multiplied by any continuous
observable of polynomial anchor growth. Their numerator derivative is an actual
integral, with all required integrability obtained from exponential-square tails. -/
theorem expectedCharacteristicRatio_integrable_and_hasDerivAt
    (ν : Measure AnchoredCountingState) (β : Beta) (hh : ExactAnchoredHierarchy ν β)
    {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a * ‖s.val.2‖ ^ 2)) ν)
    (F : AnchoredCountingState → ℂ) (hF : Continuous F) {d : ℕ} (hFg : AnchoredGrowth F d)
    {u v : ℂ} (huv : SameOpenHalfPlane u v) :
    Integrable (fun s => F s * anchoredCharacteristicRatio s u v) ν ∧
    Integrable (fun s => F s * (-anchoredNevanlinna s u * anchoredCharacteristicRatio s u v)) ν ∧
    HasDerivAt (fun z => ∫ s, F s * anchoredCharacteristicRatio s z v ∂ν)
      (∫ s, F s * (-anchoredNevanlinna s u * anchoredCharacteristicRatio s u v) ∂ν) u := by
  obtain ⟨R, hR, K, hK, hKoff, hSame, hPath⟩ := exists_ratioPath_compact_tube huv
  obtain ⟨C, hC, hb⟩ := exists_compact_resolvent_anchor_bound hK hKoff
  obtain ⟨D, hD, hFb⟩ := hFg
  let L : ℝ := (‖u-v‖+R)*C
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hcenter : u ∈ Metric.closedBall u R := Metric.mem_closedBall_self hR.le
  have hZ (z : ℂ) (hz : z ∈ Metric.closedBall u R) : z ∈ K := by
    simpa [ratioPath] using hPath z hz ⟨1,by constructor <;> norm_num⟩
  have hratio (z : ℂ) (hz : z ∈ Metric.closedBall u R) (s : AnchoredCountingState) :
      ‖anchoredCharacteristicRatio s z v‖ ≤ Real.exp (L*‖s.val.2‖) := by
    apply (norm_anchoredCharacteristicRatio_le_of_bound s z v C
      (fun t => hb s _ (hPath z hz t))).trans
    apply Real.exp_le_exp.mpr
    have hdist : ‖z-u‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
    have hnorm : ‖z-v‖ ≤ ‖u-v‖+R := by
      have ht := norm_add_le (z-u) (u-v)
      rw [sub_add_sub_cancel] at ht
      linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnorm hC) (norm_nonneg _)
  have hri (z : ℂ) (hz : z ∈ Metric.closedBall u R) :
      Integrable (fun s => anchoredCharacteristicRatio s z v) ν :=
    (characteristicRatio_integrable_and_loop ν β hh ha he (hSame z hz) huv.left_offReal).1
  let B := fun s : AnchoredCountingState =>
    (D*C)*(1+‖s.val.2‖)^(d+1)*Real.exp (L*‖s.val.2‖)
  have hB : Integrable B ν := integrable_anchor_polynomial_exp ν ha he (mul_nonneg hD hC) (d+1) L
  have hmain : Integrable (fun s => F s * anchoredCharacteristicRatio s u v) ν := by
    apply (integrable_anchor_polynomial_exp ν ha he hD d L).mono'
      (hF.aestronglyMeasurable.mul (hri u hcenter).aestronglyMeasurable)
    apply Filter.Eventually.of_forall
    intro s
    change ‖F s * anchoredCharacteristicRatio s u v‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul (hFb s) (hratio u hcenter s) (norm_nonneg _) (by positivity)
  have hdm : AEStronglyMeasurable
      (fun s => F s * (-anchoredNevanlinna s u * anchoredCharacteristicRatio s u v)) ν :=
    hF.aestronglyMeasurable.mul
      ((continuous_anchoredNevanlinna huv.left_offReal).neg.aestronglyMeasurable.mul
        (hri u hcenter).aestronglyMeasurable)
  refine ⟨hmain, ?_⟩
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z s => F s * anchoredCharacteristicRatio s z v)
    (F' := fun z s => F s * (-anchoredNevanlinna s z * anchoredCharacteristicRatio s z v))
    (bound := B) hR
    (Filter.eventually_of_mem (Metric.ball_mem_nhds u hR) (fun z hz =>
      hF.aestronglyMeasurable.mul (hri z (Metric.ball_subset_closedBall hz)).aestronglyMeasurable))
    hmain hdm ?_ hB ?_
  · apply Filter.Eventually.of_forall
    intro s z hz
    have hzb := Metric.ball_subset_closedBall hz
    have hS : ‖anchoredNevanlinna s z‖ ≤ C*(1+‖s.val.2‖) :=
      (hb s z (hZ z hzb)).trans (mul_le_mul_of_nonneg_left (by linarith) hC)
    have hFS : ‖F s‖ * ‖anchoredNevanlinna s z‖ ≤ (D*C)*(1+‖s.val.2‖)^(d+1) := by
      apply (mul_le_mul (hFb s) hS (norm_nonneg _) (by positivity)).trans_eq
      rw [pow_succ]
      ring
    simpa only [norm_mul, norm_neg, ← mul_assoc] using
      mul_le_mul hFS (hratio z hzb s) (norm_nonneg _) (by positivity)
  · exact Filter.Eventually.of_forall fun s z hz =>
      (hasDerivAt_anchoredCharacteristicRatio s (hSame z (Metric.ball_subset_closedBall hz))).const_mul (F s)

theorem hasDerivAt_expectedCharacteristicRatio
    (ν : Measure AnchoredCountingState) (β : Beta) (hh : ExactAnchoredHierarchy ν β)
    {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a * ‖s.val.2‖ ^ 2)) ν)
    (F : AnchoredCountingState → ℂ) (hF : Continuous F) {d : ℕ} (hFg : AnchoredGrowth F d)
    {u v : ℂ} (huv : SameOpenHalfPlane u v) :
    HasDerivAt (fun z => ∫ s, F s * anchoredCharacteristicRatio s z v ∂ν)
      (∫ s, F s * (-anchoredNevanlinna s u * anchoredCharacteristicRatio s u v) ∂ν) u :=
  (expectedCharacteristicRatio_integrable_and_hasDerivAt ν β hh ha he F hF hFg huv).2.2

end BourgadeHuang
