import BourgadeHuang.CharacteristicRatioExpectation

/-! The actual denominator derivative of expected characteristic ratios. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang

theorem norm_anchoredCharacteristicRatio_reverse_le_of_bound (s : AnchoredCountingState)
    (u v : ℂ) (C : ℝ)
    (hb : ∀ t : RatioInterval, ‖anchoredNevanlinna s (ratioPath u v t)‖ ≤ C*‖s.val.2‖) :
    ‖anchoredCharacteristicRatio s v u‖ ≤ Real.exp ((‖u-v‖*C)*‖s.val.2‖) := by
  rw [anchoredCharacteristicRatio_swap s v u]
  unfold anchoredCharacteristicRatio
  rw [← Complex.exp_neg]
  apply (Complex.norm_exp_le_exp_norm _).trans
  apply Real.exp_le_exp.mpr
  rw [norm_neg]
  have h := norm_integral_le_of_norm_le_const (μ := ratioIntervalMeasure)
    (C := (‖u-v‖*C)*‖s.val.2‖)
    (f := fun t : RatioInterval => -(u-v)*anchoredNevanlinna s (ratioPath u v t))
    (Filter.Eventually.of_forall (fun t => by
      rw [norm_mul, norm_neg]
      exact (mul_le_mul_of_nonneg_left (hb t) (norm_nonneg _)).trans_eq (by ring)))
  simpa using h

theorem expectedCharacteristicRatio_denominator
    (ν : Measure AnchoredCountingState) (β : Beta) (hh : ExactAnchoredHierarchy ν β)
    {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a * ‖s.val.2‖ ^ 2)) ν)
    {u v : ℂ} (huv : SameOpenHalfPlane u v) :
    Integrable (fun s => anchoredNevanlinna s v * anchoredCharacteristicRatio s u v) ν ∧
    HasDerivAt (fun z => ∫ s, anchoredCharacteristicRatio s u z ∂ν)
      (∫ s, anchoredNevanlinna s v * anchoredCharacteristicRatio s u v ∂ν) v := by
  obtain ⟨R,hR,K,hK,hKoff,hSame,hPath⟩ := exists_ratioPath_compact_tube huv.symm
  obtain ⟨C,hC,hb⟩ := exists_compact_resolvent_anchor_bound hK hKoff
  let L : ℝ := (‖v-u‖+R)*C
  have hcenter : v ∈ Metric.closedBall v R := Metric.mem_closedBall_self hR.le
  have hZ (z : ℂ) (hz : z ∈ Metric.closedBall v R) : z ∈ K := by
    simpa [ratioPath] using hPath z hz ⟨1,by constructor <;> norm_num⟩
  have hratio (z : ℂ) (hz : z ∈ Metric.closedBall v R) (s : AnchoredCountingState) :
      ‖anchoredCharacteristicRatio s u z‖ ≤ Real.exp (L*‖s.val.2‖) := by
    apply (norm_anchoredCharacteristicRatio_reverse_le_of_bound s z u C
      (fun t => hb s _ (hPath z hz t))).trans
    apply Real.exp_le_exp.mpr
    have hdist : ‖z-v‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
    have hnorm : ‖z-u‖ ≤ ‖v-u‖+R := by
      have ht := norm_add_le (z-v) (v-u)
      rw [sub_add_sub_cancel] at ht
      linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnorm hC) (norm_nonneg _)
  have hri (z : ℂ) (hz : z ∈ Metric.closedBall v R) :
      Integrable (fun s => anchoredCharacteristicRatio s u z) ν :=
    (characteristicRatio_integrable_and_loop ν β hh ha he (hSame z hz).symm huv.left_offReal).1
  let B := fun s : AnchoredCountingState => C*(1+‖s.val.2‖)^1*Real.exp (L*‖s.val.2‖)
  have hB : Integrable B ν := integrable_anchor_polynomial_exp ν ha he hC 1 L
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z s => anchoredCharacteristicRatio s u z)
    (F' := fun z s => anchoredNevanlinna s z * anchoredCharacteristicRatio s u z)
    (bound := B) hR
    (Filter.eventually_of_mem (Metric.ball_mem_nhds v hR) (fun z hz =>
      (hri z (Metric.ball_subset_closedBall hz)).aestronglyMeasurable))
    (hri v hcenter)
    ((continuous_anchoredNevanlinna huv.right_offReal).aestronglyMeasurable.mul
      (hri v hcenter).aestronglyMeasurable) ?_ hB ?_
  · apply Filter.Eventually.of_forall
    intro s z hz
    have hzb := Metric.ball_subset_closedBall hz
    have hS : ‖anchoredNevanlinna s z‖ ≤ C*(1+‖s.val.2‖) :=
      (hb s z (hZ z hzb)).trans (mul_le_mul_of_nonneg_left (by linarith) hC)
    simpa only [B, norm_mul, pow_one] using
      mul_le_mul hS (hratio z hzb s) (norm_nonneg _) (by positivity)
  · exact Filter.Eventually.of_forall fun s z hz =>
      hasDerivAt_anchoredCharacteristicRatio_denominator s (hSame z (Metric.ball_subset_closedBall hz)).symm

end BourgadeHuang
