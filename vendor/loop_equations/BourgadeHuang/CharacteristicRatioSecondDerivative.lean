import BourgadeHuang.CharacteristicRatioExpectation

/-! Uniform compact bounds and the true second derivative of expected ratios. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang

theorem norm_anchoredDerivative_le_anchor (s : AnchoredCountingState)
    {z : ℂ} (hz : z.im ≠ 0) :
    ‖anchoredDerivative s z‖ ≤
      (2 + (2*‖z‖)*(1/|z.im|) + ‖1+z^2‖*(1/|z.im|)^2)*‖s.val.2‖ := by
  let C := 1 + (2*‖z‖)*(1/|z.im|) + ‖1+z^2‖*(1/|z.im|)^2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb : ‖(anchoredLinearCoefficient s:ℂ)‖ ≤ ‖s.val.2‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (anchoredLinearCoefficient_nonneg s)]
    have hi : 0 ≤ ∫ a, nevanlinnaWeight a ∂s.val.1.measure := integral_nonneg nevanlinnaWeight_nonneg
    exact (sub_le_self _ hi).trans (Complex.im_le_norm _)
  have hi : ‖∫ a : ℝ, (((a:ℂ)-z)⁻¹)^2 ∂s.val.1.measure‖ ≤ C*‖s.val.2‖ := by
    calc
      _ ≤ ∫ a, C*nevanlinnaWeight a ∂s.val.1.measure :=
        norm_integral_le_of_norm_le (s.integrable_weight.const_mul C)
          (Filter.Eventually.of_forall (fun a => norm_reciprocal_sq_le_weight a hz))
      _ = C*(∫ a, nevanlinnaWeight a ∂s.val.1.measure) := integral_const_mul _ _
      _ ≤ C*‖s.val.2‖ := mul_le_mul_of_nonneg_left
        (s.integral_weight_le_im.trans (Complex.im_le_norm _)) hC
  rw [anchoredDerivative_eq_integral s hz]
  exact ((norm_add_le _ _).trans (add_le_add hb hi)).trans_eq (by dsimp [C]; ring)

theorem exists_compact_derivative_anchor_bound {K : Set ℂ} (hK : IsCompact K)
    (hoff : ∀ z ∈ K, z.im ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : AnchoredCountingState, ∀ z ∈ K,
      ‖anchoredDerivative s z‖ ≤ C*‖s.val.2‖ := by
  have hi : ContinuousOn (fun z : ℂ => 1/|z.im|) K := continuousOn_const.div
    (continuous_abs.comp Complex.continuous_im).continuousOn (fun z hz => abs_ne_zero.mpr (hoff z hz))
  have hc : ContinuousOn (fun z : ℂ =>
      2 + (2*‖z‖)*(1/|z.im|) + ‖1+z^2‖*(1/|z.im|)^2) K :=
    (continuousOn_const.add ((continuous_const.mul continuous_norm).continuousOn.mul hi)).add
      (((continuous_const.add (continuous_id.pow 2)).norm).continuousOn.mul (hi.pow 2))
  obtain ⟨C,hC⟩ := hK.bddAbove_image hc
  refine ⟨max C 0, le_max_right _ _, fun s z hz => ?_⟩
  exact (norm_anchoredDerivative_le_anchor s (hoff z hz)).trans
    (mul_le_mul_of_nonneg_right ((hC ⟨z,hz,rfl⟩).trans (le_max_left _ _)) (norm_nonneg _))

/-- A single neighborhood controls the ratio, the resolvent, and its derivative
by the anchor, with constants uniform in the state. -/
theorem exists_local_ratio_anchor_bounds {u v : ℂ} (huv : SameOpenHalfPlane u v) :
    ∃ R : ℝ, 0 < R ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ L : ℝ, 0 ≤ L ∧
      (∀ z ∈ Metric.closedBall u R, SameOpenHalfPlane z v) ∧
      (∀ z ∈ Metric.closedBall u R, ∀ s : AnchoredCountingState,
        ‖anchoredNevanlinna s z‖ ≤ C*(1+‖s.val.2‖) ∧
        ‖anchoredDerivative s z‖ ≤ C*(1+‖s.val.2‖) ∧
        ‖anchoredCharacteristicRatio s z v‖ ≤ Real.exp (L*‖s.val.2‖)) := by
  obtain ⟨R,hR,K,hK,hKoff,hSame,hPath⟩ := exists_ratioPath_compact_tube huv
  obtain ⟨C,hC,hb⟩ := exists_compact_resolvent_anchor_bound hK hKoff
  obtain ⟨D,hD,hd⟩ := exists_compact_derivative_anchor_bound hK hKoff
  refine ⟨R,hR,C+D,add_nonneg hC hD,(‖u-v‖+R)*C,by positivity,hSame,?_⟩
  intro z hz s
  have hzK : z ∈ K := by
    simpa [ratioPath] using hPath z hz ⟨1,by constructor <;> norm_num⟩
  have hA : 0 ≤ ‖s.val.2‖ := norm_nonneg _
  have hS := hb s z hzK
  have hD' := hd s z hzK
  refine ⟨?_,?_,?_⟩
  · nlinarith
  · nlinarith
  · apply (norm_anchoredCharacteristicRatio_le_of_bound s z v C (fun t => hb s _ (hPath z hz t))).trans
    apply Real.exp_le_exp.mpr
    have hdist : ‖z-u‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
    have hnorm : ‖z-v‖ ≤ ‖u-v‖+R := by
      have ht := norm_add_le (z-u) (u-v)
      rw [sub_add_sub_cancel] at ht
      linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnorm hC) hA

/-- The second derivative is obtained by differentiating the actual first
resolvent insertion, not by formal manipulation of a power series. -/
theorem expectedCharacteristicRatio_second
    (ν : Measure AnchoredCountingState) (β : Beta) (hh : ExactAnchoredHierarchy ν β)
    {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a * ‖s.val.2‖ ^ 2)) ν)
    {u v : ℂ} (huv : SameOpenHalfPlane u v) :
    Integrable (fun s => (anchoredNevanlinna s u ^ 2 - anchoredDerivative s u) *
      anchoredCharacteristicRatio s u v) ν ∧
    HasDerivAt (deriv (fun z => ∫ s, anchoredCharacteristicRatio s z v ∂ν))
      (∫ s, (anchoredNevanlinna s u ^ 2 - anchoredDerivative s u) *
        anchoredCharacteristicRatio s u v ∂ν) u := by
  obtain ⟨R,hR,C,hC,L,hL,hSame,hb⟩ := exists_local_ratio_anchor_bounds huv
  have hcenter : u ∈ Metric.closedBall u R := Metric.mem_closedBall_self hR.le
  have hri (z : ℂ) (hz : z ∈ Metric.closedBall u R) :
      Integrable (fun s => anchoredCharacteristicRatio s z v) ν :=
    (characteristicRatio_integrable_and_loop ν β hh ha he (hSame z hz) huv.left_offReal).1
  have hbase (z : ℂ) (hz : SameOpenHalfPlane z v) :
      Integrable (fun s => -anchoredNevanlinna s z * anchoredCharacteristicRatio s z v) ν ∧
      HasDerivAt (fun z => ∫ s, anchoredCharacteristicRatio s z v ∂ν)
        (∫ s, -anchoredNevanlinna s z * anchoredCharacteristicRatio s z v ∂ν) z := by
    simpa only [one_mul] using
      (expectedCharacteristicRatio_integrable_and_hasDerivAt ν β hh ha he
        (fun _ => 1) continuous_const (AnchoredGrowth.const 1) hz).2
  let G := fun z : ℂ => fun s : AnchoredCountingState =>
    (anchoredNevanlinna s z ^ 2 - anchoredDerivative s z)*anchoredCharacteristicRatio s z v
  have hdm : AEStronglyMeasurable (G u) ν :=
    (((continuous_anchoredNevanlinna huv.left_offReal).pow 2).sub
      (continuous_anchoredDerivative huv.left_offReal)).aestronglyMeasurable.mul
      (hri u hcenter).aestronglyMeasurable
  let B := fun s : AnchoredCountingState => (C^2+C)*(1+‖s.val.2‖)^2*Real.exp (L*‖s.val.2‖)
  have hB : Integrable B ν := integrable_anchor_polynomial_exp ν ha he (by positivity) 2 L
  have hraw : Integrable (G u) ν ∧
      HasDerivAt (fun z => ∫ s, -anchoredNevanlinna s z * anchoredCharacteristicRatio s z v ∂ν)
        (∫ s, G u s ∂ν) u := by
    apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun z s => -anchoredNevanlinna s z * anchoredCharacteristicRatio s z v)
      (F' := G) (bound := B) hR
      (Filter.eventually_of_mem (Metric.ball_mem_nhds u hR) (fun z hz =>
        ((continuous_anchoredNevanlinna (hSame z (Metric.ball_subset_closedBall hz)).left_offReal).neg.aestronglyMeasurable.mul
          (hri z (Metric.ball_subset_closedBall hz)).aestronglyMeasurable)))
      (hbase u huv).1 hdm ?_ hB ?_
    · apply Filter.Eventually.of_forall
      intro s z hz
      obtain ⟨hS,hD,hRatio⟩ := hb z (Metric.ball_subset_closedBall hz) s
      have hA : 0 ≤ ‖s.val.2‖ := norm_nonneg _
      have hSq : ‖anchoredNevanlinna s z ^ 2 - anchoredDerivative s z‖ ≤
          (C^2+C)*(1+‖s.val.2‖)^2 := by
        have ht := norm_sub_le (anchoredNevanlinna s z ^ 2) (anchoredDerivative s z)
        rw [norm_pow] at ht
        have hs2 := pow_le_pow_left₀ (norm_nonneg _) hS 2
        nlinarith [sq_nonneg ‖s.val.2‖]
      exact (norm_mul _ _).le.trans
        (mul_le_mul hSq hRatio (norm_nonneg _) (by positivity))
    · apply Filter.Eventually.of_forall
      intro s z hz
      have hsz := hSame z (Metric.ball_subset_closedBall hz)
      have hd := (hasDerivAt_anchoredNevanlinna s hsz.left_offReal).neg.mul
        (hasDerivAt_anchoredCharacteristicRatio s hsz)
      convert hd using 1
      dsimp [G]
      ring
  refine ⟨hraw.1, hraw.2.congr_of_eventuallyEq ?_⟩
  filter_upwards [sameOpenHalfPlane_nhds huv] with z hz
  exact (hbase z hz).2.deriv

end BourgadeHuang
