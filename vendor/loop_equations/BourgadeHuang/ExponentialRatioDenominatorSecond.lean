import BourgadeHuang.ExponentialRatioDerivatives

/-! Second denominator derivatives with exponentially bounded insertions. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang

theorem exists_local_ratio_reverse_anchor_bounds {u v : ℂ} (huv : SameOpenHalfPlane u v) :
    ∃ R : ℝ, 0 < R ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ L : ℝ, 0 ≤ L ∧
      (∀ z ∈ Metric.closedBall v R, SameOpenHalfPlane u z) ∧
      (∀ z ∈ Metric.closedBall v R, ∀ s : AnchoredCountingState,
        ‖anchoredNevanlinna s z‖ ≤ C*(1+‖s.val.2‖) ∧
        ‖anchoredDerivative s z‖ ≤ C*(1+‖s.val.2‖) ∧
        ‖anchoredCharacteristicRatio s u z‖ ≤ Real.exp (L*‖s.val.2‖)) := by
  obtain ⟨R,hR,K,hK,hKoff,hSame,hPath⟩ := exists_ratioPath_compact_tube huv.symm
  obtain ⟨C,hC,hb⟩ := exists_compact_resolvent_anchor_bound hK hKoff
  obtain ⟨D,hD,hd⟩ := exists_compact_derivative_anchor_bound hK hKoff
  refine ⟨R,hR,C+D,add_nonneg hC hD,(‖v-u‖+R)*C,by positivity,
    fun z hz => (hSame z hz).symm,?_⟩
  intro z hz s
  have hzK : z ∈ K := by
    simpa [ratioPath] using hPath z hz ⟨1,by constructor <;> norm_num⟩
  have hA : 0 ≤ ‖s.val.2‖ := norm_nonneg _
  have hS := hb s z hzK
  have hD' := hd s z hzK
  refine ⟨?_,?_,?_⟩
  · nlinarith
  · nlinarith
  · apply (norm_anchoredCharacteristicRatio_reverse_le_of_bound s z u C
      (fun t => hb s _ (hPath z hz t))).trans
    apply Real.exp_le_exp.mpr
    have hdist : ‖z-v‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
    have hnorm : ‖z-u‖ ≤ ‖v-u‖+R := by
      have ht := norm_add_le (z-v) (v-u)
      rw [sub_add_sub_cancel] at ht
      linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnorm hC) hA

theorem exponentiallyWeightedRatio_denominator_second
    (ν : Measure AnchoredCountingState) (β : Beta) (hh : ExactAnchoredHierarchy ν β)
    {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a * ‖s.val.2‖ ^ 2)) ν)
    (F : AnchoredCountingState → ℂ) (hFm : AEStronglyMeasurable F ν) (hFb : AnchoredExponentialBound F)
    {u v : ℂ} (huv : SameOpenHalfPlane u v) :
    Integrable (fun s => F s * ((anchoredNevanlinna s v ^ 2 + anchoredDerivative s v) *
      anchoredCharacteristicRatio s u v)) ν ∧
    HasDerivAt (deriv (fun z => ∫ s, F s * anchoredCharacteristicRatio s u z ∂ν))
      (∫ s, F s * ((anchoredNevanlinna s v ^ 2 + anchoredDerivative s v) *
        anchoredCharacteristicRatio s u v) ∂ν) v := by
  obtain ⟨R,hR,C,hC,L,hL,hSame,hb⟩ := exists_local_ratio_reverse_anchor_bounds huv
  obtain ⟨M,hM⟩ := hFb
  have hcenter : v ∈ Metric.closedBall v R := Metric.mem_closedBall_self hR.le
  have hri (z : ℂ) (hz : z ∈ Metric.closedBall v R) :
      Integrable (fun s => anchoredCharacteristicRatio s u z) ν :=
    (characteristicRatio_integrable_and_loop ν β hh ha he (hSame z hz) huv.left_offReal).1
  let G := fun z : ℂ => fun s : AnchoredCountingState =>
    F s * ((anchoredNevanlinna s z ^ 2 + anchoredDerivative s z)*anchoredCharacteristicRatio s u z)
  have hdm : AEStronglyMeasurable (G v) ν := hFm.mul
    ((((continuous_anchoredNevanlinna huv.right_offReal).pow 2).add
      (continuous_anchoredDerivative huv.right_offReal)).aestronglyMeasurable.mul
      (hri v hcenter).aestronglyMeasurable)
  let B := fun s : AnchoredCountingState => (C^2+C)*(1+‖s.val.2‖)^2*Real.exp ((M+L)*‖s.val.2‖)
  have hB : Integrable B ν := integrable_anchor_polynomial_exp ν ha he (by positivity) 2 (M+L)
  have hraw : Integrable (G v) ν ∧
      HasDerivAt (fun z => ∫ s, F s * (anchoredNevanlinna s z * anchoredCharacteristicRatio s u z) ∂ν)
        (∫ s, G v s ∂ν) v := by
    apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun z s => F s * (anchoredNevanlinna s z * anchoredCharacteristicRatio s u z))
      (F' := G) (bound := B) hR
      (Filter.eventually_of_mem (Metric.ball_mem_nhds v hR) (fun z hz =>
        hFm.mul ((continuous_anchoredNevanlinna (hSame z (Metric.ball_subset_closedBall hz)).right_offReal).aestronglyMeasurable.mul
          (hri z (Metric.ball_subset_closedBall hz)).aestronglyMeasurable)))
      (exponentiallyWeightedRatio_denominator ν β hh ha he F hFm ⟨M,hM⟩ huv).1 hdm ?_ hB ?_
    · apply Filter.Eventually.of_forall
      intro s z hz
      obtain ⟨hS,hD,hRatio⟩ := hb z (Metric.ball_subset_closedBall hz) s
      have hA : 0 ≤ ‖s.val.2‖ := norm_nonneg _
      have hSq : ‖anchoredNevanlinna s z ^ 2 + anchoredDerivative s z‖ ≤
          (C^2+C)*(1+‖s.val.2‖)^2 := by
        have ht := norm_add_le (anchoredNevanlinna s z ^ 2) (anchoredDerivative s z)
        rw [norm_pow] at ht
        have hs2 := pow_le_pow_left₀ (norm_nonneg _) hS 2
        nlinarith [sq_nonneg ‖s.val.2‖]
      dsimp only [G]
      rw [norm_mul, norm_mul]
      apply (mul_le_mul (hM s) (mul_le_mul hSq hRatio (norm_nonneg _) (by positivity))
        (by positivity) (Real.exp_nonneg _)).trans_eq
      dsimp [B]
      rw [add_mul M L, Real.exp_add]
      ring
    · apply Filter.Eventually.of_forall
      intro s z hz
      have hsz := hSame z (Metric.ball_subset_closedBall hz)
      have hd := ((hasDerivAt_anchoredNevanlinna s hsz.right_offReal).mul
        (hasDerivAt_anchoredCharacteristicRatio_denominator s hsz)).const_mul (F s)
      convert hd using 1
      dsimp [G]
      ring
  refine ⟨hraw.1, hraw.2.congr_of_eventuallyEq ?_⟩
  filter_upwards [sameOpenHalfPlane_nhds huv.symm] with z hz
  exact (exponentiallyWeightedRatio_denominator ν β hh ha he F hFm ⟨M,hM⟩ hz.symm).2.deriv

end BourgadeHuang
