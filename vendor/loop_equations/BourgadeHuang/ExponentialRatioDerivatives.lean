import BourgadeHuang.CharacteristicRatioSecondDerivative
import BourgadeHuang.CharacteristicRatioDenominator

/-! Exponential insertions allow the ratio derivatives to be applied one
coordinate at a time to arbitrary finite products of ratios. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang

def AnchoredExponentialBound (F : AnchoredCountingState → ℂ) : Prop :=
  ∃ L : ℝ, ∀ s, ‖F s‖ ≤ Real.exp (L*‖s.val.2‖)

theorem AnchoredExponentialBound.one : AnchoredExponentialBound (fun _ => 1) :=
  ⟨0,by simp⟩

theorem AnchoredExponentialBound.mul {F G : AnchoredCountingState → ℂ}
    (hF : AnchoredExponentialBound F) (hG : AnchoredExponentialBound G) :
    AnchoredExponentialBound (fun s => F s * G s) := by
  obtain ⟨L,hL⟩ := hF
  obtain ⟨M,hM⟩ := hG
  refine ⟨L+M, fun s => ?_⟩
  rw [norm_mul, add_mul, Real.exp_add]
  exact mul_le_mul (hL s) (hM s) (norm_nonneg _) (Real.exp_nonneg _)

theorem AnchoredExponentialBound.finset_prod {ι : Type*} (I : Finset ι)
    (F : ι → AnchoredCountingState → ℂ) (hF : ∀ i ∈ I, AnchoredExponentialBound (F i)) :
    AnchoredExponentialBound (fun s => ∏ i ∈ I, F i s) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using AnchoredExponentialBound.one
  | @insert i I hi ih =>
    simpa only [Finset.prod_insert hi] using
      (hF i (Finset.mem_insert_self _ _)).mul (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)))

theorem anchoredExponentialBound_characteristicRatio {u v : ℂ} (huv : SameOpenHalfPlane u v) :
    AnchoredExponentialBound (fun s => anchoredCharacteristicRatio s u v) := by
  obtain ⟨R,hR,K,hK,hKoff,hSame,hPath⟩ := exists_ratioPath_compact_tube huv
  obtain ⟨C,hC,hb⟩ := exists_compact_resolvent_anchor_bound hK hKoff
  refine ⟨‖u-v‖*C, fun s => ?_⟩
  exact norm_anchoredCharacteristicRatio_le_of_bound s u v C
    (fun t => hb s _ (hPath u (Metric.mem_closedBall_self hR.le) t))

theorem integrable_exponentiallyWeightedRatio
    (ν : Measure AnchoredCountingState) (β : Beta) (hh : ExactAnchoredHierarchy ν β)
    {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a * ‖s.val.2‖ ^ 2)) ν)
    (F : AnchoredCountingState → ℂ) (hFm : AEStronglyMeasurable F ν) (hFb : AnchoredExponentialBound F)
    {u v : ℂ} (huv : SameOpenHalfPlane u v) :
    Integrable (fun s => F s * anchoredCharacteristicRatio s u v) ν := by
  obtain ⟨L,hL⟩ := hFb.mul (anchoredExponentialBound_characteristicRatio huv)
  have hri := (characteristicRatio_integrable_and_loop ν β hh ha he huv huv.left_offReal).1
  have hi := integrable_anchor_polynomial_exp ν ha he (by norm_num : (0:ℝ)≤1) 0 L
  simp only [pow_zero, mul_one, one_mul] at hi
  exact hi.mono' (hFm.mul hri.aestronglyMeasurable) (Filter.Eventually.of_forall hL)

theorem exponentiallyWeightedRatio_numerator
    (ν : Measure AnchoredCountingState) (β : Beta) (hh : ExactAnchoredHierarchy ν β)
    {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a * ‖s.val.2‖ ^ 2)) ν)
    (F : AnchoredCountingState → ℂ) (hFm : AEStronglyMeasurable F ν) (hFb : AnchoredExponentialBound F)
    {u v : ℂ} (huv : SameOpenHalfPlane u v) :
    Integrable (fun s => F s * (-anchoredNevanlinna s u * anchoredCharacteristicRatio s u v)) ν ∧
    HasDerivAt (fun z => ∫ s, F s * anchoredCharacteristicRatio s z v ∂ν)
      (∫ s, F s * (-anchoredNevanlinna s u * anchoredCharacteristicRatio s u v) ∂ν) u := by
  obtain ⟨R,hR,C,hC,L,hL,hSame,hb⟩ := exists_local_ratio_anchor_bounds huv
  obtain ⟨M,hM⟩ := hFb
  have hcenter : u ∈ Metric.closedBall u R := Metric.mem_closedBall_self hR.le
  have hri (z : ℂ) (hz : z ∈ Metric.closedBall u R) :
      Integrable (fun s => anchoredCharacteristicRatio s z v) ν :=
    (characteristicRatio_integrable_and_loop ν β hh ha he (hSame z hz) huv.left_offReal).1
  let B := fun s : AnchoredCountingState => C*(1+‖s.val.2‖)^1*Real.exp ((M+L)*‖s.val.2‖)
  have hB : Integrable B ν := integrable_anchor_polynomial_exp ν ha he hC 1 (M+L)
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z s => F s * anchoredCharacteristicRatio s z v)
    (F' := fun z s => F s * (-anchoredNevanlinna s z * anchoredCharacteristicRatio s z v))
    (bound := B) hR
    (Filter.eventually_of_mem (Metric.ball_mem_nhds u hR) (fun z hz =>
      hFm.mul (hri z (Metric.ball_subset_closedBall hz)).aestronglyMeasurable))
    (integrable_exponentiallyWeightedRatio ν β hh ha he F hFm ⟨M,hM⟩ huv)
    (hFm.mul ((continuous_anchoredNevanlinna huv.left_offReal).neg.aestronglyMeasurable.mul
      (hri u hcenter).aestronglyMeasurable)) ?_ hB ?_
  · apply Filter.Eventually.of_forall
    intro s z hz
    obtain ⟨hS,_,hRatio⟩ := hb z (Metric.ball_subset_closedBall hz) s
    rw [norm_mul, norm_mul, norm_neg]
    apply (mul_le_mul (hM s) (mul_le_mul hS hRatio (norm_nonneg _) (by positivity))
      (by positivity) (Real.exp_nonneg _)).trans_eq
    dsimp [B]
    rw [pow_one, add_mul M L, Real.exp_add]
    ring
  · exact Filter.Eventually.of_forall fun s z hz =>
      (hasDerivAt_anchoredCharacteristicRatio s (hSame z (Metric.ball_subset_closedBall hz))).const_mul (F s)

theorem exponentiallyWeightedRatio_second
    (ν : Measure AnchoredCountingState) (β : Beta) (hh : ExactAnchoredHierarchy ν β)
    {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a * ‖s.val.2‖ ^ 2)) ν)
    (F : AnchoredCountingState → ℂ) (hFm : AEStronglyMeasurable F ν) (hFb : AnchoredExponentialBound F)
    {u v : ℂ} (huv : SameOpenHalfPlane u v) :
    Integrable (fun s => F s * ((anchoredNevanlinna s u ^ 2 - anchoredDerivative s u) *
      anchoredCharacteristicRatio s u v)) ν ∧
    HasDerivAt (deriv (fun z => ∫ s, F s * anchoredCharacteristicRatio s z v ∂ν))
      (∫ s, F s * ((anchoredNevanlinna s u ^ 2 - anchoredDerivative s u) *
        anchoredCharacteristicRatio s u v) ∂ν) u := by
  obtain ⟨R,hR,C,hC,L,hL,hSame,hb⟩ := exists_local_ratio_anchor_bounds huv
  obtain ⟨M,hM⟩ := hFb
  have hcenter : u ∈ Metric.closedBall u R := Metric.mem_closedBall_self hR.le
  have hri (z : ℂ) (hz : z ∈ Metric.closedBall u R) :
      Integrable (fun s => anchoredCharacteristicRatio s z v) ν :=
    (characteristicRatio_integrable_and_loop ν β hh ha he (hSame z hz) huv.left_offReal).1
  let G := fun z : ℂ => fun s : AnchoredCountingState =>
    F s * ((anchoredNevanlinna s z ^ 2 - anchoredDerivative s z)*anchoredCharacteristicRatio s z v)
  have hdm : AEStronglyMeasurable (G u) ν := hFm.mul
    ((((continuous_anchoredNevanlinna huv.left_offReal).pow 2).sub
      (continuous_anchoredDerivative huv.left_offReal)).aestronglyMeasurable.mul
      (hri u hcenter).aestronglyMeasurable)
  let B := fun s : AnchoredCountingState => (C^2+C)*(1+‖s.val.2‖)^2*Real.exp ((M+L)*‖s.val.2‖)
  have hB : Integrable B ν := integrable_anchor_polynomial_exp ν ha he (by positivity) 2 (M+L)
  have hraw : Integrable (G u) ν ∧
      HasDerivAt (fun z => ∫ s, F s * (-anchoredNevanlinna s z * anchoredCharacteristicRatio s z v) ∂ν)
        (∫ s, G u s ∂ν) u := by
    apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun z s => F s * (-anchoredNevanlinna s z * anchoredCharacteristicRatio s z v))
      (F' := G) (bound := B) hR
      (Filter.eventually_of_mem (Metric.ball_mem_nhds u hR) (fun z hz =>
        hFm.mul ((continuous_anchoredNevanlinna (hSame z (Metric.ball_subset_closedBall hz)).left_offReal).neg.aestronglyMeasurable.mul
          (hri z (Metric.ball_subset_closedBall hz)).aestronglyMeasurable)))
      (exponentiallyWeightedRatio_numerator ν β hh ha he F hFm ⟨M,hM⟩ huv).1 hdm ?_ hB ?_
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
      have hd := ((hasDerivAt_anchoredNevanlinna s hsz.left_offReal).neg.mul
        (hasDerivAt_anchoredCharacteristicRatio s hsz)).const_mul (F s)
      convert hd using 1
      dsimp [G]
      ring
  refine ⟨hraw.1, hraw.2.congr_of_eventuallyEq ?_⟩
  filter_upwards [sameOpenHalfPlane_nhds huv] with z hz
  exact (exponentiallyWeightedRatio_numerator ν β hh ha he F hFm ⟨M,hM⟩ hz).2.deriv

theorem exponentiallyWeightedRatio_denominator
    (ν : Measure AnchoredCountingState) (β : Beta) (hh : ExactAnchoredHierarchy ν β)
    {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a * ‖s.val.2‖ ^ 2)) ν)
    (F : AnchoredCountingState → ℂ) (hFm : AEStronglyMeasurable F ν) (hFb : AnchoredExponentialBound F)
    {u v : ℂ} (huv : SameOpenHalfPlane u v) :
    Integrable (fun s => F s * (anchoredNevanlinna s v * anchoredCharacteristicRatio s u v)) ν ∧
    HasDerivAt (fun z => ∫ s, F s * anchoredCharacteristicRatio s u z ∂ν)
      (∫ s, F s * (anchoredNevanlinna s v * anchoredCharacteristicRatio s u v) ∂ν) v := by
  obtain ⟨R,hR,K,hK,hKoff,hSame,hPath⟩ := exists_ratioPath_compact_tube huv.symm
  obtain ⟨C,hC,hb⟩ := exists_compact_resolvent_anchor_bound hK hKoff
  obtain ⟨M,hM⟩ := hFb
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
  let B := fun s : AnchoredCountingState => C*(1+‖s.val.2‖)^1*Real.exp ((M+L)*‖s.val.2‖)
  have hB : Integrable B ν := integrable_anchor_polynomial_exp ν ha he hC 1 (M+L)
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z s => F s * anchoredCharacteristicRatio s u z)
    (F' := fun z s => F s * (anchoredNevanlinna s z * anchoredCharacteristicRatio s u z))
    (bound := B) hR
    (Filter.eventually_of_mem (Metric.ball_mem_nhds v hR) (fun z hz =>
      hFm.mul (hri z (Metric.ball_subset_closedBall hz)).aestronglyMeasurable))
    (integrable_exponentiallyWeightedRatio ν β hh ha he F hFm ⟨M,hM⟩ huv)
    (hFm.mul ((continuous_anchoredNevanlinna huv.right_offReal).aestronglyMeasurable.mul
      (hri v hcenter).aestronglyMeasurable)) ?_ hB ?_
  · apply Filter.Eventually.of_forall
    intro s z hz
    have hzb := Metric.ball_subset_closedBall hz
    have hS : ‖anchoredNevanlinna s z‖ ≤ C*(1+‖s.val.2‖) :=
      (hb s z (hZ z hzb)).trans (mul_le_mul_of_nonneg_left (by linarith) hC)
    rw [norm_mul, norm_mul]
    apply (mul_le_mul (hM s) (mul_le_mul hS (hratio z hzb s) (norm_nonneg _) (by positivity))
      (by positivity) (Real.exp_nonneg _)).trans_eq
    dsimp [B]
    rw [pow_one, add_mul M L, Real.exp_add]
    ring
  · exact Filter.Eventually.of_forall fun s z hz =>
      (hasDerivAt_anchoredCharacteristicRatio_denominator s
        (hSame z (Metric.ball_subset_closedBall hz)).symm).const_mul (F s)

end BourgadeHuang
