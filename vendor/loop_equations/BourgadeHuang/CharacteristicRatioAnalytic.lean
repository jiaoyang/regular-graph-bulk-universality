import BourgadeHuang.CharacteristicRatioDetermination
import BourgadeHuang.CharacteristicRatioCauchyMeasurability
import BourgadeHuang.CharacteristicRatioSecondDerivative
import Mathlib.Analysis.Analytic.Constructions

/-! # Joint analyticity and uniform Cauchy bounds for genuine ratios -/
noncomputable section
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory Filter
namespace BourgadeHuang

theorem SameOpenHalfPlane.trans {u v w : ℂ}
    (huv : SameOpenHalfPlane u v) (hvw : SameOpenHalfPlane v w) : SameOpenHalfPlane u w := by
  rcases huv with ⟨hu,hv⟩ | ⟨hu,hv⟩ <;> rcases hvw with ⟨hv',hw⟩ | ⟨hv',hw⟩
  · exact Or.inl ⟨hu,hw⟩
  · linarith
  · linarith
  · exact Or.inr ⟨hu,hw⟩

theorem isOpen_sameOpenHalfPlane (v : ℂ) : IsOpen {u | SameOpenHalfPlane u v} := by
  change IsOpen ({u : ℂ | 0 < u.im} ∩ {u : ℂ | 0 < v.im} ∪
    {u : ℂ | u.im < 0} ∩ {u : ℂ | v.im < 0})
  exact ((isOpen_lt continuous_const Complex.continuous_im).inter
    (isOpen_const)).union ((isOpen_lt Complex.continuous_im continuous_const).inter isOpen_const)

theorem convex_sameOpenHalfPlane {v : ℂ} (hv : v.im ≠ 0) :
    Convex ℝ {u | SameOpenHalfPlane u v} := by
  rcases lt_or_gt_of_ne hv with hv | hv
  · have he : {u | SameOpenHalfPlane u v} = Complex.imLm ⁻¹' Set.Iio 0 := by
      ext u
      simp only [SameOpenHalfPlane, Set.mem_setOf_eq, Set.mem_preimage, Complex.imLm_coe, Set.mem_Iio]
      constructor
      · rintro (⟨_,h⟩ | ⟨h,_⟩)
        · linarith
        · exact h
      · exact fun h => Or.inr ⟨h,hv⟩
    rw [he]
    exact (convex_Iio (0:ℝ)).linear_preimage Complex.imLm
  · have he : {u | SameOpenHalfPlane u v} = Complex.imLm ⁻¹' Set.Ioi 0 := by
      ext u
      simp only [SameOpenHalfPlane, Set.mem_setOf_eq, Set.mem_preimage, Complex.imLm_coe, Set.mem_Ioi]
      constructor
      · rintro (⟨h,_⟩ | ⟨_,h⟩)
        · exact h
        · linarith
      · exact fun h => Or.inl ⟨h,hv⟩
    rw [he]
    exact (convex_Ioi (0:ℝ)).linear_preimage Complex.imLm

/-- Straight-path primitives have the exact cocycle relation in either half-plane. -/
theorem integrated_nevanlinna_ratioPath_cocycle (s : AnchoredCountingState)
    {u v b : ℂ} (hub : SameOpenHalfPlane u b) (hvb : SameOpenHalfPlane v b) :
    (∫ t : RatioInterval, (u-v)*anchoredNevanlinna s (ratioPath u v t) ∂ratioIntervalMeasure) =
      (∫ t : RatioInterval, (u-b)*anchoredNevanlinna s (ratioPath u b t) ∂ratioIntervalMeasure) -
      (∫ t : RatioInterval, (v-b)*anchoredNevanlinna s (ratioPath v b t) ∂ratioIntervalMeasure) := by
  let P := fun z a => ∫ t : RatioInterval, (z-a)*anchoredNevanlinna s (ratioPath z a t) ∂ratioIntervalMeasure
  have hd₁ (z : ℂ) (hz : SameOpenHalfPlane z b) : HasDerivAt (fun z => P z v) (anchoredNevanlinna s z) z :=
    hasDerivAt_integrated_nevanlinna_ratioPath s (hz.trans hvb.symm)
  have hd₂ (z : ℂ) (hz : SameOpenHalfPlane z b) : HasDerivAt (fun z => P z b - P v b) (anchoredNevanlinna s z) z :=
    (hasDerivAt_integrated_nevanlinna_ratioPath s hz).sub_const _
  have hh := (isOpen_sameOpenHalfPlane b).eqOn_of_deriv_eq
    (convex_sameOpenHalfPlane hvb.right_offReal).isPreconnected
    (fun z hz => (hd₁ z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hd₂ z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hd₁ z hz).deriv.trans (hd₂ z hz).deriv.symm) hvb
    (show P v v = P v b - P v b by simp [P])
  exact hh hub

/-- The genuine integrated ratio factors through any base in its half-plane. -/
theorem anchoredCharacteristicRatio_cocycle (s : AnchoredCountingState)
    {u v b : ℂ} (hub : SameOpenHalfPlane u b) (hvb : SameOpenHalfPlane v b) :
    anchoredCharacteristicRatio s u v =
      anchoredCharacteristicRatio s u b * anchoredCharacteristicRatio s b v := by
  rw [anchoredCharacteristicRatio_swap s b v]
  simp only [anchoredCharacteristicRatio, neg_mul, integral_neg, ← Complex.exp_neg, ← Complex.exp_add]
  congr 1
  rw [integrated_nevanlinna_ratioPath_cocycle s hub hvb]
  ring

theorem analyticAt_anchoredCharacteristicRatio_numerator (s : AnchoredCountingState)
    {u v : ℂ} (huv : SameOpenHalfPlane u v) :
    AnalyticAt ℂ (fun z => anchoredCharacteristicRatio s z v) u := by
  exact (show DifferentiableOn ℂ (fun z => anchoredCharacteristicRatio s z v)
    {z | SameOpenHalfPlane z v} from fun z hz =>
      (hasDerivAt_anchoredCharacteristicRatio s hz).differentiableAt.differentiableWithinAt).analyticAt
        (sameOpenHalfPlane_nhds huv)

theorem analyticAt_anchoredCharacteristicRatio_denominator (s : AnchoredCountingState)
    {u v : ℂ} (huv : SameOpenHalfPlane u v) :
    AnalyticAt ℂ (fun z => anchoredCharacteristicRatio s u z) v := by
  have heq : (fun z => anchoredCharacteristicRatio s u z) =
      (fun z => (anchoredCharacteristicRatio s z u)⁻¹) :=
    funext (fun z => anchoredCharacteristicRatio_swap s u z)
  rw [heq]
  exact (analyticAt_anchoredCharacteristicRatio_numerator s huv.symm).inv
    (anchoredCharacteristicRatio_ne_zero s v u)

/-- Pointwise ratios are genuinely jointly analytic in numerator and denominator. -/
theorem analyticAt_anchoredCharacteristicRatio_joint (s : AnchoredCountingState)
    {u v : ℂ} (huv : SameOpenHalfPlane u v) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => anchoredCharacteristicRatio s p.1 p.2) (u,v) := by
  have h₁ := (analyticAt_anchoredCharacteristicRatio_numerator s huv).comp
    ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt (u,v))
  have h₂ := (analyticAt_anchoredCharacteristicRatio_denominator s
    (sameOpenHalfPlane_self_of_offReal huv.right_offReal)).comp
    ((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt (u,v))
  apply (h₁.mul h₂).congr
  filter_upwards [(continuous_fst.tendsto (u,v)).eventually (sameOpenHalfPlane_nhds huv),
    (continuous_snd.tendsto (u,v)).eventually
      (sameOpenHalfPlane_nhds (sameOpenHalfPlane_self_of_offReal huv.right_offReal))] with p hp₁ hp₂
  exact (anchoredCharacteristicRatio_cocycle s hp₁ hp₂).symm

/-- The finite ratio product is jointly analytic in all numerator and denominator coordinates. -/
theorem analyticAt_anchoredCharacteristicRatios_joint {q : ℕ} (s : AnchoredCountingState)
    (u v : Fin q → ℂ) (huv : ∀ j, SameOpenHalfPlane (u j) (v j)) :
    AnalyticAt ℂ (fun p : (Fin q → ℂ) × (Fin q → ℂ) => anchoredCharacteristicRatios s p.1 p.2) (u,v) := by
  have h (I : Finset (Fin q)) :
      AnalyticAt ℂ (fun p : (Fin q → ℂ) × (Fin q → ℂ) =>
        ∏ j ∈ I, anchoredCharacteristicRatio s (p.1 j) (p.2 j)) (u,v) := by
    classical
    induction I using Finset.induction_on with
    | empty => simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : (Fin q → ℂ) × (Fin q → ℂ) => (1:ℂ)) (u,v))
    | @insert j I hj ih =>
      have hcoord := (((ContinuousLinearMap.proj (R := ℂ) j).comp
        (ContinuousLinearMap.fst ℂ (Fin q → ℂ) (Fin q → ℂ))).analyticAt (u,v)).prod
        (((ContinuousLinearMap.proj (R := ℂ) j).comp
          (ContinuousLinearMap.snd ℂ (Fin q → ℂ) (Fin q → ℂ))).analyticAt (u,v))
      simpa only [Finset.prod_insert hj] using
        ((analyticAt_anchoredCharacteristicRatio_joint s (huv j)).comp
          (f := fun p : (Fin q → ℂ) × (Fin q → ℂ) => (p.1 j,p.2 j)) hcoord).mul ih
  simpa [anchoredCharacteristicRatios] using h Finset.univ

/-- Both orientations admit the same exponential bound from one path tube. -/
theorem norm_anchoredCharacteristicRatio_reverse_le_of_bound (s : AnchoredCountingState)
    (u v : ℂ) (C : ℝ)
    (hb : ∀ t : RatioInterval, ‖anchoredNevanlinna s (ratioPath u v t)‖ ≤ C*‖s.val.2‖) :
    ‖anchoredCharacteristicRatio s v u‖ ≤ Real.exp ((‖u-v‖*C)*‖s.val.2‖) := by
  rw [anchoredCharacteristicRatio_swap s v u, anchoredCharacteristicRatio, ← Complex.exp_neg]
  apply (Complex.norm_exp_le_exp_norm _).trans
  apply Real.exp_le_exp.mpr
  rw [norm_neg]
  have hh := norm_integral_le_of_norm_le_const (μ := ratioIntervalMeasure)
    (C := (‖u-v‖*C)*‖s.val.2‖)
    (f := fun t : RatioInterval => -(u-v)*anchoredNevanlinna s (ratioPath u v t))
    (Filter.Eventually.of_forall (fun t => by
      rw [norm_mul,norm_neg]
      exact (mul_le_mul_of_nonneg_left (hb t) (norm_nonneg _)).trans_eq (by ring)))
  simpa using hh

/-- The scalar Cauchy estimate is uniform in every coefficient, with its exact
geometric radius and no state-dependent hidden constant. -/
theorem norm_cauchyPowerSeries_le_of_bound {f : ℂ → ℂ} {u : ℂ} {R M : ℝ}
    (hR : 0 < R) (hf : ContinuousOn f (Metric.closedBall u R))
    (hb : ∀ z ∈ Metric.closedBall u R, ‖f z‖ ≤ M) (n : ℕ) :
    ‖cauchyPowerSeries f u R n‖ ≤ M/R^n := by
  have hc : Continuous (fun θ : ℝ => f (circleMap u R θ)) :=
    (hf.mono Metric.sphere_subset_closedBall).comp_continuous (continuous_circleMap u R)
      (circleMap_mem_sphere u hR.le)
  have hi : (∫ θ : ℝ in (0)..2*Real.pi, ‖f (circleMap u R θ)‖) ≤ (2*Real.pi)*M := by
    calc
      _ ≤ ∫ _ : ℝ in (0)..2*Real.pi, M :=
        intervalIntegral.integral_mono_on Real.two_pi_pos.le (hc.norm.intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _) (fun θ _ => hb _
            (Metric.sphere_subset_closedBall (circleMap_mem_sphere u hR.le θ)))
      _ = _ := by simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  calc
    _ ≤ ((2*Real.pi)⁻¹ * ∫ θ : ℝ in (0)..2*Real.pi, ‖f (circleMap u R θ)‖) * |R|⁻¹^n :=
      norm_cauchyPowerSeries_le f u R n
    _ ≤ ((2*Real.pi)⁻¹*((2*Real.pi)*M))*|R|⁻¹^n := by
      gcongr
    _ = M/R^n := by rw [inv_mul_cancel_left₀ Real.two_pi_pos.ne', abs_of_pos hR, div_eq_mul_inv, inv_pow]

/-- Forward and reversed ratios have a common Cauchy radius before the state is
chosen, and integrable exponential anchor majorants for all their coefficients. -/
theorem exists_ratio_cauchySeries_uniform {u v : ℂ} (huv : SameOpenHalfPlane u v) :
    ∃ R : ℝ≥0, 0 < R ∧ ∃ L : ℝ, 0 ≤ L ∧
      (∀ z ∈ Metric.closedBall u (R:ℝ), SameOpenHalfPlane z v) ∧
      ∀ s : AnchoredCountingState,
        HasFPowerSeriesOnBall (fun z => anchoredCharacteristicRatio s z v)
          (cauchyPowerSeries (fun z => anchoredCharacteristicRatio s z v) u R) u R ∧
        HasFPowerSeriesOnBall (fun z => anchoredCharacteristicRatio s v z)
          (cauchyPowerSeries (fun z => anchoredCharacteristicRatio s v z) u R) u R ∧
        ∀ n, ‖cauchyPowerSeries (fun z => anchoredCharacteristicRatio s z v) u R n‖ ≤
            Real.exp (L*‖s.val.2‖)/(R:ℝ)^n ∧
          ‖cauchyPowerSeries (fun z => anchoredCharacteristicRatio s v z) u R n‖ ≤
            Real.exp (L*‖s.val.2‖)/(R:ℝ)^n := by
  obtain ⟨R,hR,K,hK,hKoff,hSame,hPath⟩ := exists_ratioPath_compact_tube huv
  obtain ⟨C,hC,hb⟩ := exists_compact_resolvent_anchor_bound hK hKoff
  let L := (‖u-v‖+R)*C
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hb' (s : AnchoredCountingState) (z : ℂ) (hz : z ∈ Metric.closedBall u R) :
      ‖anchoredCharacteristicRatio s z v‖ ≤ Real.exp (L*‖s.val.2‖) ∧
      ‖anchoredCharacteristicRatio s v z‖ ≤ Real.exp (L*‖s.val.2‖) := by
    have hnorm : ‖z-v‖ ≤ ‖u-v‖+R := by
      have ht := norm_add_le (z-u) (u-v)
      rw [sub_add_sub_cancel] at ht
      have hz' : ‖z-u‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
      linarith
    have he : Real.exp ((‖z-v‖*C)*‖s.val.2‖) ≤ Real.exp (L*‖s.val.2‖) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hnorm hC) (norm_nonneg _))
    exact ⟨(norm_anchoredCharacteristicRatio_le_of_bound s z v C (fun t => hb s _ (hPath z hz t))).trans he,
      (norm_anchoredCharacteristicRatio_reverse_le_of_bound s z v C (fun t => hb s _ (hPath z hz t))).trans he⟩
  refine ⟨⟨R,hR.le⟩,hR,L,hL,hSame,fun s => ?_⟩
  have hd₁ : DifferentiableOn ℂ (fun z => anchoredCharacteristicRatio s z v) (Metric.closedBall u R) :=
    fun z hz => (hasDerivAt_anchoredCharacteristicRatio s (hSame z hz)).differentiableAt.differentiableWithinAt
  have hd₂ : DifferentiableOn ℂ (fun z => anchoredCharacteristicRatio s v z) (Metric.closedBall u R) :=
    fun z hz => (hasDerivAt_anchoredCharacteristicRatio_denominator s (hSame z hz).symm).differentiableAt.differentiableWithinAt
  refine ⟨hd₁.hasFPowerSeriesOnBall hR,hd₂.hasFPowerSeriesOnBall hR, fun n => ?_⟩
  exact ⟨norm_cauchyPowerSeries_le_of_bound hR hd₁.continuousOn (fun z hz => (hb' s z hz).1) n,
    norm_cauchyPowerSeries_le_of_bound hR hd₂.continuousOn (fun z hz => (hb' s z hz).2) n⟩

/-- The preceding uniform scalar expansions have genuinely measurable coefficients
in the random state, in both orientations. -/
theorem exists_ratio_cauchySeries_uniform_measurable {u v : ℂ}
    (huv : SameOpenHalfPlane u v) :
    ∃ R : ℝ≥0, 0 < R ∧ ∃ L : ℝ, 0 ≤ L ∧
      (∀ n, StronglyMeasurable (fun s : AnchoredCountingState =>
        cauchyPowerSeries (fun z => anchoredCharacteristicRatio s z v) u R n)) ∧
      (∀ n, StronglyMeasurable (fun s : AnchoredCountingState =>
        cauchyPowerSeries (fun z => anchoredCharacteristicRatio s v z) u R n)) ∧
      ∀ s : AnchoredCountingState,
        HasFPowerSeriesOnBall (fun z => anchoredCharacteristicRatio s z v)
          (cauchyPowerSeries (fun z => anchoredCharacteristicRatio s z v) u R) u R ∧
        HasFPowerSeriesOnBall (fun z => anchoredCharacteristicRatio s v z)
          (cauchyPowerSeries (fun z => anchoredCharacteristicRatio s v z) u R) u R ∧
        ∀ n, ‖cauchyPowerSeries (fun z => anchoredCharacteristicRatio s z v) u R n‖ ≤
            Real.exp (L*‖s.val.2‖)/(R:ℝ)^n ∧
          ‖cauchyPowerSeries (fun z => anchoredCharacteristicRatio s v z) u R n‖ ≤
            Real.exp (L*‖s.val.2‖)/(R:ℝ)^n := by
  obtain ⟨R,hR,L,hL,hSame,hp⟩ := exists_ratio_cauchySeries_uniform huv
  have hcircle (θ : ℝ) : SameOpenHalfPlane (circleMap u R θ) v :=
    hSame _ (Metric.sphere_subset_closedBall (circleMap_mem_sphere u R.coe_nonneg θ))
  exact ⟨R,hR,L,hL,
    stronglyMeasurable_ratio_cauchyPowerSeries u v R hcircle,
    stronglyMeasurable_reverseRatio_cauchyPowerSeries u v R (fun θ => (hcircle θ).symm),hp⟩

end BourgadeHuang
