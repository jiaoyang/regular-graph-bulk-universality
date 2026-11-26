import BourgadeHuang.EntireRatioMeasurability
import BourgadeHuang.CharacteristicRatioJointExpectation
import BourgadeHuang.EntireRatioReflection

/-! Uniform exponential anchor bounds for the genuine entire numerator. -/
noncomputable section
open scoped Topology BigOperators NNReal ENNReal
open MeasureTheory Filter
namespace BourgadeHuang

theorem norm_anchoredLinearCoefficient_le_anchor (s : AnchoredCountingState) :
    ‖(anchoredLinearCoefficient s:ℂ)‖ ≤ ‖s.val.2‖ := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (anchoredLinearCoefficient_nonneg s)]
  exact (sub_le_self _ (integral_nonneg nevanlinnaWeight_nonneg)).trans (Complex.im_le_norm _)

theorem norm_entireNumerator_exponent_le (R : ℝ) (_hR : 0 ≤ R)
    (s : AnchoredCountingState) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖-s.val.2*(z-Complex.I)-(anchoredLinearCoefficient s:ℂ)*(z-Complex.I)^2/2‖ ≤
      ((R+1)+(R+1)^2/2)*‖s.val.2‖ := by
  have hdist : ‖z-Complex.I‖ ≤ R+1 :=
    (norm_sub_le z Complex.I).trans (by simpa using add_le_add_right hz 1)
  calc
    _ ≤ ‖-s.val.2*(z-Complex.I)‖+‖(anchoredLinearCoefficient s:ℂ)*(z-Complex.I)^2/2‖ := norm_sub_le _ _
    _ = ‖s.val.2‖*‖z-Complex.I‖+‖(anchoredLinearCoefficient s:ℂ)‖*‖z-Complex.I‖^2/2 := by
      simp only [norm_mul,norm_neg,norm_div,norm_pow,Complex.norm_ofNat]
    _ ≤ ‖s.val.2‖*(R+1)+‖s.val.2‖*(R+1)^2/2 := by
      gcongr
      exact norm_anchoredLinearCoefficient_le_anchor s
    _ = _ := by ring

/-- An explicit compact-disk growth coefficient, independent of the state. -/
def entireNumeratorGrowthConstant (R : ℝ) : ℝ :=
  (R+1)+(R+1)^2/2+(R+1)^2*Real.exp (R+1)

theorem entireNumeratorGrowthConstant_nonneg {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ entireNumeratorGrowthConstant R := by unfold entireNumeratorGrowthConstant; positivity

theorem norm_canonicalParticleProduct_le (R : ℝ) (hR : 0 ≤ R)
    (s : AnchoredCountingState) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖canonicalParticleProduct s z‖ ≤
      Real.exp (((R+1)^2*Real.exp (R+1))*‖s.val.2‖) := by
  let C := (R+1)^2*Real.exp (R+1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hsum : (∑' i : s.val.1.ParticleLabels, nevanlinnaWeight (s.val.1.particleLocation i)) =
      ∫ x, nevanlinnaWeight x ∂s.val.1.measure :=
    (s.val.1.hasSum_particleLocations s.integrable_weight).tsum_eq
  have hb := norm_tprod_le_exp_tsum (s.summable_particle_weight.mul_left C)
    (fun i => norm_canonicalParticleFactor_sub_one_le R hR (s.val.1.particleLocation i) z hz)
  change ‖canonicalParticleProduct s z‖ ≤ Real.exp
    (∑' i : s.val.1.ParticleLabels, C*nevanlinnaWeight (s.val.1.particleLocation i)) at hb
  rw [tsum_mul_left,hsum] at hb
  exact hb.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
    (s.integral_weight_le_im.trans (Complex.im_le_norm _)) hC))

/-- Every compact numerator disk has a uniform exponential anchor majorant. -/
theorem norm_anchoredEntireNumerator_le (R : ℝ) (hR : 0 ≤ R)
    (s : AnchoredCountingState) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖anchoredEntireNumerator s z‖ ≤ Real.exp (entireNumeratorGrowthConstant R*‖s.val.2‖) := by
  rw [anchoredEntireNumerator,norm_mul]
  calc
    _ ≤ Real.exp (((R+1)+(R+1)^2/2)*‖s.val.2‖)*
        Real.exp (((R+1)^2*Real.exp (R+1))*‖s.val.2‖) :=
      mul_le_mul ((Complex.norm_exp_le_exp_norm _).trans
        (Real.exp_le_exp.mpr (norm_entireNumerator_exponent_le R hR s hz)))
        (norm_canonicalParticleProduct_le R hR s hz) (norm_nonneg _) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; unfold entireNumeratorGrowthConstant; ring

/-- A scalar Cauchy expansion is an anchored analytic family when its genuine
circle evaluations are measurable and have a uniform exponential bound. -/
theorem hasAnchoredPowerSeries_of_uniform_circle_bound
    (F : AnchoredCountingState → ℂ → ℂ) (u : ℂ) (R : ℝ≥0) (hR : 0 < R)
    (L : ℝ) (hL : 0 ≤ L)
    (hd : ∀ s z, z ∈ Metric.closedBall u (R:ℝ) → DifferentiableAt ℂ (F s) z)
    (hm : ∀ z ∈ Metric.sphere u (R:ℝ), Measurable (fun s => F s z))
    (hb : ∀ s z, z ∈ Metric.closedBall u (R:ℝ) → ‖F s z‖ ≤ Real.exp (L*‖s.val.2‖)) :
    HasAnchoredPowerSeries F u := by
  have hcoeff (n : ℕ) : StronglyMeasurable (fun s => cauchyPowerSeries (F s) u R n) := by
    apply stronglyMeasurable_cauchyPowerSeries_of_circle
    apply measurable_uncurry_of_continuous_of_measurable
      (u := fun θ : ℝ => fun s : AnchoredCountingState => F s (circleMap u R θ))
    · intro s
      apply continuous_iff_continuousAt.mpr
      intro θ
      exact (hd s _ (Metric.sphere_subset_closedBall (circleMap_mem_sphere u R.coe_nonneg θ))).continuousAt.comp
        (continuous_circleMap u R).continuousAt
    · intro θ
      exact hm _ (circleMap_mem_sphere u R.coe_nonneg θ)
  refine ⟨R,hR,fun s => cauchyPowerSeries (F s) u R,L,hL,hcoeff,fun s => ?_,fun s n => ?_⟩
  · have hOn : DifferentiableOn ℂ (F s) (Metric.closedBall u (R:ℝ)) :=
      fun z hz => (hd s z hz).differentiableWithinAt
    exact hOn.hasFPowerSeriesOnBall hR
  · exact norm_cauchyPowerSeries_le_of_bound hR
      (fun z hz => (hd s z hz).continuousAt.continuousWithinAt) (hb s) n

/-- The inverse normalized numerator has a common exponential bound on a
neighborhood of every off-real denominator. -/
theorem exists_inverseEntireNumerator_bound {v : ℂ} (hv : v.im ≠ 0) :
    ∃ R : ℝ≥0, 0 < R ∧ ∃ L : ℝ, 0 ≤ L ∧
      (∀ z ∈ Metric.closedBall v (R:ℝ), z.im ≠ 0) ∧
      ∀ s : AnchoredCountingState, ∀ z ∈ Metric.closedBall v (R:ℝ),
        ‖(anchoredEntireNumerator s z)⁻¹‖ ≤ Real.exp (L*‖s.val.2‖) := by
  obtain ⟨b,hvb,hb⟩ : ∃ b : ℂ, SameOpenHalfPlane v b ∧
      ∀ s : AnchoredCountingState, ‖anchoredEntireNumerator s b‖ = 1 := by
    rcases lt_or_gt_of_ne hv with hneg | hpos
    · exact ⟨-Complex.I,Or.inr ⟨hneg,by simp⟩,norm_anchoredEntireNumerator_neg_I⟩
    · exact ⟨Complex.I,Or.inl ⟨hpos,by simp⟩,fun s => by simp⟩
  obtain ⟨R,hR,K,hK,hKoff,hSame,hPath⟩ := exists_ratioPath_compact_tube hvb
  obtain ⟨C,hC,hbound⟩ := exists_compact_resolvent_anchor_bound hK hKoff
  let L := (‖v-b‖+R)*C
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨⟨R,hR.le⟩,hR,L,hL,fun z hz => (hSame z hz).left_offReal,fun s z hz => ?_⟩
  have he : ‖(anchoredEntireNumerator s z)⁻¹‖ = ‖anchoredCharacteristicRatio s b z‖ := by
    rw [← entireCharacteristicRatio_eq_anchored s (hSame z hz).symm]
    simp only [entireCharacteristicRatio,norm_div,hb s,one_div,norm_inv]
  rw [he]
  have hnorm : ‖z-b‖ ≤ ‖v-b‖+R := by
    have ht := norm_add_le (z-v) (v-b)
    rw [sub_add_sub_cancel] at ht
    have hz' : ‖z-v‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
    linarith
  exact (norm_anchoredCharacteristicRatio_reverse_le_of_bound s z b C
    (fun t => hbound s _ (hPath z hz t))).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hnorm hC) (norm_nonneg _)))

theorem hasAnchoredPowerSeries_inverseEntireNumerator {v : ℂ} (hv : v.im ≠ 0) :
    HasAnchoredPowerSeries (fun s z => (anchoredEntireNumerator s z)⁻¹) v := by
  obtain ⟨R,hR,L,hL,hoff,hb⟩ := exists_inverseEntireNumerator_bound hv
  apply hasAnchoredPowerSeries_of_uniform_circle_bound _ v R hR L hL
  · intro s z hz
    exact (differentiable_anchoredEntireNumerator s z).inv
      (anchoredEntireNumerator_ne_zero s (hoff z hz))
  · intro z _
    exact (measurable_anchoredEntireNumerator z).inv
  · exact hb

/-- The normalized entire numerator is an anchored analytic family at every
complex point, including the real axis and the opposite half-plane. -/
theorem hasAnchoredPowerSeries_entireNumerator (u : ℂ) :
    HasAnchoredPowerSeries anchoredEntireNumerator u := by
  apply hasAnchoredPowerSeries_of_uniform_circle_bound _ u 1 (by norm_num)
    (entireNumeratorGrowthConstant (‖u‖+1)) (entireNumeratorGrowthConstant_nonneg (by positivity))
  · intro s z _
    exact differentiable_anchoredEntireNumerator s z
  · intro z _
    exact measurable_anchoredEntireNumerator z
  · intro s z hz
    apply norm_anchoredEntireNumerator_le (‖u‖+1) (by positivity) s
    have hz' : ‖z-u‖ ≤ 1 := by simpa only [Metric.mem_closedBall,dist_eq_norm,NNReal.coe_one] using hz
    have h := norm_add_le (z-u) u
    rw [sub_add_cancel] at h
    linarith

end BourgadeHuang
