import BourgadeHuang.EntireCharacteristicRatio
import BourgadeHuang.CharacteristicRatioCauchyMeasurability

/-! Measurability of the entire characteristic numerator. The actual Cauchy
coefficients are recovered on a fixed upper-half-plane circle, so no measurable
choice of a particle enumeration is required. -/
noncomputable section
open scoped Topology BigOperators NNReal ENNReal
open MeasureTheory Filter Complex
namespace BourgadeHuang

lemma im_pos_of_mem_sphere_I_half {z : ℂ}
    (hz : z ∈ Metric.sphere Complex.I (1/2 : ℝ)) : 0 < z.im := by
  have hn : ‖z-Complex.I‖ = (1/2 : ℝ) := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
  have hi := (abs_le.mp (Complex.abs_im_le_norm (z-Complex.I))).1
  simp only [Complex.sub_im, Complex.I_im] at hi
  rw [hn] at hi
  linarith

lemma sameOpenHalfPlane_circle_I_half (θ : ℝ) :
    SameOpenHalfPlane (circleMap Complex.I (1/2) θ) Complex.I :=
  Or.inl ⟨im_pos_of_mem_sphere_I_half (circleMap_mem_sphere _ (by norm_num) _), by simp⟩

lemma anchoredEntireNumerator_eq_ratio_I (s : AnchoredCountingState) {z : ℂ}
    (hz : 0 < z.im) :
    anchoredEntireNumerator s z = anchoredCharacteristicRatio s z Complex.I := by
  simpa only [entireCharacteristicRatio, anchoredEntireNumerator_I, div_one] using
    entireCharacteristicRatio_eq_anchored s (u := z) (v := Complex.I) (Or.inl ⟨hz, by simp⟩)

lemma cauchyPowerSeries_entireNumerator_eq (s : AnchoredCountingState) :
    cauchyPowerSeries (anchoredEntireNumerator s) Complex.I (1/2) =
      cauchyPowerSeries (fun z => anchoredCharacteristicRatio s z Complex.I) Complex.I (1/2) := by
  funext n
  unfold cauchyPowerSeries
  congr 2
  apply circleIntegral.integral_congr (by norm_num)
  intro z hz
  dsimp only
  rw [anchoredEntireNumerator_eq_ratio_I s (im_pos_of_mem_sphere_I_half hz)]

theorem stronglyMeasurable_cauchyPowerSeries_entireNumerator (n : ℕ) :
    StronglyMeasurable (fun s : AnchoredCountingState =>
      cauchyPowerSeries (anchoredEntireNumerator s) Complex.I (1/2) n) := by
  simp_rw [cauchyPowerSeries_entireNumerator_eq]
  exact stronglyMeasurable_ratio_cauchyPowerSeries Complex.I Complex.I (1/2)
    sameOpenHalfPlane_circle_I_half n

theorem stronglyMeasurable_anchoredEntireNumerator (z : ℂ) :
    StronglyMeasurable (fun s : AnchoredCountingState => anchoredEntireNumerator s z) := by
  let a := fun (n : ℕ) (s : AnchoredCountingState) =>
    cauchyPowerSeries (anchoredEntireNumerator s) Complex.I (1/2) n (fun _ => z-Complex.I)
  have ha (n : ℕ) : StronglyMeasurable (a n) :=
    (ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => ℂ) ℂ (fun _ => z-Complex.I)).continuous.comp_stronglyMeasurable
      (stronglyMeasurable_cauchyPowerSeries_entireNumerator n)
  have hs (s : AnchoredCountingState) : HasSum (fun n => a n s) (anchoredEntireNumerator s z) := by
    have h := (differentiable_anchoredEntireNumerator s).hasFPowerSeriesOnBall Complex.I
      (R := (1/2 : ℝ≥0)) (by norm_num)
    simpa only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using
      h.hasSum_sub (y := z) (by simp)
  apply stronglyMeasurable_of_tendsto Filter.atTop
    (f := fun N s => ∑ n ∈ Finset.range N, a n s)
  · intro N
    exact Finset.stronglyMeasurable_sum _ (fun n _ => ha n)
  · exact tendsto_pi_nhds.mpr (fun s => (hs s).tendsto_sum_nat)

theorem measurable_anchoredEntireNumerator (z : ℂ) :
    Measurable (fun s : AnchoredCountingState => anchoredEntireNumerator s z) :=
  (stronglyMeasurable_anchoredEntireNumerator z).measurable

theorem measurable_entireCharacteristicRatio (u v : ℂ) :
    Measurable (fun s : AnchoredCountingState => entireCharacteristicRatio s u v) :=
  (measurable_anchoredEntireNumerator u).div (measurable_anchoredEntireNumerator v)

theorem measurable_uncurry_anchoredEntireNumerator :
    Measurable (fun p : ℂ × AnchoredCountingState => anchoredEntireNumerator p.2 p.1) := by
  apply measurable_uncurry_of_continuous_of_measurable (u := fun z s => anchoredEntireNumerator s z)
  · intro s
    exact (differentiable_anchoredEntireNumerator s).continuous
  · exact measurable_anchoredEntireNumerator

end BourgadeHuang
