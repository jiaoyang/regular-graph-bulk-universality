import BourgadeHuang.AnchoredStateBorel
import BourgadeHuang.WeakMomentTransfer

/-!
# Measurable compact counts and moments of the constructed limit

Compact-set masses are upper semicontinuous for the vague topology. In an
anchored Nevanlinna state the weighted-mass inequality bounds each compact
count by the anchor, so the actual limiting law has all local count moments.
-/
noncomputable section
open scoped Topology ENNReal
open MeasureTheory Filter
namespace BourgadeHuang

/-- Compact-set mass is upper semicontinuous in the genuine vague topology. -/
theorem LocalCountingMeasure.upperSemicontinuous_compact_mass {K : Set ℝ}
    (hK : IsCompact K) : UpperSemicontinuous (fun ξ : LocalCountingMeasure => ξ.measure K) := by
  have he : (fun ξ : LocalCountingMeasure => ξ.measure K) =
      (fun ξ => ⨅ (f : ℝ → ℝ) (_ : Continuous f) (_ : HasCompactSupport f)
        (_ : Set.EqOn f 1 K) (_ : 0 ≤ f), ENNReal.ofReal (∫ x, f x ∂ξ.measure)) := by
    funext ξ
    exact hK.measure_eq_biInf_integral_hasCompactSupport ξ.measure
  rw [he]
  apply upperSemicontinuous_iInf
  intro f
  apply upperSemicontinuous_iInf
  intro hf
  apply upperSemicontinuous_iInf
  intro hs
  apply upperSemicontinuous_iInf
  intro _
  apply upperSemicontinuous_iInf
  intro _
  exact (ENNReal.continuous_ofReal.comp (continuous_linearStatistic ⟨⟨f, hf⟩, hs⟩)).upperSemicontinuous

/-- Compact counting evaluations are Borel measurable. -/
theorem LocalCountingMeasure.measurable_compact_mass {K : Set ℝ} (hK : IsCompact K) :
    Measurable (fun ξ : LocalCountingMeasure => ξ.measure K) :=
  (LocalCountingMeasure.upperSemicontinuous_compact_mass hK).measurable

/-- The real-valued compact count is measurable as well. -/
theorem LocalCountingMeasure.measurable_compact_count {K : Set ℝ} (hK : IsCompact K) :
    Measurable (fun ξ : LocalCountingMeasure => (ξ.measure K).toReal) :=
  ENNReal.measurable_toReal.comp (LocalCountingMeasure.measurable_compact_mass hK)

/-- Restricting a varying counting measure to a compact set is a measurable
measure-valued map. Closed-set evaluations suffice by a monotone-class argument. -/
theorem LocalCountingMeasure.measurable_restrict_compact {K : Set ℝ} (hK : IsCompact K) :
    Measurable (fun ξ : LocalCountingMeasure => ξ.measure.restrict K) := by
  haveI (ξ : LocalCountingMeasure) : IsFiniteMeasure (ξ.measure.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  apply Measurable.measure_of_isPiSystem
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_isClosed (α := ℝ))) isPiSystem_isClosed
  · intro s hs
    have he : (fun ξ : LocalCountingMeasure => ξ.measure.restrict K s) =
        (fun ξ => ξ.measure (s ∩ K)) := by
      funext ξ
      exact Measure.restrict_apply hs.measurableSet
    rw [he]
    exact LocalCountingMeasure.measurable_compact_mass (hK.inter_left hs)
  · simpa only [Measure.restrict_apply_univ] using LocalCountingMeasure.measurable_compact_mass hK

/-- Every Borel counting evaluation is measurable, not only interval counts. -/
theorem LocalCountingMeasure.measurable_mass {A : Set ℝ} (hA : MeasurableSet A) :
    Measurable (fun ξ : LocalCountingMeasure => ξ.measure A) := by
  have hm (n : ℕ) : Measurable (fun ξ : LocalCountingMeasure =>
      ξ.measure (A ∩ Metric.closedBall 0 (n : ℝ))) := by
    have hh := (Measure.measurable_coe hA).comp
      (LocalCountingMeasure.measurable_restrict_compact (isCompact_closedBall (0 : ℝ) (n : ℝ)))
    simpa only [Function.comp_def, Measure.restrict_apply hA] using hh
  have hmono : Monotone (fun n : ℕ => A ∩ Metric.closedBall (0 : ℝ) (n : ℝ)) := by
    intro n m hnm
    exact Set.inter_subset_inter_right A (Metric.closedBall_subset_closedBall (by exact_mod_cast hnm))
  have he : (fun ξ : LocalCountingMeasure => ξ.measure A) =
      (fun ξ => ⨆ n : ℕ, ξ.measure (A ∩ Metric.closedBall 0 (n : ℝ))) := by
    funext ξ
    rw [← hmono.measure_iUnion, ← Set.inter_iUnion, Metric.iUnion_closedBall_nat, Set.inter_univ]
  rw [he]
  exact .iSup hm

/-- The vague-space realization is a measurable map into the space of measures. -/
theorem LocalCountingMeasure.measurable_measure :
    Measurable (fun ξ : LocalCountingMeasure => ξ.measure) :=
  Measure.measurable_measure.mpr (fun _ hA => LocalCountingMeasure.measurable_mass hA)

/-- The weighted Nevanlinna mass controls every bounded local count. -/
theorem AnchoredCountingState.count_le_anchor (s : AnchoredCountingState)
    {K : Set ℝ} {R : ℝ} (hK : ∀ a ∈ K, |a| ≤ R) :
    (s.val.1.measure K).toReal ≤ (1 + R ^ 2) * ‖s.val.2‖ := by
  have hc : 0 ≤ 1 + R ^ 2 := by positivity
  have hmajor (a : ℝ) (ha : a ∈ K) : 1 ≤ (1 + R ^ 2) * nevanlinnaWeight a := by
    have ha2 : a ^ 2 ≤ R ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg a) (hK a ha) 2
    change 1 ≤ (1 + R ^ 2) * (1 + a ^ 2)⁻¹
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity : 0 < 1 + a ^ 2)).mpr
    nlinarith
  have hm := (s.integrable_weight.const_mul (1 + R ^ 2)).measure_le_integral
    (Filter.Eventually.of_forall (fun a => mul_nonneg hc (nevanlinnaWeight_nonneg a))) hmajor
  have hnonneg : 0 ≤ ∫ a, (1 + R ^ 2) * nevanlinnaWeight a ∂s.val.1.measure :=
    integral_nonneg (fun a => mul_nonneg hc (nevanlinnaWeight_nonneg a))
  calc
    (s.val.1.measure K).toReal ≤ (ENNReal.ofReal (∫ a,
        (1 + R ^ 2) * nevanlinnaWeight a ∂s.val.1.measure)).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
    _ = (1 + R ^ 2) * ∫ a, nevanlinnaWeight a ∂s.val.1.measure := by
      rw [ENNReal.toReal_ofReal hnonneg, integral_const_mul]
    _ ≤ (1 + R ^ 2) * s.val.2.im := mul_le_mul_of_nonneg_left s.integral_weight_le_im hc
    _ ≤ (1 + R ^ 2) * ‖s.val.2‖ := mul_le_mul_of_nonneg_left (Complex.im_le_norm _) hc

/-- An integrable anchor moment implies the corresponding compact count moment. -/
theorem integrable_compact_count_pow_of_anchor_moment
    (ν : Measure AnchoredCountingState) {K : Set ℝ} (hK : IsCompact K) (q : ℕ)
    (hi : Integrable (fun s : AnchoredCountingState => ‖s.val.2‖ ^ q) ν) :
    Integrable (fun s : AnchoredCountingState => (s.val.1.measure K).toReal ^ q) ν := by
  obtain ⟨R, hb⟩ := hK.isBounded.subset_closedBall (0 : ℝ)
  have hbound (a : ℝ) (ha : a ∈ K) : |a| ≤ R := by
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hb ha
  have hm : Measurable (fun s : AnchoredCountingState => (s.val.1.measure K).toReal ^ q) :=
    ((LocalCountingMeasure.measurable_compact_count hK).comp
      (measurable_fst.comp measurable_subtype_coe)).pow_const q
  apply (hi.const_mul ((1 + R ^ 2) ^ q)).mono' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro s
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ENNReal.toReal_nonneg q)]
  calc
    (s.val.1.measure K).toReal ^ q ≤ ((1 + R ^ 2) * ‖s.val.2‖) ^ q :=
      pow_le_pow_left₀ ENNReal.toReal_nonneg (s.count_le_anchor hbound) q
    _ = (1 + R ^ 2) ^ q * ‖s.val.2‖ ^ q := mul_pow _ _ _

/-- Exponential-square anchor control gives exponential-square compact counts. -/
theorem integrable_exp_sq_compact_count_of_anchor
    (ν : Measure AnchoredCountingState) {K : Set ℝ} (hK : IsCompact K)
    {t : ℝ} (ht : 0 < t)
    (hi : Integrable (fun s : AnchoredCountingState => Real.exp (t * ‖s.val.2‖ ^ 2)) ν) :
    ∃ u : ℝ, 0 < u ∧ Integrable (fun s : AnchoredCountingState =>
      Real.exp (u * (s.val.1.measure K).toReal ^ 2)) ν := by
  obtain ⟨R, hb⟩ := hK.isBounded.subset_closedBall (0 : ℝ)
  have hbound (a : ℝ) (ha : a ∈ K) : |a| ≤ R := by
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hb ha
  have hc : 0 < (1 + R ^ 2) ^ 2 := by positivity
  have hu : 0 < t / (1 + R ^ 2) ^ 2 := div_pos ht hc
  refine ⟨t / (1 + R ^ 2) ^ 2, hu, ?_⟩
  have hm : Measurable (fun s : AnchoredCountingState =>
      t / (1 + R ^ 2) ^ 2 * (s.val.1.measure K).toReal ^ 2) :=
    (((LocalCountingMeasure.measurable_compact_count hK).comp
    (measurable_fst.comp measurable_subtype_coe)).pow_const 2).const_mul (t / (1 + R ^ 2) ^ 2)
  apply hi.mono' hm.exp.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro s
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    t / (1 + R ^ 2) ^ 2 * (s.val.1.measure K).toReal ^ 2 ≤
        t / (1 + R ^ 2) ^ 2 * ((1 + R ^ 2) * ‖s.val.2‖) ^ 2 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ ENNReal.toReal_nonneg (s.count_le_anchor hbound) 2) hu.le
    _ = t * ‖s.val.2‖ ^ 2 := by rw [mul_pow]; field_simp; ring

/-- The counting marginal of an actual anchored state law. -/
def anchoredCountingLaw (ν : ProbabilityMeasure AnchoredCountingState) :
    ProbabilityMeasure LocalCountingMeasure :=
  ν.map (measurable_fst.comp measurable_subtype_coe).aemeasurable

end BourgadeHuang
