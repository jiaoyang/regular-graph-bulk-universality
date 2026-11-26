import BourgadeHuang.MultipairCharacteristicRatio
import BourgadeHuang.NevanlinnaTransformUniqueness
import BourgadeHuang.CharacteristicRatioMeasurability

/-! # Determination of anchored laws by finite characteristic ratios

Repeated ratios along shrinking paths converge to arbitrary exponential
resolvent sources. Exponential-square anchor tails justify expectation limits,
so equality of ratio expectations determines the full anchored probability law.
-/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang

/-- A numerator approaching its denominator along the prescribed source. -/
def ratioApproxNumerator (z c : ℂ) (n : ℕ) : ℂ :=
  z - (atomRecoveryHeight n : ℂ) * c

theorem tendsto_ratioApproxNumerator (z c : ℂ) :
    Tendsto (ratioApproxNumerator z c) atTop (𝓝 z) := by
  simpa only [ratioApproxNumerator, Complex.ofReal_zero, zero_mul, sub_zero] using
    tendsto_const_nhds.sub (tendsto_atomRecoveryHeight.ofReal.mul_const c)

theorem sameOpenHalfPlane_self_of_offReal {z : ℂ} (hz : z.im ≠ 0) :
    SameOpenHalfPlane z z := by
  rcases lt_or_gt_of_ne hz with h | h
  · exact Or.inr ⟨h,h⟩
  · exact Or.inl ⟨h,h⟩

/-- One compact off-real tube controls every sufficiently short source path,
with a bound independent of both the state and the approximation index. -/
theorem ratioApproxPath_eventually_bounded {z : ℂ} (hz : z.im ≠ 0) (c : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      SameOpenHalfPlane (ratioApproxNumerator z c n) z ∧
      ∀ s : AnchoredCountingState, ∀ t : RatioInterval,
        ‖anchoredNevanlinna s (ratioPath (ratioApproxNumerator z c n) z t)‖ ≤ C*‖s.val.2‖ := by
  obtain ⟨R,hR,K,hK,hKoff,hSame,hPath⟩ :=
    exists_ratioPath_compact_tube (sameOpenHalfPlane_self_of_offReal hz)
  obtain ⟨C,hC,hb⟩ := exists_compact_resolvent_anchor_bound hK hKoff
  refine ⟨C,hC,?_⟩
  filter_upwards [(tendsto_ratioApproxNumerator z c).eventually (Metric.closedBall_mem_nhds z hR)] with n hn
  exact ⟨hSame _ hn, fun s t => hb s _ (hPath _ hn t)⟩

theorem tendsto_ratioApproxPath_integral (s : AnchoredCountingState)
    {z : ℂ} (hz : z.im ≠ 0) (c : ℂ) :
    Tendsto (fun n => ∫ t : RatioInterval,
      anchoredNevanlinna s (ratioPath (ratioApproxNumerator z c n) z t) ∂ratioIntervalMeasure)
      atTop (𝓝 (anchoredNevanlinna s z)) := by
  obtain ⟨C,hC,hbound⟩ := ratioApproxPath_eventually_bounded hz c
  have hh := tendsto_integral_filter_of_dominated_convergence
    (μ := ratioIntervalMeasure) (l := atTop)
    (F := fun n : ℕ => fun t : RatioInterval =>
      anchoredNevanlinna s (ratioPath (ratioApproxNumerator z c n) z t))
    (f := fun _ : RatioInterval => anchoredNevanlinna s z)
    (fun _ => C*‖s.val.2‖) ?_ ?_ (integrable_const _) ?_
  · simpa using hh
  · filter_upwards [hbound] with n hn
    have hc : Continuous (fun t : RatioInterval =>
        anchoredNevanlinna s (ratioPath (ratioApproxNumerator z c n) z t)) := by
      exact (continuous_anchoredNevanlinna_offReal s).comp
        (((continuous_ratioPath (ratioApproxNumerator z c n) z).comp continuous_subtype_val).subtype_mk
          (fun t : RatioInterval => ratioPath_offReal hn.1 t.property))
    exact hc.aestronglyMeasurable
  · filter_upwards [hbound] with n hn
    exact Filter.Eventually.of_forall (hn.2 s)
  · apply Filter.Eventually.of_forall
    intro t
    have ht : Tendsto (fun n => ratioPath (ratioApproxNumerator z c n) z t) atTop (𝓝 z) := by
      simpa only [ratioPath, sub_self, mul_zero, add_zero] using
        tendsto_const_nhds.add (((tendsto_ratioApproxNumerator z c).sub_const z).const_mul (t:ℂ))
    exact (differentiableAt_anchoredNevanlinna s hz).continuousAt.tendsto.comp ht

/-- The renormalized finite source associated with the short-path ratios. -/
def ratioApproxSource {q : ℕ} (z c : Fin q → ℂ) (n : ℕ) (s : AnchoredCountingState) : ℂ :=
  ∑ j, c j * ∫ t : RatioInterval,
    anchoredNevanlinna s (ratioPath (ratioApproxNumerator (z j) (c j) n) (z j) t) ∂ratioIntervalMeasure

theorem tendsto_ratioApproxSource {q : ℕ} (z c : Fin q → ℂ)
    (hz : ∀ j, (z j).im ≠ 0) (s : AnchoredCountingState) :
    Tendsto (fun n => ratioApproxSource z c n s) atTop (𝓝 (finiteNevanlinnaSource z c s)) := by
  apply tendsto_finset_sum
  intro j _
  exact (tendsto_ratioApproxPath_integral s (hz j) (c j)).const_mul (c j)

theorem ratioApproxSource_eventually_bounded {q : ℕ} (z c : Fin q → ℂ)
    (hz : ∀ j, (z j).im ≠ 0) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ᶠ n : ℕ in atTop,
      (∀ j, SameOpenHalfPlane (ratioApproxNumerator (z j) (c j) n) (z j)) ∧
      ∀ s : AnchoredCountingState, ‖ratioApproxSource z c n s‖ ≤ L*‖s.val.2‖ := by
  choose C hC hb using fun j => ratioApproxPath_eventually_bounded (hz j) (c j)
  refine ⟨∑ j, ‖c j‖*C j, Finset.sum_nonneg (fun j _ => mul_nonneg (norm_nonneg _) (hC j)), ?_⟩
  filter_upwards [Filter.eventually_all.mpr hb] with n hn
  refine ⟨fun j => (hn j).1, fun s => ?_⟩
  calc
    _ ≤ ∑ j, ‖c j * ∫ t : RatioInterval,
        anchoredNevanlinna s (ratioPath (ratioApproxNumerator (z j) (c j) n) (z j) t) ∂ratioIntervalMeasure‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j, ‖c j‖*(C j*‖s.val.2‖) := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa using norm_integral_le_of_norm_le_const
        (μ := ratioIntervalMeasure) (Filter.Eventually.of_forall ((hn j).2 s))
    _ = (∑ j, ‖c j‖*C j)*‖s.val.2‖ := by rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intros; ring

/-- Repeating each small ratio exactly `n+1` times realizes the exponential
of the renormalized source, with no asymptotic algebra left implicit. -/
theorem exp_ratioApproxSource_eq_product {q : ℕ} (z c : Fin q → ℂ)
    (n : ℕ) (s : AnchoredCountingState) :
    Complex.exp (ratioApproxSource z c n s) =
      ∏ j, (anchoredCharacteristicRatio s (ratioApproxNumerator (z j) (c j) n) (z j))^(n+1) := by
  rw [ratioApproxSource, Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro j _
  rw [anchoredCharacteristicRatio, ← Complex.exp_nat_mul]
  congr 1
  rw [integral_const_mul]
  have hn : ((n:ℂ)+1) ≠ 0 := by exact_mod_cast (show (n:ℝ)+1 ≠ 0 by positivity)
  simp only [ratioApproxNumerator, sub_sub_cancel_left, neg_neg, Nat.cast_add, Nat.cast_one,
    atomRecoveryHeight, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_add, Complex.ofReal_natCast]
  field_simp

/-- Exponential-square tails justify the repeated-ratio expectation limit. -/
theorem tendsto_integral_exp_ratioApproxSource
    (ν : Measure AnchoredCountingState) {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    {q : ℕ} (z c : Fin q → ℂ) (hz : ∀ j, (z j).im ≠ 0) :
    Tendsto (fun n => ∫ s, Complex.exp (ratioApproxSource z c n s) ∂ν)
      atTop (𝓝 (finiteNevanlinnaTransform ν z c)) := by
  obtain ⟨L,hL,hb⟩ := ratioApproxSource_eventually_bounded z c hz
  have hB : Integrable (fun s : AnchoredCountingState => Real.exp (L*‖s.val.2‖)) ν := by
    simpa only [pow_zero, mul_one, one_mul] using
      integrable_anchor_polynomial_exp ν ha he (by norm_num : (0:ℝ) ≤ 1) 0 L
  apply tendsto_integral_filter_of_dominated_convergence
    (μ := ν) (l := atTop) (fun s : AnchoredCountingState => Real.exp (L*‖s.val.2‖))
  · filter_upwards [hb] with n hn
    simp_rw [exp_ratioApproxSource_eq_product]
    apply Measurable.aestronglyMeasurable
    exact Finset.measurable_prod _ (fun j _ => (measurable_anchoredCharacteristicRatio (hn.1 j)).pow_const (n+1))
  · filter_upwards [hb] with n hn
    exact Filter.Eventually.of_forall (fun s =>
      (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr (hn.2 s)))
  · exact hB
  · exact Filter.Eventually.of_forall (fun s =>
      (Complex.continuous_exp.tendsto _).comp (tendsto_ratioApproxSource z c hz s))

/-- All finite ratio products include the repeated short-path approximants. -/
theorem exp_ratioApproxSource_integral_eq_of_ratio_expectations
    (μ ν : Measure AnchoredCountingState)
    (h : ∀ (q : ℕ) (u v : Fin q → ℂ), (∀ j, SameOpenHalfPlane (u j) (v j)) →
      (∫ s, anchoredCharacteristicRatios s u v ∂μ) =
        ∫ s, anchoredCharacteristicRatios s u v ∂ν)
    {q : ℕ} (z c : Fin q → ℂ) (n : ℕ)
    (hn : ∀ j, SameOpenHalfPlane (ratioApproxNumerator (z j) (c j) n) (z j)) :
    (∫ s, Complex.exp (ratioApproxSource z c n s) ∂μ) =
      ∫ s, Complex.exp (ratioApproxSource z c n s) ∂ν := by
  let ι := Fin q × Fin (n+1)
  let e := (Fintype.equivFin ι).symm
  let u := fun i => ratioApproxNumerator (z (e i).1) (c (e i).1) n
  let v := fun i => z (e i).1
  have hh := h (Fintype.card ι) u v (fun i => hn (e i).1)
  have hprod (s : AnchoredCountingState) :
      anchoredCharacteristicRatios s u v = Complex.exp (ratioApproxSource z c n s) := by
    rw [anchoredCharacteristicRatios, exp_ratioApproxSource_eq_product]
    calc
      (∏ i, anchoredCharacteristicRatio s (u i) (v i)) =
          ∏ p : ι, anchoredCharacteristicRatio s (ratioApproxNumerator (z p.1) (c p.1) n) (z p.1) :=
        e.prod_comp (fun p : ι => anchoredCharacteristicRatio s
          (ratioApproxNumerator (z p.1) (c p.1) n) (z p.1))
      _ = _ := by rw [Fintype.prod_prod_type]; simp
  simpa only [hprod] using hh

/-- Equality of every finite characteristic-ratio expectation determines all
finite complex exponential resolvent transforms. -/
theorem finiteNevanlinnaTransform_eq_of_ratio_expectations
    (μ ν : Measure AnchoredCountingState)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hμ : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) μ)
    (hν : Integrable (fun s : AnchoredCountingState => Real.exp (b*‖s.val.2‖^2)) ν)
    (h : ∀ (q : ℕ) (u v : Fin q → ℂ), (∀ j, SameOpenHalfPlane (u j) (v j)) →
      (∫ s, anchoredCharacteristicRatios s u v ∂μ) =
        ∫ s, anchoredCharacteristicRatios s u v ∂ν)
    {q : ℕ} (z c : Fin q → ℂ) (hz : ∀ j, (z j).im ≠ 0) :
    finiteNevanlinnaTransform μ z c = finiteNevanlinnaTransform ν z c := by
  have hlimμ := tendsto_integral_exp_ratioApproxSource μ ha hμ z c hz
  have hlimν := tendsto_integral_exp_ratioApproxSource ν hb hν z c hz
  obtain ⟨L,hL,hevent⟩ := ratioApproxSource_eventually_bounded z c hz
  apply tendsto_nhds_unique hlimμ
  apply hlimν.congr'
  filter_upwards [hevent] with n hn
  exact (exp_ratioApproxSource_integral_eq_of_ratio_expectations μ ν h z c n hn.1).symm

/-- The actual full anchored law is uniquely determined by the finite ratio
expectations, under the already-proved exponential-square anchor control. -/
theorem anchored_law_eq_of_characteristic_ratio_expectations
    (μ ν : ProbabilityMeasure AnchoredCountingState)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hμ : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) (μ : Measure AnchoredCountingState))
    (hν : Integrable (fun s : AnchoredCountingState => Real.exp (b*‖s.val.2‖^2)) (ν : Measure AnchoredCountingState))
    (h : ∀ (q : ℕ) (u v : Fin q → ℂ), (∀ j, SameOpenHalfPlane (u j) (v j)) →
      (∫ s, anchoredCharacteristicRatios s u v ∂(μ : Measure AnchoredCountingState)) =
        ∫ s, anchoredCharacteristicRatios s u v ∂(ν : Measure AnchoredCountingState)) : μ = ν := by
  apply anchored_law_eq_of_exponential_transforms μ ν
  intro q z c hz
  exact finiteNevanlinnaTransform_eq_of_ratio_expectations (μ : Measure AnchoredCountingState)
    (ν : Measure AnchoredCountingState) ha hb hμ hν h z c hz

/-- Consequently the underlying counting-measure marginals also agree. -/
theorem counting_law_eq_of_characteristic_ratio_expectations
    (μ ν : ProbabilityMeasure AnchoredCountingState)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hμ : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) (μ : Measure AnchoredCountingState))
    (hν : Integrable (fun s : AnchoredCountingState => Real.exp (b*‖s.val.2‖^2)) (ν : Measure AnchoredCountingState))
    (h : ∀ (q : ℕ) (u v : Fin q → ℂ), (∀ j, SameOpenHalfPlane (u j) (v j)) →
      (∫ s, anchoredCharacteristicRatios s u v ∂(μ : Measure AnchoredCountingState)) =
        ∫ s, anchoredCharacteristicRatios s u v ∂(ν : Measure AnchoredCountingState)) :
    anchoredCountingLaw μ = anchoredCountingLaw ν :=
  congrArg anchoredCountingLaw (anchored_law_eq_of_characteristic_ratio_expectations μ ν ha hb hμ hν h)

end BourgadeHuang
