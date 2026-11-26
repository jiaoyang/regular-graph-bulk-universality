import BourgadeHuang.EntireRatioExpectation
import BourgadeHuang.ExponentialRatioDerivatives

/-! # Genuine orthogonal characteristic ratios

The two denominator factors have exponent one half. The branch is fixed by a
straight-path primitive in their common half-plane, while the numerator remains
entire. No principal square root or unproved branch choice is used.
-/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang

/-- The positive straight-path primitive of the reconstructed resolvent. -/
def nevanlinnaPathPrimitive (s : AnchoredCountingState) (u v : ℂ) : ℂ :=
  ∫ t : RatioInterval, (u-v)*anchoredNevanlinna s (ratioPath u v t) ∂ratioIntervalMeasure

@[simp] theorem nevanlinnaPathPrimitive_self (s : AnchoredCountingState) (v : ℂ) :
    nevanlinnaPathPrimitive s v v = 0 := by simp [nevanlinnaPathPrimitive]

theorem anchoredCharacteristicRatio_eq_exp_primitive (s : AnchoredCountingState) (u v : ℂ) :
    anchoredCharacteristicRatio s u v = Complex.exp (-nevanlinnaPathPrimitive s u v) := by
  simp only [anchoredCharacteristicRatio, nevanlinnaPathPrimitive, neg_mul, integral_neg]

theorem nevanlinnaPathPrimitive_cocycle (s : AnchoredCountingState) {u v b : ℂ}
    (hub : SameOpenHalfPlane u b) (hvb : SameOpenHalfPlane v b) :
    nevanlinnaPathPrimitive s u v =
      nevanlinnaPathPrimitive s u b - nevanlinnaPathPrimitive s v b :=
  integrated_nevanlinna_ratioPath_cocycle s hub hvb

theorem nevanlinnaPathPrimitive_swap (s : AnchoredCountingState) {u v : ℂ}
    (huv : SameOpenHalfPlane u v) :
    nevanlinnaPathPrimitive s u v = -nevanlinnaPathPrimitive s v u := by
  simpa only [nevanlinnaPathPrimitive_self, zero_sub] using
    nevanlinnaPathPrimitive_cocycle s
      (sameOpenHalfPlane_self_of_offReal huv.left_offReal) huv.symm

theorem hasDerivAt_nevanlinnaPathPrimitive_numerator (s : AnchoredCountingState) {u v : ℂ}
    (huv : SameOpenHalfPlane u v) :
    HasDerivAt (fun z => nevanlinnaPathPrimitive s z v) (anchoredNevanlinna s u) u :=
  hasDerivAt_integrated_nevanlinna_ratioPath s huv

theorem hasDerivAt_nevanlinnaPathPrimitive_denominator (s : AnchoredCountingState) {u v : ℂ}
    (huv : SameOpenHalfPlane u v) :
    HasDerivAt (fun z => nevanlinnaPathPrimitive s u z) (-anchoredNevanlinna s v) v := by
  apply (hasDerivAt_nevanlinnaPathPrimitive_numerator s huv.symm).neg.congr_of_eventuallyEq
  filter_upwards [sameOpenHalfPlane_nhds huv.symm] with z hz
  exact nevanlinnaPathPrimitive_swap s hz.symm

theorem measurable_nevanlinnaPathPrimitive {u v : ℂ} (huv : SameOpenHalfPlane u v) :
    Measurable (fun s => nevanlinnaPathPrimitive s u v) := by
  have h := (measurable_integrated_nevanlinna_ratioPath huv).neg
  simpa only [neg_mul, integral_neg, neg_neg, nevanlinnaPathPrimitive] using h

/-- The entire numerator divided by the coherently chosen square root of two
characteristic denominators. The denominator arguments must share a half-plane
for the analytic and normalization theorems. -/
def orthogonalCharacteristicRatio (s : AnchoredCountingState) (u v w : ℂ) : ℂ :=
  entireCharacteristicRatio s u v * Complex.exp ((1/2 : ℂ)*nevanlinnaPathPrimitive s w v)

@[simp] theorem orthogonalCharacteristicRatio_diagonal (s : AnchoredCountingState) (u v : ℂ) :
    orthogonalCharacteristicRatio s u v v = entireCharacteristicRatio s u v := by
  simp [orthogonalCharacteristicRatio]

theorem orthogonalCharacteristicRatio_eq_exp (s : AnchoredCountingState) {u v w : ℂ}
    (huv : SameOpenHalfPlane u v) :
    orthogonalCharacteristicRatio s u v w =
      Complex.exp (-nevanlinnaPathPrimitive s u v + (1/2:ℂ)*nevanlinnaPathPrimitive s w v) := by
  rw [orthogonalCharacteristicRatio, entireCharacteristicRatio_eq_anchored s huv,
    anchoredCharacteristicRatio_eq_exp_primitive, Complex.exp_add]

theorem hasDerivAt_entireCharacteristicRatio_denominator (s : AnchoredCountingState)
    (u : ℂ) {v : ℂ} (hv : v.im ≠ 0) :
    HasDerivAt (fun z => entireCharacteristicRatio s u z)
      (anchoredNevanlinna s v * entireCharacteristicRatio s u v) v := by
  have h := (hasDerivAt_const v (anchoredEntireNumerator s u)).div
    (hasDerivAt_anchoredEntireNumerator s hv) (anchoredEntireNumerator_ne_zero s hv)
  convert h using 1
  unfold entireCharacteristicRatio
  field_simp [anchoredEntireNumerator_ne_zero s hv]
  ring

theorem differentiable_orthogonalCharacteristicRatio_numerator
    (s : AnchoredCountingState) (v w : ℂ) :
    Differentiable ℂ (fun u => orthogonalCharacteristicRatio s u v w) :=
  (differentiable_entireCharacteristicRatio_numerator s v).mul_const _

theorem hasDerivAt_orthogonalCharacteristicRatio_numerator (s : AnchoredCountingState)
    {u v w : ℂ} (hu : u.im ≠ 0) :
    HasDerivAt (fun z => orthogonalCharacteristicRatio s z v w)
      (-anchoredNevanlinna s u * orthogonalCharacteristicRatio s u v w) u := by
  convert (hasDerivAt_entireCharacteristicRatio_numerator s (v := v) hu).mul_const
    (Complex.exp ((1/2:ℂ)*nevanlinnaPathPrimitive s w v)) using 1
  simp only [orthogonalCharacteristicRatio]
  ring

theorem hasDerivAt_orthogonalCharacteristicRatio_last (s : AnchoredCountingState)
    (u : ℂ) {v w : ℂ} (hwv : SameOpenHalfPlane w v) :
    HasDerivAt (fun z => orthogonalCharacteristicRatio s u v z)
      ((1/2:ℂ)*anchoredNevanlinna s w * orthogonalCharacteristicRatio s u v w) w := by
  convert (((hasDerivAt_nevanlinnaPathPrimitive_numerator s hwv).const_mul (1/2:ℂ)).cexp).const_mul
    (entireCharacteristicRatio s u v) using 1
  simp only [orthogonalCharacteristicRatio]
  ring

theorem hasDerivAt_orthogonalCharacteristicRatio_middle (s : AnchoredCountingState)
    (u : ℂ) {v w : ℂ} (hwv : SameOpenHalfPlane w v) :
    HasDerivAt (fun z => orthogonalCharacteristicRatio s u z w)
      ((1/2:ℂ)*anchoredNevanlinna s v * orthogonalCharacteristicRatio s u v w) v := by
  convert (hasDerivAt_entireCharacteristicRatio_denominator s u hwv.right_offReal).mul
    (((hasDerivAt_nevanlinnaPathPrimitive_denominator s hwv).const_mul (1/2:ℂ)).cexp) using 1
  simp only [orthogonalCharacteristicRatio]
  ring

theorem measurable_orthogonalCharacteristicRatio (u : ℂ) {v w : ℂ}
    (hwv : SameOpenHalfPlane w v) :
    Measurable (fun s => orthogonalCharacteristicRatio s u v w) :=
  (measurable_entireCharacteristicRatio u v).mul
    (Complex.measurable_exp.comp ((measurable_nevanlinnaPathPrimitive hwv).const_mul _))


theorem entireCharacteristicRatio_mul (s : AnchoredCountingState) (u w : ℂ) {v : ℂ}
    (hv : v.im ≠ 0) :
    entireCharacteristicRatio s u v * entireCharacteristicRatio s v w =
      entireCharacteristicRatio s u w := by
  simp only [entireCharacteristicRatio]
  field_simp [anchoredEntireNumerator_ne_zero s hv]

theorem entireCharacteristicRatio_mul_exp_primitive (s : AnchoredCountingState)
    (u : ℂ) {v w : ℂ} (hwv : SameOpenHalfPlane w v) :
    entireCharacteristicRatio s u v * Complex.exp (nevanlinnaPathPrimitive s w v) =
      entireCharacteristicRatio s u w := by
  have he : Complex.exp (nevanlinnaPathPrimitive s w v) =
      entireCharacteristicRatio s v w := by
    rw [entireCharacteristicRatio_eq_anchored s hwv.symm,
      anchoredCharacteristicRatio_eq_exp_primitive, nevanlinnaPathPrimitive_swap s hwv.symm,
      neg_neg]
  rw [he, entireCharacteristicRatio_mul s u w hwv.right_offReal]

/-- The chosen branch has exactly the intended square, including real numerators
where the entire numerator can vanish. -/
theorem orthogonalCharacteristicRatio_sq (s : AnchoredCountingState) (u : ℂ)
    {v w : ℂ} (hwv : SameOpenHalfPlane w v) :
    orthogonalCharacteristicRatio s u v w ^ 2 =
      entireCharacteristicRatio s u v * entireCharacteristicRatio s u w := by
  have he : Complex.exp ((1/2:ℂ)*nevanlinnaPathPrimitive s w v)^2 =
      Complex.exp (nevanlinnaPathPrimitive s w v) := by
    rw [pow_two, ← Complex.exp_add]
    congr 1
    ring
  rw [orthogonalCharacteristicRatio, mul_pow, he,
    ← entireCharacteristicRatio_mul_exp_primitive s u hwv]
  ring

/-- The analytic branch is symmetric in its two denominator arguments. -/
theorem orthogonalCharacteristicRatio_swap_denominators (s : AnchoredCountingState)
    (u : ℂ) {v w : ℂ} (hwv : SameOpenHalfPlane w v) :
    orthogonalCharacteristicRatio s u v w = orthogonalCharacteristicRatio s u w v := by
  rw [orthogonalCharacteristicRatio, orthogonalCharacteristicRatio,
    ← entireCharacteristicRatio_mul_exp_primitive s u hwv,
    nevanlinnaPathPrimitive_swap s hwv.symm, mul_assoc, ← Complex.exp_add]
  congr 2
  ring

theorem norm_nevanlinnaPathPrimitive_le_of_bound (s : AnchoredCountingState)
    (u v : ℂ) (C : ℝ)
    (hb : ∀ t : RatioInterval, ‖anchoredNevanlinna s (ratioPath u v t)‖ ≤ C*‖s.val.2‖) :
    ‖nevanlinnaPathPrimitive s u v‖ ≤ (‖u-v‖*C)*‖s.val.2‖ := by
  apply (norm_integral_le_of_norm_le_const (μ := ratioIntervalMeasure)
    (C := (‖u-v‖*C)*‖s.val.2‖) _).trans_eq (by simp)
  exact Filter.Eventually.of_forall (fun t => by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hb t) (norm_nonneg _)).trans_eq (by ring))

theorem anchoredExponentialBound_exp_primitive (c : ℂ) {u v : ℂ}
    (huv : SameOpenHalfPlane u v) :
    AnchoredExponentialBound (fun s => Complex.exp (c*nevanlinnaPathPrimitive s u v)) := by
  obtain ⟨R,hR,K,hK,hKoff,_,hPath⟩ := exists_ratioPath_compact_tube huv
  obtain ⟨C,_,hb⟩ := exists_compact_resolvent_anchor_bound hK hKoff
  refine ⟨‖c‖*(‖u-v‖*C), fun s => ?_⟩
  apply (Complex.norm_exp_le_exp_norm _).trans
  apply Real.exp_le_exp.mpr
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left (norm_nevanlinnaPathPrimitive_le_of_bound s u v C
    (fun t => hb s _ (hPath u (Metric.mem_closedBall_self hR.le) t)))
      (norm_nonneg _)).trans_eq (by ring)

theorem anchoredExponentialBound_orthogonalCharacteristicRatio (u : ℂ) {v w : ℂ}
    (hwv : SameOpenHalfPlane w v) :
    AnchoredExponentialBound (fun s => orthogonalCharacteristicRatio s u v w) :=
  (anchoredExponentialBound_entireCharacteristicRatio u hwv.right_offReal).mul
    (anchoredExponentialBound_exp_primitive (1/2:ℂ) hwv)

theorem integrable_orthogonalCharacteristicRatio
    (ν : Measure AnchoredCountingState) {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (u : ℂ) {v w : ℂ} (hwv : SameOpenHalfPlane w v) :
    Integrable (fun s => orthogonalCharacteristicRatio s u v w) ν := by
  obtain ⟨L,hL⟩ := anchoredExponentialBound_orthogonalCharacteristicRatio u hwv
  have hi := integrable_anchor_polynomial_exp ν ha he (by norm_num : (0:ℝ) ≤ 1) 0 L
  simp only [pow_zero,mul_one,one_mul] at hi
  exact hi.mono' (measurable_orthogonalCharacteristicRatio u hwv).aestronglyMeasurable
    (Filter.Eventually.of_forall hL)

def orthogonalCharacteristicRatios {q : ℕ} (s : AnchoredCountingState)
    (u v w : Fin q → ℂ) : ℂ := ∏ j, orthogonalCharacteristicRatio s (u j) (v j) (w j)

theorem measurable_orthogonalCharacteristicRatios {q : ℕ} (u v w : Fin q → ℂ)
    (hwv : ∀ j, SameOpenHalfPlane (w j) (v j)) :
    Measurable (fun s => orthogonalCharacteristicRatios s u v w) :=
  Finset.measurable_prod _ (fun j _ => measurable_orthogonalCharacteristicRatio (u j) (hwv j))

theorem anchoredExponentialBound_orthogonalCharacteristicRatios {q : ℕ}
    (u v w : Fin q → ℂ) (hwv : ∀ j, SameOpenHalfPlane (w j) (v j)) :
    AnchoredExponentialBound (fun s => orthogonalCharacteristicRatios s u v w) :=
  AnchoredExponentialBound.finset_prod _ _
    (fun j _ => anchoredExponentialBound_orthogonalCharacteristicRatio (u j) (hwv j))

theorem integrable_orthogonalCharacteristicRatios {q : ℕ}
    (ν : Measure AnchoredCountingState) {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (u v w : Fin q → ℂ) (hwv : ∀ j, SameOpenHalfPlane (w j) (v j)) :
    Integrable (fun s => orthogonalCharacteristicRatios s u v w) ν := by
  obtain ⟨L,hL⟩ := anchoredExponentialBound_orthogonalCharacteristicRatios u v w hwv
  have hi := integrable_anchor_polynomial_exp ν ha he (by norm_num : (0:ℝ) ≤ 1) 0 L
  simp only [pow_zero,mul_one,one_mul] at hi
  exact hi.mono' (measurable_orthogonalCharacteristicRatios u v w hwv).aestronglyMeasurable
    (Filter.Eventually.of_forall hL)

end BourgadeHuang
