import GeneralizedBulk.Gaussian.GlobalConstruction
import GeneralizedBulk.Analysis.FiberProducts
import GeneralizedBulk.Analysis.PolynomialMoments
import GeneralizedBulk.Exterior.RawStationarity

/-! Weighted response integrability follows from proved conditional second
moments and scalar anchor moments. Gaussian moments above order two are not
assumed, and integrability of a stationary response is not an input. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped BigOperators
namespace GeneralizedBulk.Gaussian.Response

variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (P : Measure S) (Q : Measure T) (X : S → AnchoredCountingState)

/-- A local analytic estimate used below. For the actual Gaussian field it is
constructed from the infinite L² series by `control_presented_version`. -/
structure ConditionalL2 (F : S → T → ℂ) : Prop where
  memLp : ∀ᵐ x ∂P, MemLp (F x) 2 Q
  bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ x ∂P,
    (∫ γ, ‖F x γ‖ ^ 2 ∂Q) ≤ C * (1 + ‖(X x).val.2‖ ^ 2)

variable {P Q X}

namespace ConditionalL2

theorem congr_ae {F G : S → T → ℂ} (hF : ConditionalL2 P Q X F)
    (h : ∀ᵐ x ∂P, F x =ᵐ[Q] G x) : ConditionalL2 P Q X G := by
  constructor
  · filter_upwards [hF.memLp, h] with x hx heq
    exact (memLp_congr_ae heq).1 hx
  · obtain ⟨C, hC, hb⟩ := hF.bound
    refine ⟨C, hC, ?_⟩
    filter_upwards [hb, h] with x hx heq
    rw [← integral_congr_ae (heq.mono fun γ hγ => congrArg (fun z : ℂ => ‖z‖ ^ 2) hγ)]
    exact hx

theorem one [IsProbabilityMeasure Q] : ConditionalL2 P Q X (fun _ _ => 1) := by
  constructor
  · exact Eventually.of_forall (fun _ => memLp_const _)
  · refine ⟨1, by norm_num, Eventually.of_forall (fun x => ?_)⟩
    simp only [norm_one, one_pow, integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul]
    nlinarith [sq_nonneg ‖(X x).val.2‖]

end ConditionalL2

/-- Finite scalar anchor moments control the extra quadratic factor in the
conditional second moments, even after multiplying by any scalar polynomial. -/
theorem integrable_weight_norm_anchor_square [IsFiniteMeasure P]
    (hX : Measurable X)
    (hm : ∀ n : ℕ, Integrable (fun x => ‖(X x).val.2‖ ^ n) P)
    (weight : S → ℂ) (hw : Analysis.AllMoments P weight) :
    Integrable (fun x => ‖weight x‖ * (1 + ‖(X x).val.2‖ ^ 2)) P := by
  have ha : AEStronglyMeasurable (fun x => ‖(X x).val.2‖) P :=
    ((measurable_snd.comp (measurable_subtype_coe.comp hX)).norm).aestronglyMeasurable
  have hpmeas : AEStronglyMeasurable (fun x => 1 + ‖(X x).val.2‖ ^ 2) P :=
    (aestronglyMeasurable_const.add (ha.pow 2))
  have hpint : Integrable (fun x => (1 + ‖(X x).val.2‖ ^ 2) ^ 2) P := by
    apply (((integrable_const (1 : ℝ)).add (hm 4)).const_mul 2).mono' (hpmeas.pow 2)
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change (1 + ‖(X x).val.2‖ ^ 2) ^ 2 ≤ 2 * (1 + ‖(X x).val.2‖ ^ 4)
    nlinarith [sq_nonneg (‖(X x).val.2‖ ^ 2 - 1)]
  have hp : MemLp (fun x => 1 + ‖(X x).val.2‖ ^ 2) 2 P :=
    (memLp_two_iff_integrable_sq hpmeas).2 hpint
  have hwp : MemLp (fun x => ‖weight x‖) 2 P :=
    (memLp_two_iff_integrable_sq hw.measurable.norm).2 (hw.norm_pow 2)
  exact hwp.integrable_mul hp

/-- Conditional L², proved for the actual marks, is sufficient for every
scalar-polynomial weighted entry product. -/
theorem integrable_weighted_product [IsFiniteMeasure P] [IsProbabilityMeasure Q]
    (hX : Measurable X)
    (hm : ∀ n : ℕ, Integrable (fun x => ‖(X x).val.2‖ ^ n) P)
    (F G : S → T → ℂ) (weight : S → ℂ)
    (hF : ConditionalL2 P Q X F) (hG : ConditionalL2 P Q X G)
    (hw : Analysis.AllMoments P weight)
    (hf : AEStronglyMeasurable (fun z : S × T => F z.1 z.2) (P.prod Q))
    (hg : AEStronglyMeasurable (fun z : S × T => G z.1 z.2) (P.prod Q)) :
    Integrable (fun z : S × T => weight z.1 * F z.1 z.2 * G z.1 z.2) (P.prod Q) := by
  obtain ⟨C, hC, hb⟩ := hF.bound
  obtain ⟨D, hD, hd⟩ := hG.bound
  apply Analysis.integrable_weighted_product_of_second_moments P Q F G weight
    (fun x => C * (1 + ‖(X x).val.2‖ ^ 2))
    (fun x => D * (1 + ‖(X x).val.2‖ ^ 2))
  · exact ((hw.measurable.fst).mul hf).mul hg
  · filter_upwards [hF.memLp] with x hx
    exact hx.integrable_norm_pow'
  · filter_upwards [hG.memLp] with x hx
    exact hx.integrable_norm_pow'
  · exact hb
  · exact hd
  · convert (integrable_weight_norm_anchor_square hX hm weight hw).const_mul ((C + D) / 2) using 1
    funext x
    ring

theorem integrable_weighted_entry [IsFiniteMeasure P] [IsProbabilityMeasure Q]
    (hX : Measurable X)
    (hm : ∀ n : ℕ, Integrable (fun x => ‖(X x).val.2‖ ^ n) P)
    (F : S → T → ℂ) (weight : S → ℂ)
    (hF : ConditionalL2 P Q X F) (hw : Analysis.AllMoments P weight)
    (hf : AEStronglyMeasurable (fun z : S × T => F z.1 z.2) (P.prod Q)) :
    Integrable (fun z : S × T => weight z.1 * F z.1 z.2) (P.prod Q) := by
  simpa only [mul_one] using integrable_weighted_product hX hm F (fun _ _ => 1) weight
    hF ConditionalL2.one hw hf aestronglyMeasurable_const

/-- Every scalar resolvent has all moments, proved from its single-anchor bound. -/
theorem scalar_allMoments [IsFiniteMeasure P]
    (hX : Measurable X)
    (hm : ∀ n : ℕ, Integrable (fun x => ‖(X x).val.2‖ ^ n) P)
    {w : ℂ} (hw : w.im ≠ 0) :
    Analysis.AllMoments P (fun x => anchoredNevanlinna (X x) w) := by
  refine ⟨((continuous_anchoredNevanlinna hw).measurable.comp hX).aestronglyMeasurable, fun n => ?_⟩
  apply ((hm n).const_mul (scalarValueEnvelope w ^ n)).mono'
    ((((continuous_anchoredNevanlinna hw).measurable.comp hX).norm.pow_const n).aestronglyMeasurable)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _)
    (norm_anchoredNevanlinna_le_anchor (X x) hw) n

theorem scalarProduct_allMoments [IsFiniteMeasure P]
    (hX : Measurable X)
    (hm : ∀ n : ℕ, Integrable (fun x => ‖(X x).val.2‖ ^ n) P)
    {n : ℕ} (aux : Fin n → ℂ) (ha : ∀ j, (aux j).im ≠ 0) :
    Analysis.AllMoments P (fun x => Loop.scalarProduct (X x) aux) := by
  exact Analysis.AllMoments.finset_prod Finset.univ _
    (fun j _ => scalar_allMoments hX hm (ha j))

theorem scalarExcludedProduct_allMoments [IsFiniteMeasure P]
    (hX : Measurable X)
    (hm : ∀ n : ℕ, Integrable (fun x => ‖(X x).val.2‖ ^ n) P)
    {n : ℕ} (aux : Fin n → ℂ) (ha : ∀ j, (aux j).im ≠ 0) (j : Fin n) :
    Analysis.AllMoments P (fun x => Loop.scalarExcludedProduct (X x) aux j) := by
  exact Analysis.AllMoments.finset_prod (Finset.univ.erase j) _
    (fun k _ => scalar_allMoments hX hm (ha k))

/-- An arbitrary fixed finite linear matrix trace is integrable with scalar
polynomial weights. -/
theorem integrable_weighted_linear_trace [IsFiniteMeasure P] [IsProbabilityMeasure Q]
    (hX : Measurable X)
    (hm : ∀ n : ℕ, Integrable (fun x => ‖(X x).val.2‖ ^ n) P)
    (F : S → T → EndpointMatrix) (A : EndpointMatrix) (weight : S → ℂ)
    (hF : ∀ i j, ConditionalL2 P Q X (fun x γ => F x γ i j))
    (hw : Analysis.AllMoments P weight)
    (hf : ∀ i j, AEStronglyMeasurable (fun z : S × T => F z.1 z.2 i j) (P.prod Q)) :
    Integrable (fun z : S × T => weight z.1 * Matrix.trace (A * F z.1 z.2)) (P.prod Q) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.mul_sum]
  apply integrable_finset_sum
  intro i hi
  apply integrable_finset_sum
  intro j hj
  convert (integrable_weighted_entry hX hm (fun x γ => F x γ j i) weight (hF j i) hw (hf j i)).const_mul (A i j) using 1
  funext z
  ring

/-- The four fixed matrix factors are fully expanded; only products of two
random entries require conditional second moments. -/
theorem trace_product_entry_expansion (A B F G : EndpointMatrix) :
    Matrix.trace (A * F * B * G) =
      ∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
        (A i k * B j l) * (F k j * G l i) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  ring

/-- Arbitrary fixed quadratic matrix traces need only the already proved
conditional second moments. -/
theorem integrable_weighted_quadratic_trace [IsFiniteMeasure P] [IsProbabilityMeasure Q]
    (hX : Measurable X)
    (hm : ∀ n : ℕ, Integrable (fun x => ‖(X x).val.2‖ ^ n) P)
    (F G : S → T → EndpointMatrix) (A B : EndpointMatrix) (weight : S → ℂ)
    (hF : ∀ i j, ConditionalL2 P Q X (fun x γ => F x γ i j))
    (hG : ∀ i j, ConditionalL2 P Q X (fun x γ => G x γ i j))
    (hw : Analysis.AllMoments P weight)
    (hf : ∀ i j, AEStronglyMeasurable (fun z : S × T => F z.1 z.2 i j) (P.prod Q))
    (hg : ∀ i j, AEStronglyMeasurable (fun z : S × T => G z.1 z.2 i j) (P.prod Q)) :
    Integrable (fun z : S × T => weight z.1 * Matrix.trace (A * F z.1 z.2 * B * G z.1 z.2)) (P.prod Q) := by
  simp_rw [trace_product_entry_expansion]
  simp only [Finset.mul_sum]
  apply integrable_finset_sum
  intro i hi
  apply integrable_finset_sum
  intro j hj
  apply integrable_finset_sum
  intro k hk
  apply integrable_finset_sum
  intro l hl
  convert (integrable_weighted_product hX hm (fun x γ => F x γ k j) (fun x γ => G x γ l i)
    weight (hF k j) (hG l i) hw (hf k j) (hg l i)).const_mul (A i k * B j l) using 1
  funext z
  ring

/-- Translation by the deterministic raw mean retains conditional L² control. -/
theorem ConditionalL2.mean_add [IsProbabilityMeasure Q] (parameters : Parameters)
    {F : S → T → ℂ} (hF : ConditionalL2 P Q X F)
    {w : ℂ} (hw : w.im ≠ 0) (i j : Fin 4) :
    ConditionalL2 P Q X (fun x γ => Marked.mean parameters X w x i j + F x γ) := by
  obtain ⟨C, hC, hb⟩ := hF.bound
  refine ⟨?_, 4 * meanEntryEnvelope parameters w ^ 2 + 2 * C, by positivity, ?_⟩
  · filter_upwards [hF.memLp] with x hx
    exact (memLp_const _).add hx
  · filter_upwards [hF.memLp, hb] with x hx hbx
    have hm := marked_mean_entry_bound parameters (X x) hw i j
    have hm2 := pow_le_pow_left₀ (norm_nonneg _) hm 2
    have hm3 : ‖Marked.mean parameters X w x i j‖ ^ 2 ≤
        2 * meanEntryEnvelope parameters w ^ 2 * (1 + ‖(X x).val.2‖ ^ 2) := by
      apply hm2.trans
      rw [mul_pow]
      nlinarith [mul_nonneg (sq_nonneg (meanEntryEnvelope parameters w)) (sq_nonneg (‖(X x).val.2‖ - 1))]
    apply (integral_norm_sq_const_add_le Q (F x) hx (Marked.mean parameters X w x i j)).trans
    nlinarith

/-- Measurability of each deterministic mean entry. -/
theorem mean_entry_aestronglyMeasurable (parameters : Parameters) (hX : Measurable X)
    {w : ℂ} (hw : w.im ≠ 0) (i j : Fin 4) :
    AEStronglyMeasurable (fun x => Marked.mean parameters X w x i j) P := by
  have hs := (continuous_anchoredNevanlinna hw).measurable.comp hX
  have hg : Measurable (fun x => (parameters.center : ℂ) +
      (parameters.scale : ℂ) * anchoredNevanlinna (X x) w) := measurable_const.add (hs.const_mul _)
  have hb : Measurable (fun x => (parameters.p : ℂ) *
      ((parameters.center : ℂ) + (parameters.scale : ℂ) * anchoredNevanlinna (X x) w) + parameters.r) :=
    (hg.const_mul (parameters.p : ℂ)).add measurable_const
  fin_cases i <;> fin_cases j <;>
    simp [Marked.mean, GeneralizedSwitching.meanMatrix] <;>
      first | exact hg.aestronglyMeasurable | exact hb.aestronglyMeasurable |
        exact aestronglyMeasurable_const

variable [IsFiniteMeasure P] [IsProbabilityMeasure Q]

/-- Weighted drift integrability is a consequence of scalar moments and
conditional second moments, rather than a new stationary-flow assumption. -/
theorem weighted_drift_integrable (parameters : Parameters) (hX : Measurable X)
    (hm : ∀ n : ℕ, Integrable (fun x => ‖(X x).val.2‖ ^ n) P)
    (Z : S → (ℂ × Bool) → T → EndpointMatrix)
    (hZ : ∀ v i j, ConditionalL2 P Q X (fun x γ => Z x v γ i j))
    (hz : ∀ v i j, AEStronglyMeasurable (fun z : S × T => Z z.1 v z.2 i j) (P.prod Q))
    {n : ℕ} {w : ℂ} (hw : w.im ≠ 0) (aux : Fin n → ℂ) (ha : ∀ j, (aux j).im ≠ 0) :
    Integrable (fun z : S × T => Marked.dh parameters X Z w z.1 z.2 *
      Loop.scalarProduct (X z.1) aux) (P.prod Q) := by
  let M := Marked.markedMatrix parameters X Z w
  have hM (i j : Fin 4) : ConditionalL2 P Q X (fun x γ => M x γ i j) :=
    ConditionalL2.mean_add parameters (hZ (w, false) i j) hw i j
  have hmM (i j : Fin 4) : AEStronglyMeasurable (fun z : S × T => M z.1 z.2 i j) (P.prod Q) :=
    (mean_entry_aestronglyMeasurable parameters hX hw i j).fst.add (hz (w, false) i j)
  have hW := scalarProduct_allMoments hX hm aux ha
  have hl := integrable_weighted_linear_trace hX hm M GeneralizedSwitching.edgeMatrix
    (fun x => Loop.scalarProduct (X x) aux) hM hW hmM
  have hq := integrable_weighted_quadratic_trace hX hm M M signMatrix signMatrix
    (fun x => Loop.scalarProduct (X x) aux) hM hM hW hmM hmM
  convert (hl.const_mul 2).add (hq.const_mul 2) using 1
  funext z
  simp only [Marked.dh, trace_matrixResponse, Pi.add_apply]
  dsimp [M]
  ring

/-- The differentiated auxiliary-channel product is integrable using the
same quadratic estimates, including repeated spectral parameters. -/
theorem weighted_cross_integrable (hX : Measurable X)
    (hm : ∀ n : ℕ, Integrable (fun x => ‖(X x).val.2‖ ^ n) P)
    (Z : S → (ℂ × Bool) → T → EndpointMatrix)
    (hZ : ∀ v i j, ConditionalL2 P Q X (fun x γ => Z x v γ i j))
    (hz : ∀ v i j, AEStronglyMeasurable (fun z : S × T => Z z.1 v z.2 i j) (P.prod Q))
    {n : ℕ} (w : ℂ) (aux : Fin n → ℂ) (ha : ∀ j, (aux j).im ≠ 0) (a : Fin n) :
    Integrable (fun z : S × T => (Marked.h Z w z.1 z.2 * Marked.ds Z (aux a) z.1 z.2) *
      Loop.scalarExcludedProduct (X z.1) aux a) (P.prod Q) := by
  have hW := scalarExcludedProduct_allMoments hX hm aux ha a
  have hi (i j : Fin 4) : Integrable (fun z : S × T =>
      (2 * (endpointSign i * endpointSign j)) *
        (Loop.scalarExcludedProduct (X z.1) aux a * Z z.1 (w, false) z.2 i i *
          Z z.1 (aux a, true) z.2 j j)) (P.prod Q) :=
    (integrable_weighted_product hX hm (fun x γ => Z x (w, false) γ i i)
      (fun x γ => Z x (aux a, true) γ j j) _ (hZ _ i i) (hZ _ j j) hW
      (hz _ i i) (hz _ j j)).const_mul _
  have heq (z : S × T) :
      (Marked.h Z w z.1 z.2 * Marked.ds Z (aux a) z.1 z.2) *
          Loop.scalarExcludedProduct (X z.1) aux a =
        ∑ i : Fin 4, ∑ j : Fin 4, (2 * (endpointSign i * endpointSign j)) *
          (Loop.scalarExcludedProduct (X z.1) aux a * Z z.1 (w, false) z.2 i i *
            Z z.1 (aux a, true) z.2 j j) := by
    simp only [Marked.h, Marked.ds]
    calc
      _ = 2 * (Matrix.trace (signMatrix * Z z.1 (w, false) z.2) *
          Matrix.trace (signMatrix * Z z.1 (aux a, true) z.2)) *
            Loop.scalarExcludedProduct (X z.1) aux a := by ring
      _ = _ := by
        rw [trace_sign_mul_trace_sign]
        simp only [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
  simp_rw [heq]
  exact integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hi i j))

/-- The polynomial observable differentiated by the exterior flow is also
integrable; the sign trace of the deterministic mean vanishes identically. -/
theorem polynomialObservable_integrable (parameters : Parameters) (hX : Measurable X)
    (hm : ∀ n : ℕ, Integrable (fun x => ‖(X x).val.2‖ ^ n) P)
    (Z : S → (ℂ × Bool) → T → EndpointMatrix)
    (hZ : ∀ v i j, ConditionalL2 P Q X (fun x γ => Z x v γ i j))
    (hz : ∀ v i j, AEStronglyMeasurable (fun z : S × T => Z z.1 v z.2 i j) (P.prod Q))
    {n : ℕ} (w : ℂ) (aux : Fin n → ℂ) (ha : ∀ j, (aux j).im ≠ 0) :
    Integrable (fun z : S × T => Exterior.rawPolynomialObservable
      (fun u => anchoredNevanlinna (X z.1) u)
      (fun u => Marked.markedMatrix parameters X Z u z.1 z.2) w aux) (P.prod Q) := by
  have h := integrable_weighted_linear_trace hX hm (fun x γ => Z x (w, false) γ)
    signMatrix (fun x => Loop.scalarProduct (X x) aux) (hZ (w, false))
    (scalarProduct_allMoments hX hm aux ha) (hz (w, false))
  convert h using 1
  funext z
  simp only [Exterior.rawPolynomialObservable, ← Marked.h_eq_trace_marked, Marked.h, Loop.scalarProduct]
  ring

/-- The complete marked response is genuinely integrable before its expected
stationary value is calculated by the exterior flow. -/
theorem responseObservable_integrable (parameters : Parameters) (hX : Measurable X)
    (hm : ∀ n : ℕ, Integrable (fun x => ‖(X x).val.2‖ ^ n) P)
    (Z : S → (ℂ × Bool) → T → EndpointMatrix)
    (hZ : ∀ v i j, ConditionalL2 P Q X (fun x γ => Z x v γ i j))
    (hz : ∀ v i j, AEStronglyMeasurable (fun z : S × T => Z z.1 v z.2 i j) (P.prod Q))
    {n : ℕ} {w : ℂ} (hw : w.im ≠ 0) (aux : Fin n → ℂ) (ha : ∀ j, (aux j).im ≠ 0) :
    Integrable (Loop.responseObservable X (Marked.h Z) (Marked.dh parameters X Z) (Marked.ds Z) w aux) (P.prod Q) := by
  exact (weighted_drift_integrable parameters hX hm Z hZ hz hw aux ha).add
    (integrable_finset_sum _ (fun j _ => weighted_cross_integrable hX hm Z hZ hz w aux ha j))

section ActualConstruction
variable {I : Type*} [Countable I]
variable (P : Measure S) [IsProbabilityMeasure P]
    (Y : S → PresentedState I) (hY : Measurable Y)
    (hm1 : Integrable (fun x => ‖(Y x).scalar.val.2‖) P) (parameters : Parameters)

/-- The conditional estimate used by the weighted-response proof is a theorem
of the explicitly constructed Gaussian model, with no moment premise on marks. -/
theorem constructedZ_conditionalL2 (v : ℂ × Bool) (i j : Fin 4) :
    ConditionalL2 P (iidLaw (markLaw parameters.p) I) (fun x => (Y x).scalar)
      (fun x γ => constructedZ P Y hY hm1 parameters x v γ i j) := by
  refine ⟨constructedZ_memLp_two P Y hY hm1 parameters v i j,
    2 * ‖(parameters.scale : ℂ)‖ ^ 2 * coefficientSquareEnvelope v, ?_,
    constructedZ_second_moment P Y hY hm1 parameters v i j⟩
  have := coefficientSquareEnvelope_nonneg v
  positivity

theorem constructedZ_joint_measurable (v : ℂ × Bool) (i j : Fin 4) :
    AEStronglyMeasurable (fun z : S × (I → (Fin 4 → ℝ)) =>
      constructedZ P Y hY hm1 parameters z.1 v z.2 i j)
      (P.prod (iidLaw (markLaw parameters.p) I)) := by
  exact (((continuous_apply j).comp (continuous_apply i)).measurable.comp
    (measurable_constructedField P Y hY hm1 parameters v)).aestronglyMeasurable

/-- Actual weighted Gaussian drift integrability, from scalar anchor moments. -/
theorem constructed_weighted_drift_integrable
    (hm : ∀ n : ℕ, Integrable (fun x => ‖(Y x).scalar.val.2‖ ^ n) P)
    {n : ℕ} {w : ℂ} (hw : w.im ≠ 0) (aux : Fin n → ℂ) (ha : ∀ j, (aux j).im ≠ 0) :
    Integrable (fun z : S × (I → (Fin 4 → ℝ)) =>
      Marked.dh parameters (fun x => (Y x).scalar) (constructedZ P Y hY hm1 parameters) w z.1 z.2 *
        Loop.scalarProduct (Y z.1).scalar aux) (P.prod (iidLaw (markLaw parameters.p) I)) := by
  exact weighted_drift_integrable parameters (PresentedState.measurable_scalar.comp hY) hm _
    (constructedZ_conditionalL2 P Y hY hm1 parameters)
    (constructedZ_joint_measurable P Y hY hm1 parameters) hw aux ha

/-- Actual weighted cross-channel integrability, including coincident parameters. -/
theorem constructed_weighted_cross_integrable
    (hm : ∀ n : ℕ, Integrable (fun x => ‖(Y x).scalar.val.2‖ ^ n) P)
    {n : ℕ} (w : ℂ) (aux : Fin n → ℂ) (ha : ∀ j, (aux j).im ≠ 0) (a : Fin n) :
    Integrable (fun z : S × (I → (Fin 4 → ℝ)) =>
      (Marked.h (constructedZ P Y hY hm1 parameters) w z.1 z.2 *
        Marked.ds (constructedZ P Y hY hm1 parameters) (aux a) z.1 z.2) *
          Loop.scalarExcludedProduct (Y z.1).scalar aux a) (P.prod (iidLaw (markLaw parameters.p) I)) := by
  exact weighted_cross_integrable (PresentedState.measurable_scalar.comp hY) hm _
    (constructedZ_conditionalL2 P Y hY hm1 parameters)
    (constructedZ_joint_measurable P Y hY hm1 parameters) w aux ha a

/-- Actual polynomial observable integrability for the raw-to-exterior flow. -/
theorem constructed_polynomialObservable_integrable
    (hm : ∀ n : ℕ, Integrable (fun x => ‖(Y x).scalar.val.2‖ ^ n) P)
    {n : ℕ} (w : ℂ) (aux : Fin n → ℂ) (ha : ∀ j, (aux j).im ≠ 0) :
    Integrable (fun z : S × (I → (Fin 4 → ℝ)) => Exterior.rawPolynomialObservable
      (fun u => anchoredNevanlinna (Y z.1).scalar u)
      (fun u => Marked.markedMatrix parameters (fun x => (Y x).scalar)
        (constructedZ P Y hY hm1 parameters) u z.1 z.2) w aux)
      (P.prod (iidLaw (markLaw parameters.p) I)) := by
  exact polynomialObservable_integrable parameters (PresentedState.measurable_scalar.comp hY) hm _
    (constructedZ_conditionalL2 P Y hY hm1 parameters)
    (constructedZ_joint_measurable P Y hY hm1 parameters) w aux ha

/-- Actual expanded polynomial response integrability for exterior differentiation. -/
theorem constructed_responseObservable_integrable
    (hm : ∀ n : ℕ, Integrable (fun x => ‖(Y x).scalar.val.2‖ ^ n) P)
    {n : ℕ} {w : ℂ} (hw : w.im ≠ 0) (aux : Fin n → ℂ) (ha : ∀ j, (aux j).im ≠ 0) :
    Integrable (Loop.responseObservable (fun x => (Y x).scalar)
      (Marked.h (constructedZ P Y hY hm1 parameters))
      (Marked.dh parameters (fun x => (Y x).scalar) (constructedZ P Y hY hm1 parameters))
      (Marked.ds (constructedZ P Y hY hm1 parameters)) w aux)
      (P.prod (iidLaw (markLaw parameters.p) I)) := by
  exact responseObservable_integrable parameters (PresentedState.measurable_scalar.comp hY) hm _
    (constructedZ_conditionalL2 P Y hY hm1 parameters)
    (constructedZ_joint_measurable P Y hY hm1 parameters) hw aux ha

end ActualConstruction
end GeneralizedBulk.Gaussian.Response
