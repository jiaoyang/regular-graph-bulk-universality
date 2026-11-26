import GeneralizedBulk.Gaussian.SeriesActual
import GeneralizedBulk.Gaussian.PresentedAnalytic
import GeneralizedBulk.MarkedResponse
import BourgadeHuang.CharacteristicRatioSecondDerivative

/-! Conditional second moments of the actual fixed-label analytic Gaussian field. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped BigOperators Topology

namespace GeneralizedBulk.Gaussian

/-- A deterministic envelope for either coefficient square. It depends only
on the spectral slot, never on the scalar configuration or its particles. -/
def coefficientSquareEnvelope (v : ℂ × Bool) : ℝ :=
  derivativeEnvelope v.1 + derivativeEnvelope v.1 ^ 2

theorem coefficientSquareEnvelope_nonneg (v : ℂ × Bool) :
    0 ≤ coefficientSquareEnvelope v := by
  exact add_nonneg (derivativeEnvelope_nonneg _) (sq_nonneg _)

theorem particleCoefficient_sq_le_weight (x : ℝ) (v : ℂ × Bool) :
    ‖particleCoefficient x v‖ ^ 2 ≤ coefficientSquareEnvelope v * nevanlinnaWeight x := by
  by_cases hw : v.1.im = 0
  · simp only [particleCoefficient, hw, ↓reduceIte, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
    exact mul_nonneg (coefficientSquareEnvelope_nonneg _) (nevanlinnaWeight_nonneg _)
  have hR : 0 < |v.1.im| / 2 := by positivity
  have hb := particleCoefficient_derivative_ball_bound x hw (Metric.mem_ball_self hR)
  have hweight : nevanlinnaWeight x ≤ 1 := by
    unfold nevanlinnaWeight
    exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg x])
  have hweightSq : nevanlinnaWeight x ^ 2 ≤ nevanlinnaWeight x := by
    nlinarith [nevanlinnaWeight_nonneg x]
  cases ht : v.2
  · have hn : ‖particleCoefficient x v‖ ^ 2 = ‖particleCoefficient x (v.1, true)‖ := by
      simp [particleCoefficient, hw, ht, norm_pow]
    rw [hn]
    exact hb.trans (by unfold coefficientSquareEnvelope; nlinarith [sq_nonneg (derivativeEnvelope v.1), nevanlinnaWeight_nonneg x])
  · have hsq := pow_le_pow_left₀ (norm_nonneg _) hb 2
    calc
      ‖particleCoefficient x v‖ ^ 2 = ‖particleCoefficient x (v.1, true)‖ ^ 2 := by simp [particleCoefficient, hw, ht]
      _ ≤ (derivativeEnvelope v.1 * nevanlinnaWeight x) ^ 2 := hsq
      _ ≤ derivativeEnvelope v.1 ^ 2 * nevanlinnaWeight x := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_left hweightSq (sq_nonneg _)
      _ ≤ coefficientSquareEnvelope v * nevanlinnaWeight x := by
        unfold coefficientSquareEnvelope
        nlinarith [mul_nonneg (derivativeEnvelope_nonneg v.1) (nevanlinnaWeight_nonneg x)]

variable {I : Type*} [Countable I] {s : AnchoredCountingState}

/-- Weighted local finiteness is quantitatively controlled by the scalar anchor. -/
theorem presented_weight_sum_le_anchor (p : ParticlePresentation s I) :
    (∑' n, nevanlinnaWeight (p.location n)) ≤ ‖s.val.2‖ := by
  rw [(p.hasSum_observable s.integrable_weight).tsum_eq]
  exact s.integral_weight_le_im.trans (Complex.im_le_norm _)

/-- Square-summability has a uniform state bound, including for derivative slots. -/
theorem presented_coefficient_square_sum_le (p : ParticlePresentation s I) (sigma : ℂ)
    (v : ℂ × Bool) :
    (∑' n, ‖sigma * particleCoefficient (p.location n) v‖ ^ 2) ≤
      (‖sigma‖ ^ 2 * coefficientSquareEnvelope v) * ‖s.val.2‖ := by
  have hs : Summable (fun n => ‖sigma * particleCoefficient (p.location n) v‖ ^ 2) := by
    simpa only [norm_mul, mul_pow] using (p.summable_coefficient_sq v).mul_left (‖sigma‖ ^ 2)
  calc
    _ ≤ ∑' n, (‖sigma‖ ^ 2 * coefficientSquareEnvelope v) * nevanlinnaWeight (p.location n) := by
      apply hs.tsum_le_tsum _ (p.summable_weight.mul_left _)
      intro n
      rw [norm_mul, mul_pow]
      exact (mul_le_mul_of_nonneg_left (particleCoefficient_sq_le_weight _ v) (sq_nonneg _)).trans_eq (by ring)
    _ = (‖sigma‖ ^ 2 * coefficientSquareEnvelope v) * ∑' n, nevanlinnaWeight (p.location n) := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left (presented_weight_sum_le_anchor p)
      (mul_nonneg (sq_nonneg _) (coefficientSquareEnvelope_nonneg v))

def presentedGaussianRaw (parameters : Parameters) (n : I)
    (ω : I → (Fin 4 → ℝ)) : EndpointMatrix :=
  fun i j => (markQuadraticFamily parameters.p n i j ω : ℂ)

def presentedGaussianL2 (parameters : Parameters) (p : ParticlePresentation s I)
    (v : ℂ × Bool) (ω : I → (Fin 4 → ℝ)) : EndpointMatrix :=
  matrixL2Series (iidLaw (markLaw parameters.p) I)
    (fun n i j => markQuadraticLp parameters.p n i j)
    (fun v n => (parameters.scale : ℂ) * particleCoefficient (p.location n) v) v ω

/-- All primitive Wick data are proved for the actual fixed-label Gaussian law. -/
theorem presentedGaussianL2_entryWick (parameters : Parameters) (p : ParticlePresentation s I) :
    EntryWickCovariance (iidLaw (markLaw parameters.p) I)
      (parameters.p : ℂ) (parameters.scale : ℂ) (particleKernel s)
      (presentedGaussianL2 parameters p) := by
  have hh := entryWickCovariance_matrixL2Series (iidLaw (markLaw parameters.p) I)
    (fun n i j => markQuadraticLp parameters.p n i j)
    (fun v n => particleCoefficient (p.location n) v)
    (parameters.p : ℂ) (parameters.scale : ℂ) 2 (by norm_num)
    (fun n i j => markQuadraticLp_norm_sq_le_two _ parameters.abs_p_lt_one n i j)
    (fun i j n m hnm => markQuadraticLp_inner_off _ parameters.abs_p_lt_one hnm i j)
    p.summable_coefficient_sq
    (fun n i j => markQuadraticLp_mean_zero _ parameters.abs_p_lt_one n i j)
    (fun n m hnm i j a b => markQuadraticLp_off_covariance _ parameters.abs_p_lt_one hnm i j a b)
    (fun n i j a b => markQuadraticLp_diagonal_covariance _ parameters.abs_p_lt_one n i j a b)
  have hk : (fun v u => ∑' n : I, particleCoefficient (p.location n) v *
      particleCoefficient (p.location n) u) = particleKernel s := by
    funext v u
    exact (p.hasSum_kernel v u).tsum_eq
  rw [hk] at hh
  exact hh

/-- The raw iid marks satisfy the summability event required by the analytic
version; this is proved from their actual Gaussian second moments. -/
theorem presentedGaussianRaw_weighted_summable (parameters : Parameters)
    (p : ParticlePresentation s I) (i j : Fin 4) :
    ∀ᵐ ω ∂iidLaw (markLaw parameters.p) I,
      Summable (fun n => nevanlinnaWeight (p.location n) * ‖presentedGaussianRaw parameters n ω i j‖) := by
  apply GeneralizedBulk.Analysis.ae_weighted_summable _ _ _ 3
  · intro n
    exact (integrable_markQuadraticFamily_pow parameters.p n i j 1).ofReal.congr
      (Eventually.of_forall (fun ω => by simp [presentedGaussianRaw]))
  · intro n
    exact nevanlinnaWeight_nonneg _
  · exact p.summable_weight
  · intro n
    have heq : (fun ω => ‖presentedGaussianRaw parameters n ω i j‖) =ᵐ[iidLaw (markLaw parameters.p) I]
        (fun ω => ‖markQuadraticLp parameters.p n i j ω‖) :=
      (markQuadraticLp_ae parameters.p n i j).symm.mono (fun ω h => congrArg norm h)
    rw [integral_congr_ae heq]
    exact markQuadraticLp_integral_norm_le_three _ parameters.abs_p_lt_one n i j

/-- Actual conditional second moment, with linear growth in the scalar anchor. -/
theorem presentedGaussianL2_second_moment (parameters : Parameters)
    (p : ParticlePresentation s I) (v : ℂ × Bool) (i j : Fin 4) :
    (∫ ω, ‖presentedGaussianL2 parameters p v ω i j‖ ^ 2 ∂iidLaw (markLaw parameters.p) I) ≤
      (2 * ‖(parameters.scale : ℂ)‖ ^ 2 * coefficientSquareEnvelope v) * ‖s.val.2‖ := by
  have hb := integral_norm_sq_l2Series_le (iidLaw (markLaw parameters.p) I)
    (fun n => markQuadraticLp parameters.p n i j)
    (fun n => (parameters.scale : ℂ) * particleCoefficient (p.location n) v) 2
    (fun n m hnm => markQuadraticLp_inner_off _ parameters.abs_p_lt_one hnm i j)
    (by norm_num) (fun n => markQuadraticLp_norm_sq_le_two _ parameters.abs_p_lt_one n i j)
    (by simpa only [norm_mul, mul_pow] using
      (p.summable_coefficient_sq v).mul_left (‖(parameters.scale : ℂ)‖ ^ 2))
  exact hb.trans ((mul_le_mul_of_nonneg_left (presented_coefficient_square_sum_le p _ v)
    (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring))

/-- A common analytic field uses any actual measurable global anchor whose
conditional value agrees with the constructed L² anchor. -/
def presentedGaussianField (parameters : Parameters) (p : ParticlePresentation s I)
    (anchor : (I → (Fin 4 → ℝ)) → EndpointMatrix) :=
  Presented.matrixField p anchor (parameters.scale : ℂ) (presentedGaussianRaw parameters)

theorem presentedGaussianField_slot_eq_L2_ae (parameters : Parameters)
    (p : ParticlePresentation s I) (anchor : (I → (Fin 4 → ℝ)) → EndpointMatrix)
    (hanchor : ∀ i j, (fun ω => anchor ω i j) =ᵐ[iidLaw (markLaw parameters.p) I]
      (fun ω => presentedGaussianL2 parameters p (Complex.I, false) ω i j))
    (v : ℂ × Bool) (i j : Fin 4) :
    (fun ω => presentedGaussianField parameters p anchor v ω i j) =ᵐ[iidLaw (markLaw parameters.p) I]
      (fun ω => presentedGaussianL2 parameters p v ω i j) := by
  exact Presented.slot_eq_L2_ae _ p (fun ω => anchor ω i j) _
    (fun n ω => presentedGaussianRaw parameters n ω i j)
    (fun n => markQuadraticLp parameters.p n i j) 2
    (fun n => markQuadraticLp_ae parameters.p n i j)
    (fun n m hnm => markQuadraticLp_inner_off _ parameters.abs_p_lt_one hnm i j)
    (by norm_num) (fun n => markQuadraticLp_norm_sq_le_two _ parameters.abs_p_lt_one n i j)
    (presentedGaussianRaw_weighted_summable parameters p i j) (hanchor i j) v

theorem presentedGaussianField_memLp_two (parameters : Parameters)
    (p : ParticlePresentation s I) (anchor : (I → (Fin 4 → ℝ)) → EndpointMatrix)
    (hanchor : ∀ i j, (fun ω => anchor ω i j) =ᵐ[iidLaw (markLaw parameters.p) I]
      (fun ω => presentedGaussianL2 parameters p (Complex.I, false) ω i j))
    (v : ℂ × Bool) (i j : Fin 4) :
    MemLp (fun ω => presentedGaussianField parameters p anchor v ω i j) 2
      (iidLaw (markLaw parameters.p) I) := by
  apply (memLp_congr_ae (presentedGaussianField_slot_eq_L2_ae parameters p anchor hanchor v i j)).2
  exact Lp.memLp _

theorem presentedGaussianField_second_moment (parameters : Parameters)
    (p : ParticlePresentation s I) (anchor : (I → (Fin 4 → ℝ)) → EndpointMatrix)
    (hanchor : ∀ i j, (fun ω => anchor ω i j) =ᵐ[iidLaw (markLaw parameters.p) I]
      (fun ω => presentedGaussianL2 parameters p (Complex.I, false) ω i j))
    (v : ℂ × Bool) (i j : Fin 4) :
    (∫ ω, ‖presentedGaussianField parameters p anchor v ω i j‖ ^ 2 ∂iidLaw (markLaw parameters.p) I) ≤
      (2 * ‖(parameters.scale : ℂ)‖ ^ 2 * coefficientSquareEnvelope v) * ‖s.val.2‖ := by
  rw [integral_congr_ae ((presentedGaussianField_slot_eq_L2_ae parameters p anchor hanchor v i j).mono
    (fun ω h => congrArg (fun z : ℂ => ‖z‖ ^ 2) h))]
  exact presentedGaussianL2_second_moment parameters p v i j

/-- Every centered value/derivative entry has a conditional quadratic bound
with the same scalar-state polynomial. -/
theorem presentedGaussianField_second_moment_quadratic (parameters : Parameters)
    (p : ParticlePresentation s I) (anchor : (I → (Fin 4 → ℝ)) → EndpointMatrix)
    (hanchor : ∀ i j, (fun ω => anchor ω i j) =ᵐ[iidLaw (markLaw parameters.p) I]
      (fun ω => presentedGaussianL2 parameters p (Complex.I, false) ω i j))
    (v : ℂ × Bool) (i j : Fin 4) :
    (∫ ω, ‖presentedGaussianField parameters p anchor v ω i j‖ ^ 2 ∂iidLaw (markLaw parameters.p) I) ≤
      (2 * ‖(parameters.scale : ℂ)‖ ^ 2 * coefficientSquareEnvelope v) * (1 + ‖s.val.2‖ ^ 2) := by
  apply (presentedGaussianField_second_moment parameters p anchor hanchor v i j).trans
  apply mul_le_mul_of_nonneg_left _ (by
    have := coefficientSquareEnvelope_nonneg v
    positivity)
  nlinarith [sq_nonneg (‖s.val.2‖ - 1)]

/-- An elementary entry estimate for the deterministic endpoint mean. -/
theorem norm_meanMatrix_entry_le (g b : ℂ) (i j : Fin 4) :
    ‖GeneralizedSwitching.meanMatrix g b 0 i j‖ ≤ ‖g‖ + ‖b‖ := by
  fin_cases i <;> fin_cases j <;>
    simp [GeneralizedSwitching.meanMatrix] <;> positivity

def scalarValueEnvelope (w : ℂ) : ℝ :=
  1 + ‖w‖ + ‖1 + w ^ 2‖ / |w.im|

theorem scalarValueEnvelope_nonneg (w : ℂ) : 0 ≤ scalarValueEnvelope w := by
  unfold scalarValueEnvelope
  positivity

def meanEntryEnvelope (parameters : Parameters) (w : ℂ) : ℝ :=
  (1 + ‖(parameters.p : ℂ)‖) *
    (‖(parameters.center : ℂ)‖ + ‖(parameters.scale : ℂ)‖ * scalarValueEnvelope w) +
    ‖(parameters.r : ℂ)‖

theorem meanEntryEnvelope_nonneg (parameters : Parameters) (w : ℂ) :
    0 ≤ meanEntryEnvelope parameters w := by
  unfold meanEntryEnvelope
  have := scalarValueEnvelope_nonneg w
  positivity

/-- The full deterministic mean grows at most linearly in the scalar anchor. -/
theorem marked_mean_entry_bound (parameters : Parameters) (s : AnchoredCountingState)
    {w : ℂ} (hw : w.im ≠ 0) (i j : Fin 4) :
    ‖Marked.mean parameters (fun _ : Unit => s) w () i j‖ ≤
      meanEntryEnvelope parameters w * (1 + ‖s.val.2‖) := by
  let g : ℂ := (parameters.center : ℂ) + (parameters.scale : ℂ) * anchoredNevanlinna s w
  let A : ℝ := ‖(parameters.center : ℂ)‖ + ‖(parameters.scale : ℂ)‖ * scalarValueEnvelope w
  have hA : 0 ≤ A := by
    dsimp [A]
    have := scalarValueEnvelope_nonneg w
    positivity
  have hg : ‖g‖ ≤ A * (1 + ‖s.val.2‖) := by
    calc
      _ ≤ ‖(parameters.center : ℂ)‖ + ‖(parameters.scale : ℂ)‖ * ‖anchoredNevanlinna s w‖ := by
        exact (norm_add_le _ _).trans_eq (by rw [norm_mul])
      _ ≤ ‖(parameters.center : ℂ)‖ + ‖(parameters.scale : ℂ)‖ * (scalarValueEnvelope w * ‖s.val.2‖) :=
        add_le_add_left (mul_le_mul_of_nonneg_left (norm_anchoredNevanlinna_le_anchor s hw) (norm_nonneg _)) _
      _ ≤ _ := by
        dsimp [A]
        nlinarith [mul_nonneg (norm_nonneg (parameters.center : ℂ)) (norm_nonneg s.val.2),
          mul_nonneg (norm_nonneg (parameters.scale : ℂ)) (scalarValueEnvelope_nonneg w)]
  have hb : ‖(parameters.p : ℂ) * g + parameters.r‖ ≤
      (‖(parameters.p : ℂ)‖ * A + ‖(parameters.r : ℂ)‖) * (1 + ‖s.val.2‖) := by
    calc
      _ ≤ ‖(parameters.p : ℂ)‖ * ‖g‖ + ‖(parameters.r : ℂ)‖ := by
        exact (norm_add_le _ _).trans_eq (by rw [norm_mul])
      _ ≤ ‖(parameters.p : ℂ)‖ * (A * (1 + ‖s.val.2‖)) + ‖(parameters.r : ℂ)‖ :=
        add_le_add_right (mul_le_mul_of_nonneg_left hg (norm_nonneg _)) _
      _ ≤ _ := by nlinarith [mul_nonneg (norm_nonneg (parameters.r : ℂ)) (norm_nonneg s.val.2)]
  exact (norm_meanMatrix_entry_le g ((parameters.p : ℂ) * g + parameters.r) i j).trans
    ((add_le_add hg hb).trans_eq (by dsimp [meanEntryEnvelope, A]; ring))

/-- Shifting a complex L² random variable preserves L² and has an explicit
second-moment bound. No moments above two are needed here. -/
theorem integral_norm_sq_const_add_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → ℂ)
    (hF : MemLp F 2 μ) (m : ℂ) :
    (∫ ω, ‖m + F ω‖ ^ 2 ∂μ) ≤ 2 * ‖m‖ ^ 2 + 2 * ∫ ω, ‖F ω‖ ^ 2 ∂μ := by
  have hshift : MemLp (fun ω => m + F ω) 2 μ := (memLp_const m).add hF
  have hi := hF.integrable_norm_pow'
  calc
    _ ≤ ∫ ω, 2 * ‖m‖ ^ 2 + 2 * ‖F ω‖ ^ 2 ∂μ := by
      apply integral_mono hshift.integrable_norm_pow' ((integrable_const _).add (hi.const_mul 2))
      intro ω
      change ‖m + F ω‖ ^ 2 ≤ 2 * ‖m‖ ^ 2 + 2 * ‖F ω‖ ^ 2
      have ht := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le m (F ω)) 2
      nlinarith [sq_nonneg (‖m‖ - ‖F ω‖)]
    _ = _ := by
      simp only [integral_add (integrable_const _) (hi.const_mul 2), integral_const_mul]
      simp

/-- Full endpoint resolvent entries have a conditional second moment bounded
by a deterministic constant times the scalar anchor square. -/
theorem presentedGaussianField_full_second_moment (parameters : Parameters)
    (p : ParticlePresentation s I) (anchor : (I → (Fin 4 → ℝ)) → EndpointMatrix)
    (hanchor : ∀ i j, (fun ω => anchor ω i j) =ᵐ[iidLaw (markLaw parameters.p) I]
      (fun ω => presentedGaussianL2 parameters p (Complex.I, false) ω i j))
    {w : ℂ} (hw : w.im ≠ 0) (i j : Fin 4) :
    (∫ ω, ‖Marked.mean parameters (fun _ : Unit => s) w () i j +
      presentedGaussianField parameters p anchor (w, false) ω i j‖ ^ 2 ∂iidLaw (markLaw parameters.p) I) ≤
      (4 * meanEntryEnvelope parameters w ^ 2 +
        4 * ‖(parameters.scale : ℂ)‖ ^ 2 * coefficientSquareEnvelope (w, false)) * (1 + ‖s.val.2‖ ^ 2) := by
  let K : ℝ := 2 * ‖(parameters.scale : ℂ)‖ ^ 2 * coefficientSquareEnvelope (w, false)
  have hK : 0 ≤ K := by
    dsimp [K]
    have := coefficientSquareEnvelope_nonneg (w, false)
    positivity
  have hm := marked_mean_entry_bound parameters s hw i j
  have hm2 := pow_le_pow_left₀ (norm_nonneg _) hm 2
  have hE : 0 ≤ meanEntryEnvelope parameters w := meanEntryEnvelope_nonneg _ _
  have hZ := presentedGaussianField_second_moment_quadratic parameters p anchor hanchor (w, false) i j
  have h := integral_norm_sq_const_add_le (iidLaw (markLaw parameters.p) I)
    (fun ω => presentedGaussianField parameters p anchor (w, false) ω i j)
    (presentedGaussianField_memLp_two parameters p anchor hanchor (w, false) i j)
    (Marked.mean parameters (fun _ : Unit => s) w () i j)
  apply h.trans
  have hm3 : ‖Marked.mean parameters (fun _ : Unit => s) w () i j‖ ^ 2 ≤
      2 * meanEntryEnvelope parameters w ^ 2 * (1 + ‖s.val.2‖ ^ 2) := by
    apply hm2.trans
    rw [mul_pow]
    nlinarith [mul_nonneg (sq_nonneg (meanEntryEnvelope parameters w)) (sq_nonneg (‖s.val.2‖ - 1))]
  nlinarith

/-- The common analytic fixed-label field has the actual infinite-series Wick
covariance; its only supplied data is the already constructed anchor version. -/
theorem presentedGaussianField_entryWick (parameters : Parameters)
    (p : ParticlePresentation s I) (anchor : (I → (Fin 4 → ℝ)) → EndpointMatrix)
    (hanchor : ∀ i j, (fun ω => anchor ω i j) =ᵐ[iidLaw (markLaw parameters.p) I]
      (fun ω => presentedGaussianL2 parameters p (Complex.I, false) ω i j)) :
    EntryWickCovariance (iidLaw (markLaw parameters.p) I)
      (parameters.p : ℂ) (parameters.scale : ℂ) (particleKernel s)
      (presentedGaussianField parameters p anchor) := by
  apply (presentedGaussianL2_entryWick parameters p).congr_ae
  intro v i j
  exact (presentedGaussianField_slot_eq_L2_ae parameters p anchor hanchor v i j).symm

/-- A single full-measure event supports every nonreal derivative of every
entry, with the actual raw mark functions on a fixed iid sample space. -/
theorem presentedGaussianField_hasDerivAt_ae (parameters : Parameters)
    (p : ParticlePresentation s I) (anchor : (I → (Fin 4 → ℝ)) → EndpointMatrix) :
    ∀ᵐ ω ∂iidLaw (markLaw parameters.p) I, ∀ i j : Fin 4, ∀ w : ℂ, w.im ≠ 0 →
      HasDerivAt (fun z => presentedGaussianField parameters p anchor (z, false) ω i j)
        (presentedGaussianField parameters p anchor (w, true) ω i j) w := by
  exact Presented.matrixField_hasDerivAt_ae _ p anchor (parameters.scale : ℂ)
    (presentedGaussianRaw parameters) (presentedGaussianRaw_weighted_summable parameters p)

end GeneralizedBulk.Gaussian
