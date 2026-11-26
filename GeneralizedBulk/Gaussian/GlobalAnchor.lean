import GeneralizedBulk.Gaussian.SeriesActual
import GeneralizedBulk.Gaussian.RandomCoefficients
import GeneralizedBulk.Analysis.ConditionalL2

/-!
# A single jointly measurable Gaussian anchor

The anchor is a genuine Hilbert-space sum on scalar-state × independent-mark
space. A single `Lp` representative is jointly measurable. Its conditional
identification with the statewise series follows from a deterministic
subsequence of conditional mean-square errors.
-/
noncomputable section
open MeasureTheory Filter BourgadeHuang
open scoped Topology BigOperators ComplexConjugate

namespace GeneralizedBulk.Gaussian

theorem finite_sum_Lp_ae {I Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : I → Lp ℂ 2 μ) (raw : I → Ω → ℂ)
    (hf : ∀ n, (f n : Ω → ℂ) =ᵐ[μ] raw n) (s : Finset I) :
    ((∑ n ∈ s, f n : Lp ℂ 2 μ) : Ω → ℂ) =ᵐ[μ] (fun ω => ∑ n ∈ s, raw n ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, Pi.zero_apply] using Lp.coeFn_zero ℂ 2 μ
  | @insert n s hn ih =>
    simp only [Finset.sum_insert hn]
    filter_upwards [Lp.coeFn_add (f n) (∑ k ∈ s, f k), hf n, ih] with ω hadd hn hs
    simpa only [Pi.add_apply, hn, hs] using hadd

theorem integral_sq_error_eq_Lp_norm {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f g : Ω → ℂ) (F G : Lp ℂ 2 μ)
    (hF : (F : Ω → ℂ) =ᵐ[μ] f) (hG : (G : Ω → ℂ) =ᵐ[μ] g) :
    (∫ ω, ‖f ω - g ω‖ ^ 2 ∂μ) = ‖F - G‖ ^ 2 := by
  rw [← integral_norm_sq_L2]
  apply integral_congr_ae
  filter_upwards [hF, hG, Lp.coeFn_sub F G] with ω hf hg hs
  simp only [Pi.sub_apply] at hs
  rw [hs, hf, hg]

section Generic
variable {I S : Type*} [MeasurableSpace S]
variable (P : Measure S) [IsProbabilityMeasure P]
variable (p : ℝ) (hp : |p| < 1)
variable (A : I → S → ℂ) (hA : ∀ n, Measurable (A n))
variable (hA2 : ∀ n, Integrable (fun x => ‖A n x‖ ^ 2) P)

def jointTermFunction (n : I) (i j : Fin 4) (z : S × (I → (Fin 4 → ℝ))) : ℂ :=
  A n z.1 * (markQuadraticFamily p n i j z.2 : ℂ)

include hA in
theorem measurable_jointTermFunction (n : I) (i j : Fin 4) :
    Measurable (jointTermFunction p A n i j) := by
  exact ((hA n).comp measurable_fst).mul
    (Complex.continuous_ofReal.measurable.comp
      ((measurable_markQuadraticFamily p n i j).comp measurable_snd))

include hA hA2 in
theorem jointTermFunction_memLp_two (n : I) (i j : Fin 4) :
    MemLp (jointTermFunction p A n i j) 2 (P.prod (iidLaw (markLaw p) I)) := by
  apply (memLp_two_iff_integrable_sq_norm
    (measurable_jointTermFunction p A hA n i j).aestronglyMeasurable).2
  have hb := ((markQuadraticFamily_memLp_two p n i j).ofReal (K := ℂ)).integrable_norm_pow'
  have hprod := (hA2 n).mul_prod hb
  simpa only [jointTermFunction, norm_mul, mul_pow] using hprod

def jointTerm (n : I) (i j : Fin 4) : Lp ℂ 2 (P.prod (iidLaw (markLaw p) I)) :=
  (jointTermFunction_memLp_two P p A hA hA2 n i j).toLp (jointTermFunction p A n i j)

theorem jointTerm_ae (n : I) (i j : Fin 4) :
    (jointTerm P p A hA hA2 n i j : S × (I → (Fin 4 → ℝ)) → ℂ) =ᵐ[P.prod (iidLaw (markLaw p) I)]
      jointTermFunction p A n i j := MemLp.coeFn_toLp _

include hp in
theorem jointTerm_inner_off {n m : I} (hnm : n ≠ m) (i j : Fin 4) :
    @inner ℂ (Lp ℂ 2 (P.prod (iidLaw (markLaw p) I))) _
      (jointTerm P p A hA hA2 n i j) (jointTerm P p A hA hA2 m i j) = 0 := by
  rw [L2.inner_def]
  have heq : (fun z => @inner ℂ ℂ _ (jointTerm P p A hA hA2 n i j z)
      (jointTerm P p A hA hA2 m i j z)) =ᵐ[P.prod (iidLaw (markLaw p) I)]
      (fun z => (starRingEnd ℂ (A n z.1) * A m z.1) *
        ((markQuadraticFamily p n i j z.2 * markQuadraticFamily p m i j z.2 : ℝ) : ℂ)) := by
    filter_upwards [jointTerm_ae P p A hA hA2 n i j, jointTerm_ae P p A hA hA2 m i j]
      with z hn hm
    simp only [hn, hm, jointTermFunction, RCLike.inner_apply', map_mul,
      Complex.ofReal_mul, Complex.conj_ofReal]
    ring
  rw [integral_congr_ae heq,
    integral_prod_mul (fun x => starRingEnd ℂ (A n x) * A m x)
      (fun γ => ((markQuadraticFamily p n i j γ * markQuadraticFamily p m i j γ : ℝ) : ℂ)),
    integral_complex_ofReal,
    markQuadraticFamily_off_covariance p hp hnm]
  simp

include hp in
theorem jointTerm_norm_sq_le (n : I) (i j : Fin 4) :
    ‖jointTerm P p A hA hA2 n i j‖ ^ 2 ≤ 2 * (∫ x, ‖A n x‖ ^ 2 ∂P) := by
  rw [← integral_norm_sq_L2]
  have heq : (fun z => ‖jointTerm P p A hA hA2 n i j z‖ ^ 2) =ᵐ[P.prod (iidLaw (markLaw p) I)]
      (fun z => ‖A n z.1‖ ^ 2 * markQuadraticFamily p n i j z.2 ^ 2) := by
    filter_upwards [jointTerm_ae P p A hA hA2 n i j] with z hz
    simp only [hz, jointTermFunction, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [integral_congr_ae heq,
    integral_prod_mul (fun x => ‖A n x‖ ^ 2) (fun γ => markQuadraticFamily p n i j γ ^ 2)]
  have hvar : (∫ γ, markQuadraticFamily p n i j γ ^ 2 ∂iidLaw (markLaw p) I) ≤ 2 := by
    simp_rw [pow_two]
    rw [markQuadraticFamily_diagonal_covariance p hp n i j i j]
    exact covariance_entry_variance_le_two p hp i j
  have hnonneg : 0 ≤ ∫ x, ‖A n x‖ ^ 2 ∂P := integral_nonneg (fun x => sq_nonneg _)
  nlinarith

variable (hsq : Summable (fun n => ∫ x, ‖A n x‖ ^ 2 ∂P))

include hp hsq in
theorem summable_jointTerm (i j : Fin 4) :
    Summable (fun n => jointTerm P p A hA hA2 n i j) := by
  apply summable_of_pairwise_inner_zero _ (fun n m hnm => jointTerm_inner_off P p hp A hA hA2 hnm i j)
  apply Summable.of_nonneg_of_le (fun n => sq_nonneg _) _ (hsq.mul_left 2)
  intro n
  exact jointTerm_norm_sq_le P p hp A hA hA2 n i j

def globalAnchorLp (i j : Fin 4) : Lp ℂ 2 (P.prod (iidLaw (markLaw p) I)) :=
  ∑' n, jointTerm P p A hA hA2 n i j

/-- This one representative is measurable jointly in scalar state and marks. -/
theorem measurable_globalAnchor (i j : Fin 4) :
    Measurable (globalAnchorLp P p A hA hA2 i j : S × (I → (Fin 4 → ℝ)) → ℂ) :=
  (Lp.stronglyMeasurable _).measurable

include hp hsq in
theorem hasSum_globalAnchorLp (i j : Fin 4) :
    HasSum (fun n => jointTerm P p A hA hA2 n i j) (globalAnchorLp P p A hA hA2 i j) :=
  (summable_jointTerm P p hp A hA hA2 hsq i j).hasSum

def anchorPartial (u : ℕ → Finset I) (n : ℕ) (i j : Fin 4) (x : S)
    (γ : I → (Fin 4 → ℝ)) : ℂ := ∑ k ∈ u n, jointTermFunction p A k i j (x, γ)

theorem partial_anchor_ae (u : ℕ → Finset I) (n : ℕ) (i j : Fin 4) :
    ((∑ k ∈ u n, jointTerm P p A hA hA2 k i j : Lp ℂ 2 (P.prod (iidLaw (markLaw p) I))) :
      S × (I → (Fin 4 → ℝ)) → ℂ)
      =ᵐ[P.prod (iidLaw (markLaw p) I)]
      (fun z => anchorPartial p A u n i j z.1 z.2) :=
  finite_sum_Lp_ae _ _ _ (fun k => jointTerm_ae P p A hA hA2 k i j) _

include hp hsq in
theorem anchor_partial_joint_error_zero
    (u : ℕ → Finset I) (hu : Tendsto u atTop atTop) (i j : Fin 4) :
    (∀ n, Integrable (fun z : S × (I → (Fin 4 → ℝ)) =>
      ‖anchorPartial p A u n i j z.1 z.2 - globalAnchorLp P p A hA hA2 i j z‖ ^ 2)
      (P.prod (iidLaw (markLaw p) I))) ∧
    Tendsto (fun n => ∫ z : S × (I → (Fin 4 → ℝ)),
      ‖anchorPartial p A u n i j z.1 z.2 - globalAnchorLp P p A hA hA2 i j z‖ ^ 2
        ∂P.prod (iidLaw (markLaw p) I)) atTop (𝓝 0) := by
  let D : ℕ → Lp ℂ 2 (P.prod (iidLaw (markLaw p) I)) :=
    fun n => (∑ k ∈ u n, jointTerm P p A hA hA2 k i j) - globalAnchorLp P p A hA hA2 i j
  have heq (n : ℕ) :
      (fun z => ‖anchorPartial p A u n i j z.1 z.2 -
        globalAnchorLp P p A hA hA2 i j z‖ ^ 2) =ᵐ[P.prod (iidLaw (markLaw p) I)]
        (fun z => ‖D n z‖ ^ 2) := by
    filter_upwards [partial_anchor_ae P p A hA hA2 u n i j,
      Lp.coeFn_sub (∑ k ∈ u n, jointTerm P p A hA hA2 k i j)
        (globalAnchorLp P p A hA hA2 i j)] with z hp hs
    simp only [D, Pi.sub_apply] at hs ⊢
    rw [hs, hp]
  constructor
  · intro n
    exact ((Lp.memLp (D n)).integrable_norm_pow').congr (heq n).symm
  · have hD : Tendsto D atTop (𝓝 0) := by
      have hh := (hasSum_globalAnchorLp P p hp A hA hA2 hsq i j).comp hu
      simpa only [D, sub_self] using hh.sub_const (globalAnchorLp P p A hA hA2 i j)
    have hlim := hD.norm.pow 2
    simpa only [integral_congr_ae (heq _), integral_norm_sq_L2, norm_zero, zero_pow (by decide : 2 ≠ 0)] using hlim

include hp hsq in
theorem anchor_conditional_error_subsequence
    (u : ℕ → Finset I) (hu : Tendsto u atTop atTop) (i j : Fin 4) :
    ∃ r : ℕ → ℕ, StrictMono r ∧ ∀ᵐ x ∂P,
      Tendsto (fun n => ∫ γ,
        ‖anchorPartial p A u (r n) i j x γ - globalAnchorLp P p A hA hA2 i j (x, γ)‖ ^ 2
          ∂iidLaw (markLaw p) I) atTop (𝓝 0) := by
  obtain ⟨hi, hz⟩ := anchor_partial_joint_error_zero P p hp A hA hA2 hsq u hu i j
  exact GeneralizedBulk.Analysis.exists_subsequence_conditional_error_zero P (iidLaw (markLaw p) I)
    (fun n x γ => anchorPartial p A u n i j x γ)
    (fun x γ => globalAnchorLp P p A hA hA2 i j (x, γ)) hi hz

theorem globalAnchor_section_memLp_ae (i j : Fin 4) :
    ∀ᵐ x ∂P, MemLp (fun γ => globalAnchorLp P p A hA hA2 i j (x, γ)) 2
      (iidLaw (markLaw p) I) := by
  have hi := ((Lp.memLp (globalAnchorLp P p A hA hA2 i j)).integrable_norm_pow').prod_right_ae
  filter_upwards [hi] with x hx
  apply (memLp_two_iff_integrable_sq_norm _).2 hx
  exact ((measurable_globalAnchor P p A hA hA2 i j).comp
    (measurable_const.prodMk measurable_id)).aestronglyMeasurable

theorem local_partial_anchor_ae (x : S) (s : Finset I) (i j : Fin 4) :
    ((∑ k ∈ s, A k x • markQuadraticLp p k i j : Lp ℂ 2 (iidLaw (markLaw p) I)) :
      (I → (Fin 4 → ℝ)) → ℂ) =ᵐ[iidLaw (markLaw p) I]
      (fun γ => ∑ k ∈ s, jointTermFunction p A k i j (x, γ)) := by
  apply finite_sum_Lp_ae
  intro k
  filter_upwards [Lp.coeFn_smul (A k x) (markQuadraticLp p k i j), markQuadraticLp_ae p k i j]
    with γ hsm hr
  simp only [Pi.smul_apply, smul_eq_mul, hr] at hsm
  exact hsm

include hp hsq in
/-- The single joint representative agrees on almost every scalar fiber with
the independently constructed conditional L² series. This is proved from joint
and conditional mean-square limits, not assumed as a measurable-selection fact. -/
theorem globalAnchor_conditional_agreement [Countable I]
    (hpoint : ∀ x, Summable (fun n => ‖A n x‖ ^ 2)) (i j : Fin 4) :
    ∀ᵐ x ∂P, (fun γ => globalAnchorLp P p A hA hA2 i j (x, γ)) =ᵐ[iidLaw (markLaw p) I]
      (fun γ => l2Series (iidLaw (markLaw p) I) (fun n => markQuadraticLp p n i j)
        (fun n => A n x) γ) := by
  classical
  obtain ⟨u, hu⟩ := exists_seq_tendsto (atTop : Filter (Finset I))
  obtain ⟨r, hr, herr⟩ := anchor_conditional_error_subsequence P p hp A hA hA2 hsq u hu i j
  filter_upwards [herr, globalAnchor_section_memLp_ae P p A hA hA2 i j] with x hzero hsection
  let Q := iidLaw (markLaw p) I
  let G : Lp ℂ 2 Q := hsection.toLp (fun γ => globalAnchorLp P p A hA hA2 i j (x, γ))
  let F : ℕ → Lp ℂ 2 Q := fun n => ∑ k ∈ u (r n), A k x • markQuadraticLp p k i j
  have hG : (G : (I → (Fin 4 → ℝ)) → ℂ) =ᵐ[Q]
      (fun γ => globalAnchorLp P p A hA hA2 i j (x, γ)) := MemLp.coeFn_toLp _
  have herror (n : ℕ) :
      (∫ γ, ‖anchorPartial p A u (r n) i j x γ -
        globalAnchorLp P p A hA hA2 i j (x, γ)‖ ^ 2 ∂Q) = ‖F n - G‖ ^ 2 :=
    integral_sq_error_eq_Lp_norm Q _ _ (F n) G
      (local_partial_anchor_ae p A x (u (r n)) i j) hG
  have hnormsq : Tendsto (fun n => ‖F n - G‖ ^ 2) atTop (𝓝 0) := by
    convert hzero using 1
    funext n
    exact (herror n).symm
  have hGlim : Tendsto F atTop (𝓝 G) := by
    rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_norm_tendsto_zero]
    have hh := hnormsq.sqrt
    simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hh
  have hsum := summable_weighted_orthogonal (fun n => markQuadraticLp p n i j)
    (fun n => A n x) 2 (fun n m hnm => markQuadraticLp_inner_off p hp hnm i j)
    (by norm_num) (fun n => markQuadraticLp_norm_sq_le_two p hp n i j) (hpoint x)
  have hLlim : Tendsto F atTop (𝓝 (l2Series Q (fun n => markQuadraticLp p n i j)
      (fun n => A n x))) := hsum.hasSum.comp (hu.comp hr.tendsto_atTop)
  have hEq : G = l2Series Q (fun n => markQuadraticLp p n i j) (fun n => A n x) :=
    tendsto_nhds_unique hGlim hLlim
  rw [← hEq]
  exact hG.symm

end Generic

section Presented
variable {I S : Type*} [Countable I] [MeasurableSpace S]
variable (P : Measure S) [IsProbabilityMeasure P]
variable (X : S → PresentedState I) (hX : Measurable X)
variable (hm : Integrable (fun x => ‖(X x).scalar.val.2‖) P)

def presentedAnchorCoefficient (sigma : ℂ) (n : I) (x : S) : ℂ :=
  sigma * particleCoefficient ((X x).location n) (Complex.I, false)

include hX in
theorem measurable_presentedAnchorCoefficient (sigma : ℂ) (n : I) :
    Measurable (presentedAnchorCoefficient X sigma n) :=
  ((measurable_particleCoefficient (Complex.I, false)).comp
    ((PresentedState.measurable_location n).comp hX)).const_mul sigma

theorem presented_weight_le_anchor (x : S) (n : I) :
    nevanlinnaWeight ((X x).location n) ≤ ‖(X x).scalar.val.2‖ := by
  have hw := (X x).presentation.summable_weight.le_tsum n
    (fun m hm => nevanlinnaWeight_nonneg ((X x).location m))
  have heq := ((X x).presentation.hasSum_observable (X x).scalar.integrable_weight).tsum_eq
  rw [heq] at hw
  exact hw.trans ((X x).scalar.integral_weight_le_im.trans (Complex.im_le_norm _))

include hX hm in
theorem integrable_presentedAnchorCoefficient_sq (sigma : ℂ) (n : I) :
    Integrable (fun x => ‖presentedAnchorCoefficient X sigma n x‖ ^ 2) P := by
  apply (hm.const_mul (5 * ‖sigma‖ ^ 2)).mono'
    ((measurable_presentedAnchorCoefficient X hX sigma n).norm.pow_const 2).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  dsimp [presentedAnchorCoefficient]
  rw [norm_mul, mul_pow]
  calc
    _ ≤ ‖sigma‖ ^ 2 * (5 * nevanlinnaWeight ((X x).location n)) :=
      mul_le_mul_of_nonneg_left (particleCoefficient_anchor_sq_bound _) (sq_nonneg _)
    _ ≤ (5 * ‖sigma‖ ^ 2) * ‖(X x).scalar.val.2‖ := by
      have hh := mul_le_mul_of_nonneg_left (presented_weight_le_anchor X x n)
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5) (sq_nonneg ‖sigma‖))
      nlinarith only [hh]

include hX hm in
theorem summable_presentedAnchorCoefficient_integrals (sigma : ℂ) :
    Summable (fun n => ∫ x, ‖presentedAnchorCoefficient X sigma n x‖ ^ 2 ∂P) :=
  summable_anchor_coefficient_integrals P X hX hm sigma

/-- The actual random-scalar-state anchor, with all coefficient conditions
proved from measurability and the first anchor moment. -/
def presentedGlobalAnchor (parameters : Parameters) (i j : Fin 4) :
    Lp ℂ 2 (P.prod (iidLaw (markLaw parameters.p) I)) :=
  globalAnchorLp P parameters.p (presentedAnchorCoefficient X parameters.scale)
    (measurable_presentedAnchorCoefficient X hX parameters.scale)
    (integrable_presentedAnchorCoefficient_sq P X hX hm parameters.scale) i j

theorem presentedGlobalAnchor_measurable (parameters : Parameters) (i j : Fin 4) :
    Measurable (presentedGlobalAnchor P X hX hm parameters i j : S × (I → (Fin 4 → ℝ)) → ℂ) :=
  (Lp.stronglyMeasurable _).measurable

theorem presentedAnchorCoefficient_summable_pointwise (sigma : ℂ) (x : S) :
    Summable (fun n => ‖presentedAnchorCoefficient X sigma n x‖ ^ 2) := by
  have hh := (X x).presentation.summable_coefficient_sq (Complex.I, false)
  simpa only [presentedAnchorCoefficient, norm_mul, mul_pow] using hh.mul_left (‖sigma‖ ^ 2)

/-- The globally measurable anchor has the correct conditional marked-series
law, with the same fixed particle labels and all multiplicities preserved. -/
theorem presentedGlobalAnchor_conditional_agreement (parameters : Parameters) (i j : Fin 4) :
    ∀ᵐ x ∂P,
      (fun γ => presentedGlobalAnchor P X hX hm parameters i j (x, γ)) =ᵐ[iidLaw (markLaw parameters.p) I]
        (fun γ => l2Series (iidLaw (markLaw parameters.p) I)
          (fun n => markQuadraticLp parameters.p n i j)
          (fun n => presentedAnchorCoefficient X parameters.scale n x) γ) := by
  exact globalAnchor_conditional_agreement P parameters.p parameters.abs_p_lt_one
    (presentedAnchorCoefficient X parameters.scale)
    (measurable_presentedAnchorCoefficient X hX parameters.scale)
    (integrable_presentedAnchorCoefficient_sq P X hX hm parameters.scale)
    (summable_presentedAnchorCoefficient_integrals P X hX hm parameters.scale)
    (presentedAnchorCoefficient_summable_pointwise X parameters.scale) i j

end Presented

end GeneralizedBulk.Gaussian
