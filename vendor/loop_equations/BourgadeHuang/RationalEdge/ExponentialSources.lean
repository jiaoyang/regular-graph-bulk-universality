import BourgadeHuang.RationalEdge.ExponentialLoop
import BourgadeHuang.CompactExponentialSources

noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalEdge

/-- The finite-source exponential equation is independent of the chosen finite index type. -/
theorem multivariate_exponential_tilted_loop_identity_fintype
    {ι : Type*} [Fintype ι]
    (ν : Measure AnchoredCountingState) (β : ℝ) (hh : ExactHierarchy ν β)
    {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a * ‖s.val.2‖ ^ 2)) ν)
    {w : ℂ} {v : ι → ℂ} (hw : w.im ≠ 0) (hv : ∀ i, (v i).im ≠ 0) (c : ι → ℂ) :
    Integrable (fun s => (loopHead β s w +
      ∑ i, c i * ((2 / (β : ℂ)) * anchoredInteraction s w (v i))) *
        Complex.exp (∑ i, c i * anchoredNevanlinna s (v i))) ν ∧
    (∫ s, (loopHead β s w + ∑ i, c i * ((2 / (β : ℂ)) * anchoredInteraction s w (v i))) *
      Complex.exp (∑ i, c i * anchoredNevanlinna s (v i)) ∂ν) = 0 := by
  let e := (Fintype.equivFin ι).symm
  have h := multivariate_exponential_tilted_loop_identity ν β hh ha he hw
    (fun i => hv (e i)) (fun i => c (e i))
  have hX (s : AnchoredCountingState) : (∑ i, c (e i) * anchoredNevanlinna s (v (e i))) =
      ∑ i, c i * anchoredNevanlinna s (v i) := e.sum_comp (fun i => c i * anchoredNevanlinna s (v i))
  have hJ (s : AnchoredCountingState) : (∑ i, c (e i) * ((2 / (β : ℂ)) * anchoredInteraction s w (v (e i)))) =
      ∑ i, c i * ((2 / (β : ℂ)) * anchoredInteraction s w (v i)) :=
    e.sum_comp (fun i => c i * ((2 / (β : ℂ)) * anchoredInteraction s w (v i)))
  simpa only [hX, hJ] using h


/-- The exponential loop identity for finite-valued parameter sources. -/
theorem exponential_loop_identity_simple_source
    {T : Type*} [MeasurableSpace T] (κ : Measure T) [IsFiniteMeasure κ]
    (ν : Measure AnchoredCountingState) (β : ℝ) (hh : ExactHierarchy ν β)
    {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a * ‖s.val.2‖ ^ 2)) ν)
    {w : ℂ} (hw : w.im ≠ 0) (f : SimpleFunc T (ℂ × ℂ))
    (hf : ∀ p ∈ f.range, p.1.im ≠ 0) :
    Integrable (fun s => (loopHead β s w +
      ∫ t, (f t).2 * ((2 / (β : ℂ)) * anchoredInteraction s w (f t).1) ∂κ) *
      Complex.exp (∫ t, (f t).2 * anchoredNevanlinna s (f t).1 ∂κ)) ν ∧
    (∫ s, (loopHead β s w +
      ∫ t, (f t).2 * ((2 / (β : ℂ)) * anchoredInteraction s w (f t).1) ∂κ) *
      Complex.exp (∫ t, (f t).2 * anchoredNevanlinna s (f t).1 ∂κ) ∂ν) = 0 := by
  have h := multivariate_exponential_tilted_loop_identity_fintype (ι := f.range) ν β hh ha he hw
    (fun p => hf p.val p.property)
    (fun p => ((κ.real (f ⁻¹' {p.val}) : ℝ) : ℂ) * p.val.2)
  have hJ (s : AnchoredCountingState) := integral_simple_weighted_source κ f
    (fun z => (2 / (β : ℂ)) * anchoredInteraction s w z)
  have hX (s : AnchoredCountingState) := integral_simple_weighted_source κ f (anchoredNevanlinna s)
  simpa only [hJ, hX] using h

/-- The exact exponential loop equation remains valid for genuinely integrated
compact sources. Finite-valued approximation is constructed inside the proof. -/
theorem exponential_loop_identity_compact_source_and_integrable
    {T : Type*} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T] [BorelSpace T] [Nonempty T]
    (κ : Measure T) [IsFiniteMeasure κ]
    (γ ρ : T → ℂ) (hγ : Continuous γ) (hρ : Continuous ρ) (hoff : ∀ t, (γ t).im ≠ 0)
    (ν : Measure AnchoredCountingState) (β : ℝ) (hh : ExactHierarchy ν β)
    {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a * ‖s.val.2‖ ^ 2)) ν)
    {w : ℂ} (hw : w.im ≠ 0) :
    Integrable (fun s => Complex.exp (∫ t, ρ t * anchoredNevanlinna s (γ t) ∂κ)) ν ∧
    Integrable (fun s => (loopHead β s w +
      ∫ t, ρ t * ((2 / (β : ℂ)) * anchoredInteraction s w (γ t)) ∂κ) *
      Complex.exp (∫ t, ρ t * anchoredNevanlinna s (γ t) ∂κ)) ν ∧
    (∫ s, (loopHead β s w +
      ∫ t, ρ t * ((2 / (β : ℂ)) * anchoredInteraction s w (γ t)) ∂κ) *
      Complex.exp (∫ t, ρ t * anchoredNevanlinna s (γ t) ∂κ) ∂ν) = 0 := by
  classical
  let P := fun t => (γ t, ρ t)
  have hP : Measurable P := (hγ.prodMk hρ).measurable
  let t₀ : T := Classical.choice inferInstance
  let f := fun n => SimpleFunc.approxOn P hP (Set.range P) (P t₀) (Set.mem_range_self t₀) n
  have hmem (n : ℕ) (t : T) : f n t ∈ Set.range P := SimpleFunc.approxOn_mem hP _ n t
  have hlim (t : T) : Tendsto (fun n => f n t) atTop (𝓝 (P t)) :=
    SimpleFunc.tendsto_approxOn hP _ (subset_closure (Set.mem_range_self t))
  have hKr : IsCompact (Set.range γ) := isCompact_range hγ
  have hKoff : ∀ z ∈ Set.range γ, z.im ≠ 0 := by rintro z ⟨t, rfl⟩; exact hoff t
  obtain ⟨CS, hCS, hSb⟩ := exists_compact_resolvent_anchor_bound hKr hKoff
  obtain ⟨CI, hCI, hIb⟩ := exists_compact_interaction_anchor_bound hKr hKoff hw
  obtain ⟨R₀, hR₀⟩ := isCompact_univ.bddAbove_image hρ.norm.continuousOn
  let R := max R₀ 0
  have hR : 0 ≤ R := le_max_right _ _
  have hρb (t : T) : ‖ρ t‖ ≤ R := (hR₀ ⟨t, Set.mem_univ t, rfl⟩).trans (le_max_left _ _)
  let F := fun (s : AnchoredCountingState) (p : ℂ × ℂ) => p.2 * anchoredNevanlinna s p.1
  let G := fun (s : AnchoredCountingState) (p : ℂ × ℂ) => p.2 * ((2 / (β : ℂ)) * anchoredInteraction s w p.1)
  let U := R * CS
  let V := R * ‖2 / (β : ℂ)‖ * CI
  have hU : 0 ≤ U := mul_nonneg hR hCS
  have hV : 0 ≤ V := mul_nonneg (mul_nonneg hR (norm_nonneg _)) hCI
  have hFb (s : AnchoredCountingState) (p : ℂ × ℂ) (hp : p ∈ Set.range P) :
      ‖F s p‖ ≤ U * ‖s.val.2‖ := by
    rcases hp with ⟨t, rfl⟩
    dsimp [F, P]
    rw [norm_mul]
    exact (mul_le_mul (hρb t) (hSb s (γ t) (Set.mem_range_self t)) (norm_nonneg _) hR).trans_eq (by ring)
  have hGb (s : AnchoredCountingState) (p : ℂ × ℂ) (hp : p ∈ Set.range P) :
      ‖G s p‖ ≤ V * ‖s.val.2‖ := by
    rcases hp with ⟨t, rfl⟩
    dsimp [G, P]
    simp only [norm_mul]
    exact (mul_le_mul (hρb t) (mul_le_mul_of_nonneg_left (hIb s (γ t) (Set.mem_range_self t))
      (norm_nonneg _)) (by positivity) hR).trans_eq (by ring)
  have hFc (s : AnchoredCountingState) (t : T) : ContinuousAt (F s) (P t) := by
    have hS : ContinuousAt (anchoredNevanlinna s) (P t).1 :=
      (differentiableAt_anchoredNevanlinna s (hoff t)).continuousAt
    exact continuous_snd.continuousAt.mul (hS.comp continuous_fst.continuousAt)
  have hGc (s : AnchoredCountingState) (t : T) : ContinuousAt (G s) (P t) := by
    have hI : ContinuousAt (anchoredInteraction s w) (P t).1 :=
      continuousAt_anchoredInteraction_right s hw (hoff t)
    exact continuous_snd.continuousAt.mul (continuousAt_const.mul
      (hI.comp continuous_fst.continuousAt))
  have hgen (A : AnchoredCountingState → ℂ × ℂ → ℂ) (C : ℝ) (hC : 0 ≤ C)
      (hAb : ∀ s p, p ∈ Set.range P → ‖A s p‖ ≤ C * ‖s.val.2‖)
      (hAc : ∀ s t, ContinuousAt (A s) (P t)) :
      (∀ s, Tendsto (fun n => ∫ t, A s (f n t) ∂κ) atTop (𝓝 (∫ t, A s (P t) ∂κ))) ∧
      (∀ n s, ‖∫ t, A s (f n t) ∂κ‖ ≤ (κ.real Set.univ * C) * (1 + ‖s.val.2‖)) := by
    have hAi (n : ℕ) (s : AnchoredCountingState) : Integrable (fun t => A s (f n t)) κ :=
      ((f n).map (A s)).integrable_of_isFiniteMeasure
    constructor
    · intro s
      exact tendsto_integral_of_dominated_convergence (fun _ : T => C * ‖s.val.2‖)
        (fun n => (hAi n s).aestronglyMeasurable) (integrable_const _)
        (fun n => Filter.Eventually.of_forall (fun t => hAb s (f n t) (hmem n t)))
        (Filter.Eventually.of_forall (fun t => (hAc s t).tendsto.comp (hlim t)))
    · intro n s
      calc
        _ ≤ ∫ t, ‖A s (f n t)‖ ∂κ := norm_integral_le_integral_norm _
        _ ≤ ∫ _ : T, C * ‖s.val.2‖ ∂κ :=
          integral_mono (hAi n s).norm (integrable_const _) (fun t => hAb s (f n t) (hmem n t))
        _ = (κ.real Set.univ * C) * ‖s.val.2‖ := by simp only [integral_const, smul_eq_mul]; ring
        _ ≤ (κ.real Set.univ * C) * (1 + ‖s.val.2‖) :=
          mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (measureReal_nonneg) hC)
  obtain ⟨hFlim, hFn⟩ := hgen F U hU hFb hFc
  obtain ⟨hGlim, hGn⟩ := hgen G V hV hGb hGc
  have hFm (n : ℕ) : Continuous (fun s => ∫ t, F s (f n t) ∂κ) := by
    change Continuous (fun s => ∫ t, (f n t).2 * anchoredNevanlinna s (f n t).1 ∂κ)
    simp_rw [integral_simple_weighted_source κ (f n)]
    apply continuous_finset_sum
    intro p _
    apply continuous_const.mul
    apply continuous_anchoredNevanlinna
    obtain ⟨t, ht⟩ := SimpleFunc.mem_range.mp p.property
    obtain ⟨u, hu⟩ := hmem n t
    have hp : P u = p.val := hu.trans ht
    rw [← hp]
    exact hoff u
  have hFmeas : AEStronglyMeasurable (fun s => ∫ t, F s (P t) ∂κ) ν :=
    aestronglyMeasurable_of_tendsto_ae atTop
    (fun n => (hFm n).aestronglyMeasurable) (Filter.Eventually.of_forall hFlim)
  have hsourceb (s : AnchoredCountingState) : ‖∫ t, F s (P t) ∂κ‖ ≤
      (κ.real Set.univ * U) * (1 + ‖s.val.2‖) :=
    le_of_tendsto (hFlim s).norm (Filter.Eventually.of_forall (fun n => hFn n s))
  have hanchorMeas : AEStronglyMeasurable (fun s : AnchoredCountingState => ‖s.val.2‖) ν :=
    (continuous_snd.comp continuous_subtype_val).norm.aestronglyMeasurable
  have hei := integrable_exp_mul_abs_of_exp_sq hanchorMeas ha he (κ.real Set.univ * U)
  simp only [abs_norm] at hei
  have hsourceExp : Integrable (fun s => Complex.exp (∫ t, F s (P t) ∂κ)) ν := by
    apply (hei.const_mul (Real.exp (κ.real Set.univ * U))).mono'
      (Complex.continuous_exp.comp_aestronglyMeasurable hFmeas)
    apply Filter.Eventually.of_forall
    intro s
    calc
      _ ≤ Real.exp ‖∫ t, F s (P t) ∂κ‖ := Complex.norm_exp_le_exp_norm _
      _ ≤ Real.exp ((κ.real Set.univ * U) * (1 + ‖s.val.2‖)) := Real.exp_le_exp.mpr (hsourceb s)
      _ = _ := by rw [mul_add, mul_one, Real.exp_add]
  refine ⟨hsourceExp, ?_⟩
  apply exponential_loop_identity_of_source_limits ν ha he (fun s => loopHead β s w)
    (anchoredGrowth_loopHead β hw) (fun n s => ∫ t, F s (f n t) ∂κ)
    (fun n s => ∫ t, G s (f n t) ∂κ) (fun s => ∫ t, F s (P t) ∂κ)
    (fun s => ∫ t, G s (P t) ∂κ) (κ.real Set.univ * U) (κ.real Set.univ * V)
    (mul_nonneg measureReal_nonneg hU) (mul_nonneg measureReal_nonneg hV)
    hFn hGn hFlim hGlim
  intro n
  exact exponential_loop_identity_simple_source κ ν β hh ha he hw (f n) (by
    intro p hp
    obtain ⟨t, rfl⟩ := SimpleFunc.mem_range.mp hp
    obtain ⟨u, hu⟩ := hmem n t
    rw [← hu]
    exact hoff u)


/-- The integrated-source loop identity, without the auxiliary standalone
integrability conclusion. -/
theorem exponential_loop_identity_compact_source
    {T : Type*} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T] [BorelSpace T] [Nonempty T]
    (κ : Measure T) [IsFiniteMeasure κ]
    (γ ρ : T → ℂ) (hγ : Continuous γ) (hρ : Continuous ρ) (hoff : ∀ t, (γ t).im ≠ 0)
    (ν : Measure AnchoredCountingState) (β : ℝ) (hh : ExactHierarchy ν β)
    {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a * ‖s.val.2‖ ^ 2)) ν)
    {w : ℂ} (hw : w.im ≠ 0) :
    Integrable (fun s => (loopHead β s w +
      ∫ t, ρ t * ((2 / (β : ℂ)) * anchoredInteraction s w (γ t)) ∂κ) *
      Complex.exp (∫ t, ρ t * anchoredNevanlinna s (γ t) ∂κ)) ν ∧
    (∫ s, (loopHead β s w +
      ∫ t, ρ t * ((2 / (β : ℂ)) * anchoredInteraction s w (γ t)) ∂κ) *
      Complex.exp (∫ t, ρ t * anchoredNevanlinna s (γ t) ∂κ) ∂ν) = 0 :=
  (exponential_loop_identity_compact_source_and_integrable κ γ ρ hγ hρ hoff ν β hh ha he hw).2


end BourgadeHuang.RationalEdge
