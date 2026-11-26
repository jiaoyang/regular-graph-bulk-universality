import BourgadeHuang.RationalBulk.EventVanishing

/-! Changing random variables on events of probability tending to zero preserves
weak convergence. This recovers the original pole configurations in Theorem 1.9. -/
noncomputable section
open scoped Topology BoundedContinuousFunction
open MeasureTheory Filter
namespace BourgadeHuang.RationalBulk

/-- Quantitative bounded-test comparison for random variables that agree on a good event. -/
theorem norm_integral_sub_le_exceptional {Ω S : Type*} [MeasurableSpace Ω]
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → S) (hX : Measurable X) (hY : Measurable Y)
    (A : Set Ω) (hagree : ∀ ω ∈ A, X ω = Y ω) (F : S →ᵇ ℝ) :
    ‖(∫ ω,F (X ω) ∂μ)-(∫ ω,F (Y ω) ∂μ)‖ ≤ 2*‖F‖*μ.real Aᶜ := by
  have hi (Z : Ω → S) (hZ : Measurable Z) : Integrable (fun ω => F (Z ω)) μ :=
    (integrable_const ‖F‖).mono' (F.continuous.measurable.comp hZ).aestronglyMeasurable
      (Eventually.of_forall (fun ω => F.norm_coe_le_norm (Z ω)))
  rw [← integral_sub (hi X hX) (hi Y hY),
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s:=Aᶜ) (fun ω hω => by
      have ha : ω ∈ A := by simpa using hω
      rw [hagree ω ha,sub_self])]
  apply norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _)
  intro ω _
  exact (norm_sub_le _ _).trans ((add_le_add (F.norm_coe_le_norm _) (F.norm_coe_le_norm _)).trans_eq (by ring))

/-- A measurable alteration with vanishing exceptional probability does not change any weak limit. -/
theorem weakLawConverges_of_agrees_high_probability {Ω S : Type*} [MeasurableSpace Ω]
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : ℕ → Ω → S) (hX : ∀ N, Measurable (X N)) (hY : ∀ N, Measurable (Y N))
    (A : ℕ → Set Ω) (hagree : ∀ N ω, ω ∈ A N → X N ω = Y N ω)
    (hprob : Tendsto (fun N => μ.real (A N)ᶜ) atTop (𝓝 0))
    (ν : Measure S) (hlim : WeakLawConverges μ Y ν) : WeakLawConverges μ X ν := by
  intro F
  have hd : Tendsto (fun N => (∫ ω,F (X N ω) ∂μ)-(∫ ω,F (Y N ω) ∂μ)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun N => norm_integral_sub_le_exceptional μ
      (X N) (Y N) (hX N) (hY N) (A N) (hagree N) F)
    simpa using hprob.const_mul (2*‖F‖)
  have hh := hd.add (hlim F)
  simpa only [sub_add_cancel,zero_add] using hh

/-- The clipped states have exactly the same weak limits as the original states. -/
theorem EventWeightedHierarchy.weakLawConverges_of_clip
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {β : ℝ} {X : ℕ → Ω → AnchoredCountingState} {A : ℕ → Set Ω}
    (h : EventWeightedHierarchy μ β X A)
    (ν : Measure AnchoredCountingState)
    (hlim : WeakLawConverges μ (fun N => clipState (A N) (X N)) ν) :
    WeakLawConverges μ X ν :=
  weakLawConverges_of_agrees_high_probability μ X _ h.measurable_state
    (fun N => measurable_clipState (h.measurable_event N) (h.measurable_state N)) A
    (fun N ω hω => (clipState_eq_of_mem (A N) (X N) hω).symm)
    h.exceptional_tendsto ν hlim

/-- Theorem 1.9 conclusion transfers directly at the vague counting-measure level. -/
theorem EventWeightedHierarchy.vagueLawConverges_of_clip
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {β : ℝ} {X : ℕ → Ω → AnchoredCountingState} {A : ℕ → Set Ω}
    (h : EventWeightedHierarchy μ β X A)
    (ν : Measure LocalCountingMeasure)
    (hlim : VagueLawConverges μ
      (fun N ω => (clipState (A N) (X N) ω).val.1) ν) :
    VagueLawConverges μ (fun N ω => (X N ω).val.1) ν := by
  exact weakLawConverges_of_agrees_high_probability μ _ _
    (fun N => measurable_fst.comp (measurable_subtype_coe.comp (h.measurable_state N)))
    (fun N => measurable_fst.comp (measurable_subtype_coe.comp
      (measurable_clipState (h.measurable_event N) (h.measurable_state N)))) A
    (fun N ω hω => congrArg (fun s : AnchoredCountingState => s.val.1)
      (clipState_eq_of_mem (A N) (X N) hω).symm)
    h.exceptional_tendsto ν hlim

end BourgadeHuang.RationalBulk
