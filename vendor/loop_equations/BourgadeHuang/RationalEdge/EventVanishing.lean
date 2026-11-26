import BourgadeHuang.RationalEdge.EventMoments

/-! Removal of the relative moment weight and replacement on exceptional events. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalEdge

@[simp] theorem emptyState_nevanlinna (z : ℂ) : anchoredNevanlinna emptyState z = 0 := by
  simp [anchoredNevanlinna, emptyState]

@[simp] theorem coordinateMaximum_empty {n : ℕ} (w : ℂ) (aux : Fin n → ℂ) :
    coordinateMaximum emptyState w aux = 0 := by
  simp [coordinateMaximum]

theorem continuous_coordinateMaximum {n : ℕ} {w : ℂ} {aux : Fin n → ℂ}
    (hw : w.im ≠ 0) (haux : ∀ j, (aux j).im ≠ 0) :
    Continuous (fun s => coordinateMaximum s w aux) := by
  apply Continuous.finset_sup'_apply
  intro j _
  apply Continuous.norm
  apply continuous_anchoredNevanlinna
  exact Fin.cases hw haux j

theorem coordinateMaximum_le_anchor {n : ℕ} {w : ℂ} {aux : Fin n → ℂ}
    (hw : w.im ≠ 0) (haux : ∀ j, (aux j).im ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, coordinateMaximum s w aux ≤ C * ‖s.val.2‖ := by
  let z : Fin (n+1) → ℂ := Fin.cons (α := fun _ => ℂ) w aux
  let c : Fin (n+1) → ℝ := fun j => 1+‖z j‖+‖1+(z j)^2‖/|(z j).im|
  have hc (j) : 0 ≤ c j := by dsimp [c]; positivity
  refine ⟨∑ j,c j, Finset.sum_nonneg (fun j _ => hc j), fun s => ?_⟩
  apply Finset.sup'_le
  intro j _
  have hz : (z j).im ≠ 0 := Fin.cases hw haux j
  apply (norm_anchoredNevanlinna_le_anchor s hz).trans
  exact mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun j _ => hc j) (Finset.mem_univ j)) (norm_nonneg _)

theorem integrable_coordinateMaximum_power {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → AnchoredCountingState) (hX : Measurable X)
    (hm : ∀ q : ℕ, Integrable (fun ω => ‖(X ω).val.2‖^q) μ)
    {n : ℕ} {w : ℂ} {aux : Fin n → ℂ} (hw : w.im ≠ 0)
    (haux : ∀ j, (aux j).im ≠ 0) (q : ℕ) :
    Integrable (fun ω => coordinateMaximum (X ω) w aux ^ q) μ := by
  obtain ⟨C,hC,hbound⟩ := coordinateMaximum_le_anchor hw haux
  apply ((hm q).const_mul (C^q)).mono'
    (((continuous_coordinateMaximum hw haux).pow q).measurable.comp hX).aestronglyMeasurable
  exact Eventually.of_forall fun ω => by
    simp only [Function.comp_apply]
    rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (coordinateMaximum_nonneg _ _ _) _)]
    simpa only [mul_pow] using pow_le_pow_left₀ (coordinateMaximum_nonneg _ _ _) (hbound (X ω)) q

theorem coordinateMaximum_clip_power {Ω : Type*} (A : Set Ω)
    (X : Ω → AnchoredCountingState) {n : ℕ} (w : ℂ) (aux : Fin n → ℂ)
    {q : ℕ} (hq : q ≠ 0) :
    (fun ω => coordinateMaximum (clipState A X ω) w aux ^ q) =
      A.indicator (fun ω => coordinateMaximum (X ω) w aux ^ q) := by
  classical
  funext ω
  by_cases ha : ω ∈ A <;> simp [clipState,ha,hq]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {β : ℝ} {X : ℕ → Ω → AnchoredCountingState} {A : ℕ → Set Ω}

theorem EventWeightedHierarchy.uniform_maximum_moments
    (h : EventWeightedHierarchy μ β X A)
    {n : ℕ} {w : ℂ} {aux : Fin n → ℂ} (hw : w.im ≠ 0)
    (haux : ∀ j, (aux j).im ≠ 0) {q : ℕ} (hq : q ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N,
      (∫ ω, coordinateMaximum (X N ω) w aux ^ q ∂(μ.restrict (A N))) ≤ C := by
  obtain ⟨D,hD,hbound⟩ := coordinateMaximum_le_anchor hw haux
  obtain ⟨B,hB⟩ := h.uniform_clip_moments q
  have hB0 : 0 ≤ B := (integral_nonneg (fun ω => pow_nonneg (norm_nonneg _) q)).trans (hB 0)
  refine ⟨D^q*B,mul_nonneg (pow_nonneg hD q) hB0,fun N => ?_⟩
  let Y := clipState (A N) (X N)
  have hYm : Measurable Y := measurable_clipState (h.measurable_event N) (h.measurable_state N)
  have hm (q : ℕ) : Integrable (fun ω => ‖(Y ω).val.2‖^q) μ :=
    integrable_clipState_moments μ (h.measurable_event N) (X N) (h.moments N) q
  rw [← integral_indicator (h.measurable_event N), ← coordinateMaximum_clip_power _ _ _ _ hq]
  calc
    _ ≤ ∫ ω,D^q*‖(Y ω).val.2‖^q ∂μ := integral_mono
      (integrable_coordinateMaximum_power μ Y hYm hm hw haux q) ((hm q).const_mul _)
      (fun ω => by simpa only [mul_pow] using
        pow_le_pow_left₀ (coordinateMaximum_nonneg _ _ _) (hbound (Y ω)) q)
    _ = D^q*(∫ ω,‖(Y ω).val.2‖^q ∂μ) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (hB N) (pow_nonneg hD q)

/-- After absorption, each event-restricted expectation tends to zero absolutely. -/
theorem EventWeightedHierarchy.restricted_loop_tendsto
    (h : EventWeightedHierarchy μ β X A)
    {n : ℕ} {w : ℂ} {aux : Fin n → ℂ} (hw : w.im ≠ 0)
    (haux : ∀ j, (aux j).im ≠ 0) :
    Tendsto (fun N => ∫ ω, loopIntegrand β (X N ω) w aux ∂(μ.restrict (A N)))
      atTop (𝓝 0) := by
  let K : Set ℂ := {w} ∪ Set.range aux
  have hK : IsCompact K := isCompact_singleton.union (Set.finite_range aux).isCompact
  have hoff : ∀ z ∈ K,z.im ≠ 0 := by
    intro z hz
    rcases hz with hz | ⟨j,rfl⟩
    · simpa only [Set.mem_singleton_iff.mp hz] using hw
    · exact haux j
  obtain ⟨ε,hε,hε0,herr⟩ := h.error n K hK hoff
  obtain ⟨C,hC,hbound⟩ := h.uniform_maximum_moments hw haux (q:=n+2) (by omega)
  apply squeeze_zero_norm (fun N => (herr N w (Set.mem_union_left _ rfl) aux
    (fun j => Set.mem_union_right _ (Set.mem_range_self j))).trans
      (mul_le_mul_of_nonneg_left (add_le_add_left (hbound N) _) (hε0 N)))
  simpa using hε.mul_const (1+C)

/-- Exact expectation splitting for replacing a state by a fixed state off an event. -/
theorem integral_loop_clip {n : ℕ} (β : ℝ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {A : Set Ω} (hA : MeasurableSet A) (X : Ω → AnchoredCountingState)
    (hX : Measurable X)
    (hm : ∀ q : ℕ, Integrable (fun ω => ‖(X ω).val.2‖^q) (μ.restrict A))
    {w : ℂ} {aux : Fin n → ℂ} (hw : w.im ≠ 0) (haux : ∀ j, (aux j).im ≠ 0) :
    (∫ ω, loopIntegrand β (clipState A X ω) w aux ∂μ) =
      (∫ ω, loopIntegrand β (X ω) w aux ∂(μ.restrict A)) +
        μ.real Aᶜ • loopIntegrand β emptyState w aux := by
  have hfun : (fun ω => loopIntegrand β (clipState A X ω) w aux) =
      A.indicator (fun ω => loopIntegrand β (X ω) w aux) +
        Aᶜ.indicator (fun _ => loopIntegrand β emptyState w aux) := by
    classical
    funext ω
    by_cases ha : ω ∈ A <;> simp [clipState,ha]
  rw [hfun, integral_add'
    ((integrable_indicator_iff hA).2 (integrable_loop_comp (μ.restrict A) X hX hm β hw haux))
    ((integrable_const _).indicator hA.compl), integral_indicator hA,
      integral_indicator_const _ hA.compl]

/-- The full hypothesis (1.6) reduces to absolute vanishing errors after clipping. -/
theorem EventWeightedHierarchy.vanishing_clip
    (h : EventWeightedHierarchy μ β X A) :
    VanishingHierarchy μ β (fun N => clipState (A N) (X N)) := by
  intro n w hw aux haux
  have hh := (h.restricted_loop_tendsto hw haux).add
    (h.exceptional_tendsto.smul_const (loopIntegrand β emptyState w aux))
  simpa only [zero_smul,add_zero,← integral_loop_clip β μ (h.measurable_event _)
    (X _) (h.measurable_state _) (h.moments _) hw haux] using hh

end BourgadeHuang.RationalEdge
