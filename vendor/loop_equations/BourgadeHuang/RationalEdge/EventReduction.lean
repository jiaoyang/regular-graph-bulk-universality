import BourgadeHuang.RationalEdge.Foundation

/-! Event restriction and moment-weighted errors in Bourgade--Huang (1.6).
The clipping operation changes a random state only on the exceptional event. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalEdge

/-- The zero Nevanlinna function, with the empty pole configuration. -/
def emptyState : AnchoredCountingState :=
  ⟨(⟨0, inferInstance, fun _ _ => ⟨0, by simp⟩⟩, 0), fun _ => by simp⟩

@[simp] theorem emptyState_anchor : emptyState.val.2 = 0 := rfl

/-- Replace the state outside a good event by the zero Nevanlinna function. -/
def clipState {Ω : Type*} (A : Set Ω) (X : Ω → AnchoredCountingState)
    (ω : Ω) : AnchoredCountingState := by
  classical
  exact if ω ∈ A then X ω else emptyState

theorem clipState_eq_of_mem {Ω : Type*} (A : Set Ω) (X : Ω → AnchoredCountingState)
    {ω : Ω} (h : ω ∈ A) : clipState A X ω = X ω := by simp [clipState, h]

theorem clipState_eq_of_not_mem {Ω : Type*} (A : Set Ω) (X : Ω → AnchoredCountingState)
    {ω : Ω} (h : ω ∉ A) : clipState A X ω = emptyState := by simp [clipState, h]

theorem measurable_clipState {Ω : Type*} [MeasurableSpace Ω] {A : Set Ω}
    (hA : MeasurableSet A) {X : Ω → AnchoredCountingState} (hX : Measurable X) :
    Measurable (clipState A X) := by
  classical
  exact hX.piecewise hA measurable_const

theorem clipState_anchor_power {Ω : Type*} (A : Set Ω) (X : Ω → AnchoredCountingState)
    {q : ℕ} (hq : q ≠ 0) :
    (fun ω => ‖(clipState A X ω).val.2‖ ^ q) =
      A.indicator (fun ω => ‖(X ω).val.2‖ ^ q) := by
  classical
  funext ω
  by_cases h : ω ∈ A <;> simp [clipState, h, hq]

theorem integrable_clipState_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {A : Set Ω} (hA : MeasurableSet A)
    (X : Ω → AnchoredCountingState)
    (hm : ∀ q : ℕ, Integrable (fun ω => ‖(X ω).val.2‖ ^ q) (μ.restrict A))
    (q : ℕ) : Integrable (fun ω => ‖(clipState A X ω).val.2‖ ^ q) μ := by
  by_cases hq : q = 0
  · subst q; simpa using (integrable_const (1 : ℝ) : Integrable _ μ)
  · rw [clipState_anchor_power A X hq]
    exact (integrable_indicator_iff hA).2 (hm q)

/-- The literal maximum over the `p=n+1` spectral parameters of (1.6). -/
def coordinateMaximum {n : ℕ} (s : AnchoredCountingState) (w : ℂ)
    (aux : Fin n → ℂ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j : Fin (n+1) =>
    ‖anchoredNevanlinna s (Fin.cons (α := fun _ => ℂ) w aux j)‖)

theorem coordinateMaximum_nonneg {n : ℕ} (s : AnchoredCountingState)
    (w : ℂ) (aux : Fin n → ℂ) : 0 ≤ coordinateMaximum s w aux := by
  unfold coordinateMaximum
  exact (norm_nonneg (anchoredNevanlinna s w)).trans
    (Finset.le_sup' (fun j : Fin (n+1) => ‖anchoredNevanlinna s (Fin.cons (α := fun _ => ℂ) w aux j)‖)
      (Finset.mem_univ 0))

theorem coordinateMaximum_momentAux (s : AnchoredCountingState) (r : ℕ) (w : ℂ) :
    coordinateMaximum s w (momentAux r w) = ‖anchoredNevanlinna s w‖ := by
  unfold coordinateMaximum
  apply le_antisymm
  · apply Finset.sup'_le
    intro j _
    refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · simpa using (anchored_norm_momentAux_resolvent s r w j).le
  · exact Finset.le_sup' (fun j : Fin (r+(r+2)+1) =>
      ‖anchoredNevanlinna s (Fin.cons (α := fun _ => ℂ) w (momentAux r w) j)‖)
        (Finset.mem_univ 0)

/-- Young absorption remains valid when the hierarchy error is proportional to
one plus the very moment being estimated. This is the non-circular step (2.17). -/
theorem weighted_moment_absorption {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (F : Ω → ℂ)
    (hX : ∀ ω, 0 ≤ X ω) (n : ℕ) {C ε : ℝ} (hC : 0 < C)
    (hε : ε ≤ 1/4)
    (hn : Integrable (fun ω => X ω ^ n) μ)
    (hn1 : Integrable (fun ω => X ω ^ (n + 1)) μ)
    (hF : Integrable F μ)
    (hsmall : ‖∫ ω, F ω ∂μ‖ ≤ ε * (1 + ∫ ω, X ω ^ (n+1) ∂μ))
    (hrem : ∀ ω, ‖F ω - ((X ω ^ (n+1) : ℝ) : ℂ)‖ ≤ C * (1 + X ω ^ n)) :
    (∫ ω, X ω ^ (n+1) ∂μ) ≤ 1 + 4*C*(1+(2*C)^n) := by
  have hb := integral_moment_bound_of_loop μ X F hX n hC hn hn1 hF hsmall hrem
  have ht : 0 ≤ ∫ ω, X ω ^ (n+1) ∂μ := integral_nonneg fun ω => pow_nonneg (hX ω) _
  have he := mul_le_mul_of_nonneg_right hε (show 0 ≤ 1 + ∫ ω, X ω ^ (n+1) ∂μ by linarith)
  nlinarith

/-- Full event-restricted, locally uniform, moment-weighted edge loop hypothesis.
Only integer moments at the anchor are needed; the Nevanlinna bound gives every
finite moment at every off-real spectral parameter. -/
structure EventWeightedHierarchy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (β : ℝ) (X : ℕ → Ω → AnchoredCountingState)
    (A : ℕ → Set Ω) : Prop where
  measurable_state : ∀ N, Measurable (X N)
  measurable_event : ∀ N, MeasurableSet (A N)
  exceptional_tendsto : Tendsto (fun N => μ.real (A N)ᶜ) atTop (𝓝 0)
  moments : ∀ N q : ℕ, Integrable (fun ω => ‖(X N ω).val.2‖ ^ q) (μ.restrict (A N))
  error : ∀ n : ℕ, ∀ K : Set ℂ, IsCompact K → (∀ z ∈ K, z.im ≠ 0) →
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ (∀ N, 0 ≤ ε N) ∧
      ∀ N (w : ℂ), w ∈ K → ∀ aux : Fin n → ℂ, (∀ j, aux j ∈ K) →
        ‖∫ ω, loopIntegrand β (X N ω) w aux ∂(μ.restrict (A N))‖ ≤
          ε N * (1 + ∫ ω, coordinateMaximum (X N ω) w aux ^ (n+2)
            ∂(μ.restrict (A N)))

end BourgadeHuang.RationalEdge
