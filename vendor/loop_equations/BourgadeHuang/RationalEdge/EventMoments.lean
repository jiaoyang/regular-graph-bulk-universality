import BourgadeHuang.RationalEdge.EventReduction
import BourgadeHuang.RationalEdge.MomentBounds

/-! Absorption of the moment-weighted hierarchy errors on high-probability events. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalEdge

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {β : ℝ} {X : ℕ → Ω → AnchoredCountingState} {A : ℕ → Set Ω}

theorem EventWeightedHierarchy.uniform_clip_moments
    (h : EventWeightedHierarchy μ β X A) (q : ℕ) :
    ∃ C : ℝ, ∀ N, (∫ ω, ‖(clipState (A N) (X N) ω).val.2‖ ^ q ∂μ) ≤ C := by
  let Y := fun N => clipState (A N) (X N)
  have hm (N q : ℕ) : Integrable (fun ω => ‖(Y N ω).val.2‖ ^ q) μ :=
    integrable_clipState_moments μ (h.measurable_event N) (X N) (h.moments N) q
  let K : Set ℂ := {Complex.I, star Complex.I}
  have hK : IsCompact K := (Set.toFinite K).isCompact
  have hoff : ∀ z ∈ K, z.im ≠ 0 := by
    intro z hz
    simp only [K, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl <;> simp
  have haux : ∀ j, momentAux q Complex.I j ∈ K := by
    intro j
    rcases momentAux_eq_or q Complex.I j with hj | hj <;> simp [K, hj]
  obtain ⟨ε,hε,hε0,herr⟩ := h.error (q+(q+2)) K hK hoff
  have hesmall : ∀ᶠ N in atTop, ε N ≤ 1/4 :=
    (hε.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/4))).mono (fun _ hn => hn.le)
  let C : ℝ := coefficientBound β * (q+(q+2):ℕ) + coefficientBound β + 2
  have hC : 0 < C := by dsimp [C]; have := coefficientBound_pos β; positivity
  let B := 1+4*C*(1+(2*C)^(2*q+3))
  have hlarge : ∀ᶠ N in atTop, (∫ ω, ‖(Y N ω).val.2‖^(2*q+4) ∂μ) ≤ B := by
    filter_upwards [hesmall] with N hN
    let F : Ω → ℂ := (A N).indicator (fun ω =>
      loopIntegrand β (X N ω) Complex.I (momentAux q Complex.I))
    have hF : Integrable F μ := (integrable_indicator_iff (h.measurable_event N)).2
      (integrable_loop_comp (μ.restrict (A N)) (X N) (h.measurable_state N)
        (h.moments N) β (by simp) (fun j => hoff _ (haux j)))
    have hlead : (∫ ω, coordinateMaximum (X N ω) Complex.I (momentAux q Complex.I) ^
        (q+(q+2)+2) ∂(μ.restrict (A N))) = ∫ ω, ‖(Y N ω).val.2‖^(2*q+4) ∂μ := by
      simp_rw [coordinateMaximum_momentAux, anchoredNevanlinna_I]
      rw [show q+(q+2)+2=2*q+4 by omega]
      rw [show (fun ω => ‖(Y N ω).val.2‖^(2*q+4)) =
        (A N).indicator (fun ω => ‖(X N ω).val.2‖^(2*q+4)) from
          clipState_anchor_power (A N) (X N) (by omega), integral_indicator (h.measurable_event N)]
    have hsmall : ‖∫ ω,F ω ∂μ‖ ≤ ε N*(1+∫ ω,‖(Y N ω).val.2‖^(2*q+4) ∂μ) := by
      dsimp only [F]
      rw [integral_indicator (h.measurable_event N)]
      simpa only [hlead] using herr N Complex.I (by simp [K]) (momentAux q Complex.I) haux
    have hrem (ω : Ω) : ‖F ω - ((‖(Y N ω).val.2‖^(2*q+4):ℝ):ℂ)‖ ≤
        C*(1+‖(Y N ω).val.2‖^(2*q+3)) := by
      by_cases ha : ω ∈ A N
      · simpa [F,Y,clipState,ha,C] using norm_loopIntegrand_remainder_I β (X N ω) q
      · simpa [F,Y,clipState,ha] using hC.le
    simpa only [B,Nat.add_assoc] using weighted_moment_absorption μ
      (fun ω => ‖(Y N ω).val.2‖) F (fun _ => norm_nonneg _) (2*q+3) hC hN
      (hm N _) (hm N _) hF hsmall hrem
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hlarge
  let B₀ : ℝ := ∑ n ∈ Finset.range N₀, ∫ ω, ‖(Y n ω).val.2‖^(2*q+4) ∂μ
  have hall (N : ℕ) : (∫ ω, ‖(Y N ω).val.2‖^(2*q+4) ∂μ) ≤ max B B₀ := by
    by_cases hN : N₀ ≤ N
    · exact (hN₀ N hN).trans (le_max_left _ _)
    · apply le_trans _ (le_max_right _ _)
      exact Finset.single_le_sum (f := fun n => ∫ ω, ‖(Y n ω).val.2‖^(2*q+4) ∂μ)
        (fun n _ => integral_nonneg (fun _ => pow_nonneg (norm_nonneg _) _))
        (Finset.mem_range.mpr (lt_of_not_ge hN))
  refine ⟨1+max B B₀,fun N => ?_⟩
  calc
    _ ≤ ∫ ω,1+‖(Y N ω).val.2‖^(2*q+4) ∂μ :=
      integral_mono (hm N q) ((integrable_const 1).add (hm N _))
        (fun _ => pow_le_one_add_pow_of_le (norm_nonneg _) (by omega))
    _ = 1+∫ ω,‖(Y N ω).val.2‖^(2*q+4) ∂μ := by
      rw [integral_add (integrable_const 1) (hm N _)]; simp
    _ ≤ _ := add_le_add_left (hall N) _

end BourgadeHuang.RationalEdge
