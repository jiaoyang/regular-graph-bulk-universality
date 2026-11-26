import BourgadeHuang.LoopBounds

/-!
# Counting moments from the full loop hierarchy

This is the uniform-moment argument of Lemma 4.9 at the parameter `i`, which
is sufficient for every bounded counting interval.  Finite-size integrability
comes from the deterministic denominator bounds, before any moment absorption.
-/

noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter

namespace BourgadeHuang

theorem pow_le_one_add_pow_of_le {x : ℝ} (hx : 0 ≤ x) {a b : ℕ} (hab : a ≤ b) :
    x ^ a ≤ 1 + x ^ b := by
  by_cases h : x ≤ 1
  · have hp : x ^ a ≤ 1 := pow_le_one₀ hx h
    linarith [pow_nonneg hx b]
  · have hp := pow_le_pow_right₀ (le_of_lt (lt_of_not_ge h)) hab
    linarith

theorem uniform_resolvent_moments_I_of_hierarchy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (β : Beta)
    (x : (N : ℕ) → Ω → Fin N → ℝ) (center : ℝ)
    (hx : ∀ N i, Measurable (fun ω => x N ω i))
    (h : ApproximateHierarchy μ β x center) (q : ℕ) :
    ∃ C : ℝ, ∀ N, (∫ ω, ‖microscopicResolvent (x N ω) center Complex.I‖ ^ q ∂μ) ≤ C := by
  let K : Set ℂ := {Complex.I, star Complex.I}
  have hK : IsCompact K := Set.Finite.isCompact (by exact Set.toFinite _)
  have hKoff : ∀ w ∈ K, w.im ≠ 0 := by
    intro w hw
    rcases hw with hw | hw
    · subst w; simp
    · have hw' : w = star Complex.I := Set.mem_singleton_iff.mp hw
      subst w; simp
  have haux : ∀ a, momentAux q Complex.I a ∈ K := by
    intro a
    rcases momentAux_eq_or q Complex.I a with ha | ha <;> simp [ha, K]
  have hi : Complex.I.im ≠ 0 := by simp
  have hsmall : ∀ᶠ N in atTop,
      ‖∫ ω, loopIntegrand β (x N ω) center Complex.I (momentAux q Complex.I) ∂μ‖ ≤ 1 := by
    have hh := hierarchy_vanishing μ β x center h (q + (q + 2)) K hK hKoff 1 (by norm_num)
    filter_upwards [hh] with N hN
    exact (hN Complex.I (by simp [K]) (momentAux q Complex.I) haux).le
  let D : ℝ := 2 * (q + (q + 2) : ℕ) + 2
  have hD : 0 < D := by dsimp [D]; positivity
  let B : ℝ := 2 + 2 * D * (1 + (2 * D) ^ (2 * q + 3))
  have hlarge : ∀ᶠ N in atTop,
      (∫ ω, ‖microscopicResolvent (x N ω) center Complex.I‖ ^ (2 * q + 4) ∂μ) ≤ B := by
    filter_upwards [hsmall] with N hN
    have hm (j : ℕ) := integrable_microscopicResolvent_norm_pow (μ := μ) (hx N) center hi j
    have hloop := integrable_loopIntegrand (μ := μ) (hx N) β center hi
      (momentAux q Complex.I) (fun a => hKoff _ (haux a))
    have habs := integral_moment_bound_of_loop μ
      (fun ω => ‖microscopicResolvent (x N ω) center Complex.I‖)
      (fun ω => loopIntegrand β (x N ω) center Complex.I (momentAux q Complex.I))
      (fun _ => norm_nonneg _) (2 * q + 3) hD (hm _) (hm _) hloop hN
      (fun ω => norm_loopIntegrand_remainder β (x N ω) center q)
    simpa [B, D] using habs
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hlarge
  let B₀ : ℝ := (N₀ + |center|) ^ (2 * q + 4)
  have hall (N : ℕ) :
      (∫ ω, ‖microscopicResolvent (x N ω) center Complex.I‖ ^ (2 * q + 4) ∂μ) ≤ max B B₀ := by
    by_cases hN : N₀ ≤ N
    · exact (hN₀ N hN).trans (le_max_left _ _)
    · apply le_trans _ (le_max_right B B₀)
      have hb (ω : Ω) : ‖microscopicResolvent (x N ω) center Complex.I‖ ≤ N₀ + |center| := by
        have hpoint : ‖microscopicResolvent (x N ω) center Complex.I‖ ≤ N + |center| := by
          simpa using norm_microscopicResolvent_le (x N ω) center hi
        exact hpoint.trans (add_le_add_right (by exact_mod_cast (le_of_lt (lt_of_not_ge hN))) _)
      calc
        (∫ ω, ‖microscopicResolvent (x N ω) center Complex.I‖ ^ (2 * q + 4) ∂μ) ≤
            ∫ _ω : Ω, B₀ ∂μ :=
          integral_mono (integrable_microscopicResolvent_norm_pow (hx N) center hi _)
            (integrable_const _) (fun ω => pow_le_pow_left₀ (norm_nonneg _) (hb ω) _)
        _ = B₀ := by simp
  refine ⟨1 + max B B₀, fun N => ?_⟩
  calc
    (∫ ω, ‖microscopicResolvent (x N ω) center Complex.I‖ ^ q ∂μ) ≤
        ∫ ω, 1 + ‖microscopicResolvent (x N ω) center Complex.I‖ ^ (2 * q + 4) ∂μ :=
      integral_mono (integrable_microscopicResolvent_norm_pow (hx N) center hi _)
        ((integrable_const 1).add (integrable_microscopicResolvent_norm_pow (hx N) center hi _))
        (fun _ => pow_le_one_add_pow_of_le (norm_nonneg _) (by omega))
    _ = 1 + ∫ ω, ‖microscopicResolvent (x N ω) center Complex.I‖ ^ (2 * q + 4) ∂μ := by
      rw [integral_add (integrable_const 1) (integrable_microscopicResolvent_norm_pow (hx N) center hi _)]
      simp
    _ ≤ 1 + max B B₀ := add_le_add_left (hall N) _

end BourgadeHuang
