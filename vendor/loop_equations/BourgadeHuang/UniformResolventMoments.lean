import BourgadeHuang.HierarchyMoments

/-!
# Uniform resolvent moments on off-real compact sets

This proves the full compact-uniform assertion (4.52) of Lemma 4.9 from the
mixed loop hierarchy. The imaginary part has a positive lower bound on an
off-real compact set. Balanced loop equations and Young absorption give the
large-N bound, reflection handles the lower half-plane, and the deterministic
resolvent bound covers the finitely many remaining sizes.
-/

noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter

namespace BourgadeHuang

/-- A nonnegative real power is controlled by the next integer power. -/
theorem rpow_le_one_add_ceil_pow {t q : ℝ} (ht : 0 ≤ t) (hq : 0 ≤ q) :
    t ^ q ≤ 1 + t ^ ⌈q⌉₊ := by
  by_cases ht1 : t ≤ 1
  · exact (Real.rpow_le_one ht ht1 hq).trans
      (le_add_of_nonneg_right (pow_nonneg ht _))
  · have hp : t ^ q ≤ t ^ ⌈q⌉₊ := by
      simpa only [Real.rpow_natCast] using
        Real.rpow_le_rpow_of_exponent_le (le_of_lt (lt_of_not_ge ht1)) (Nat.le_ceil q)
    exact hp.trans (le_add_of_nonneg_left zero_le_one)

/-- Real powers are integrable before the corresponding expectation is used. -/
theorem integrable_rpow_of_ceil_moment {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ}
    (hX : Measurable X) (hXnonneg : ∀ ω, 0 ≤ X ω) {q : ℝ} (hq : 0 ≤ q)
    (hm : Integrable (fun ω => X ω ^ ⌈q⌉₊) μ) :
    Integrable (fun ω => X ω ^ q) μ := by
  apply ((integrable_const 1).add hm).mono'
    ((Real.continuous_rpow_const hq).measurable.comp hX).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => by
    change ‖X ω ^ q‖ ≤ 1 + X ω ^ ⌈q⌉₊
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hXnonneg ω) q)]
    exact rpow_le_one_add_ceil_pow (hXnonneg ω) hq

theorem integrable_microscopicResolvent_norm_rpow {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {N : ℕ} {x : Ω → Fin N → ℝ}
    (hx : ∀ i, Measurable (fun ω => x ω i)) (center : ℝ) {w : ℂ}
    (hw : w.im ≠ 0) {q : ℝ} (hq : 0 ≤ q) :
    Integrable (fun ω => ‖microscopicResolvent (x ω) center w‖ ^ q) μ :=
  integrable_rpow_of_ceil_moment (measurable_microscopicResolvent hx center hw).norm
    (fun _ => norm_nonneg _) hq (integrable_microscopicResolvent_norm_pow hx center hw _)

/-- The complete compact-uniform, integer-moment version of (4.52). -/
theorem uniform_resolvent_moments_of_hierarchy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (β : Beta)
    (x : (N : ℕ) → Ω → Fin N → ℝ) (center : ℝ)
    (hx : ∀ N i, Measurable (fun ω => x N ω i))
    (h : ApproximateHierarchy μ β x center) (K : Set ℂ)
    (hK : IsCompact K) (hKoff : ∀ w ∈ K, w.im ≠ 0) (q : ℕ) :
    ∃ C : ℝ, ∀ N, ∀ w ∈ K,
      (∫ ω, ‖microscopicResolvent (x N ω) center w‖ ^ q ∂μ) ≤ C := by
  let K' : Set ℂ := K ∪ star '' K
  have hK' : IsCompact K' := hK.union (hK.image continuous_star)
  have hK'off : ∀ w ∈ K', w.im ≠ 0 := by
    intro w hw
    rcases hw with hw | ⟨v, hv, rfl⟩
    · exact hKoff w hw
    · simpa using hKoff v hv
  have hstar : ∀ w ∈ K', star w ∈ K' := by
    intro w hw
    rcases hw with hw | ⟨v, hv, rfl⟩
    · exact Or.inr ⟨w, hw, rfl⟩
    · exact Or.inl (by simpa using hv)
  obtain ⟨δ, hδ, hδK⟩ := hK'.exists_forall_le'
    Complex.continuous_im.abs.continuousOn
    (fun w hw => abs_pos.mpr (hK'off w hw))
  have haux (w : ℂ) (hw : w ∈ K') :
      ∀ a, momentAux q w a ∈ K' := by
    intro a
    rcases momentAux_eq_or q w a with ha | ha
    · rw [ha]; exact hw
    · rw [ha]; exact hstar w hw
  have hsmall : ∀ᶠ N in atTop, ∀ w ∈ K',
      ‖∫ ω, loopIntegrand β (x N ω) center w (momentAux q w) ∂μ‖ ≤ 1 := by
    have hh := hierarchy_vanishing μ β x center h (q + (q + 2)) K' hK' hK'off 1
      (by norm_num)
    filter_upwards [hh] with N hN w hw
    exact (hN w hw (momentAux q w) (haux w hw)).le
  let D : ℝ := 1 / δ + 1 + 2 * (q + (q + 2) : ℕ) / δ ^ 2
  have hD : 0 < D := by dsimp [D]; positivity
  let B : ℝ := 2 + 2 * D * (1 + (2 * D) ^ (2 * q + 3))
  have hcoeff (w : ℂ) (hw : w ∈ K') (hwi : 0 < w.im) :
      1 / w.im + 1 + 2 * (q + (q + 2) : ℕ) / w.im ^ 2 ≤ D := by
    have hl : δ ≤ w.im := by simpa [abs_of_pos hwi] using hδK w hw
    have h1 := one_div_le_one_div_of_le hδ hl
    have h2 := div_le_div_of_nonneg_left
      (show (0 : ℝ) ≤ 2 * (q + (q + 2) : ℕ) by positivity)
      (sq_pos_of_pos hδ) (pow_le_pow_left₀ hδ.le hl 2)
    exact add_le_add (add_le_add_right h1 1) h2
  have hlargeUpper : ∀ᶠ N in atTop, ∀ w ∈ K', 0 < w.im →
      (∫ ω, ‖microscopicResolvent (x N ω) center w‖ ^ (2 * q + 4) ∂μ) ≤ B := by
    filter_upwards [hsmall] with N hN w hw hwi
    have hm (j : ℕ) := integrable_microscopicResolvent_norm_pow
      (μ := μ) (hx N) center (hK'off w hw) j
    have hloop := integrable_loopIntegrand (μ := μ) (hx N) β center (hK'off w hw)
      (momentAux q w) (fun a => hK'off _ (haux w hw a))
    have hrem (ω : Ω) :
        ‖loopIntegrand β (x N ω) center w (momentAux q w) -
          ((‖microscopicResolvent (x N ω) center w‖ ^ (2 * q + 4) : ℝ) : ℂ)‖ ≤
          D * (1 + ‖microscopicResolvent (x N ω) center w‖ ^ (2 * q + 3)) :=
      (norm_loopIntegrand_remainder_upper β (x N ω) center q hwi).trans
        (mul_le_mul_of_nonneg_right (hcoeff w hw hwi) (by positivity))
    have habs := integral_moment_bound_of_loop μ
      (fun ω => ‖microscopicResolvent (x N ω) center w‖)
      (fun ω => loopIntegrand β (x N ω) center w (momentAux q w))
      (fun _ => norm_nonneg _) (2 * q + 3) hD (hm _) (hm _) hloop (hN w hw) hrem
    simpa [B] using habs
  have hlarge : ∀ᶠ N in atTop, ∀ w ∈ K',
      (∫ ω, ‖microscopicResolvent (x N ω) center w‖ ^ (2 * q + 4) ∂μ) ≤ B := by
    filter_upwards [hlargeUpper] with N hN w hw
    by_cases hwi : 0 < w.im
    · exact hN w hw hwi
    · have hneg : w.im < 0 := lt_of_le_of_ne (le_of_not_gt hwi) (hK'off w hw)
      have hpos : 0 < (star w).im := by simpa using neg_pos.mpr hneg
      simpa only [microscopicResolvent_reflection, norm_star] using
        hN (star w) (hstar w hw) hpos
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hlarge
  let B₀ : ℝ := ((N₀ : ℝ) / δ + |center|) ^ (2 * q + 4)
  have hall (N : ℕ) (w : ℂ) (hw : w ∈ K') :
      (∫ ω, ‖microscopicResolvent (x N ω) center w‖ ^ (2 * q + 4) ∂μ) ≤ max B B₀ := by
    by_cases hN : N₀ ≤ N
    · exact (hN₀ N hN w hw).trans (le_max_left _ _)
    · apply le_trans _ (le_max_right B B₀)
      have hb (ω : Ω) :
          ‖microscopicResolvent (x N ω) center w‖ ≤ (N₀ : ℝ) / δ + |center| := by
        have hNN : (N : ℝ) ≤ N₀ := by exact_mod_cast (le_of_lt (lt_of_not_ge hN))
        exact (norm_microscopicResolvent_le (x N ω) center (hK'off w hw)).trans
          (add_le_add_right
            ((div_le_div_of_nonneg_left (Nat.cast_nonneg N) hδ (hδK w hw)).trans
              (div_le_div_of_nonneg_right hNN hδ.le)) _)
      calc
        (∫ ω, ‖microscopicResolvent (x N ω) center w‖ ^ (2 * q + 4) ∂μ) ≤
            ∫ _ω : Ω, B₀ ∂μ :=
          integral_mono (integrable_microscopicResolvent_norm_pow (hx N) center (hK'off w hw) _)
            (integrable_const _) (fun ω => pow_le_pow_left₀ (norm_nonneg _) (hb ω) _)
        _ = B₀ := by simp
  refine ⟨1 + max B B₀, fun N w hw => ?_⟩
  have hw' : w ∈ K' := Or.inl hw
  calc
    (∫ ω, ‖microscopicResolvent (x N ω) center w‖ ^ q ∂μ) ≤
        ∫ ω, 1 + ‖microscopicResolvent (x N ω) center w‖ ^ (2 * q + 4) ∂μ :=
      integral_mono (integrable_microscopicResolvent_norm_pow (hx N) center (hKoff w hw) _)
        ((integrable_const 1).add
          (integrable_microscopicResolvent_norm_pow (hx N) center (hKoff w hw) _))
        (fun _ => pow_le_one_add_pow_of_le (norm_nonneg _) (by omega))
    _ = 1 + ∫ ω, ‖microscopicResolvent (x N ω) center w‖ ^ (2 * q + 4) ∂μ := by
      rw [integral_add (integrable_const 1)
        (integrable_microscopicResolvent_norm_pow (hx N) center (hKoff w hw) _)]
      simp
    _ ≤ 1 + max B B₀ := add_le_add_left (hall N w hw') _

/-- Moment bounds for every nonnegative real exponent, uniformly in the size
and the parameter on each off-real compact set. -/
theorem uniform_resolvent_rpow_moments_of_hierarchy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (β : Beta)
    (x : (N : ℕ) → Ω → Fin N → ℝ) (center : ℝ)
    (hx : ∀ N i, Measurable (fun ω => x N ω i))
    (h : ApproximateHierarchy μ β x center) (K : Set ℂ)
    (hK : IsCompact K) (hKoff : ∀ w ∈ K, w.im ≠ 0) {q : ℝ} (hq : 0 ≤ q) :
    ∃ C : ℝ, ∀ N, ∀ w ∈ K,
      (∫ ω, ‖microscopicResolvent (x N ω) center w‖ ^ q ∂μ) ≤ C := by
  obtain ⟨C, hC⟩ := uniform_resolvent_moments_of_hierarchy μ β x center hx h K hK hKoff ⌈q⌉₊
  refine ⟨1 + C, fun N w hw => ?_⟩
  have hm := integrable_microscopicResolvent_norm_pow (μ := μ) (hx N) center (hKoff w hw) ⌈q⌉₊
  calc
    (∫ ω, ‖microscopicResolvent (x N ω) center w‖ ^ q ∂μ) ≤
        ∫ ω, 1 + ‖microscopicResolvent (x N ω) center w‖ ^ ⌈q⌉₊ ∂μ :=
      integral_mono (integrable_microscopicResolvent_norm_rpow (hx N) center (hKoff w hw) hq)
        ((integrable_const 1).add hm)
        (fun _ => rpow_le_one_add_ceil_pow (norm_nonneg _) hq)
    _ = 1 + ∫ ω, ‖microscopicResolvent (x N ω) center w‖ ^ ⌈q⌉₊ ∂μ := by
      rw [integral_add (integrable_const 1) hm]
      simp
    _ ≤ 1 + C := add_le_add_left (hC N w hw) 1

end BourgadeHuang
