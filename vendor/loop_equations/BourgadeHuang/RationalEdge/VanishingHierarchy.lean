import BourgadeHuang.RationalEdge.MomentBounds

noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalEdge

theorem uniform_anchor_moments_of_vanishingHierarchy
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (β : ℝ) (X : ℕ → Ω → AnchoredCountingState) (hX : ∀N,Measurable (X N))
    (hm : ∀N q : ℕ,Integrable (fun ω => ‖(X N ω).val.2‖^q) μ)
    (h : VanishingHierarchy μ β X) (q : ℕ) :
    ∃C : ℝ,∀N,(∫ω,‖(X N ω).val.2‖^q ∂μ) ≤ C := by
  have haux : ∀j,(momentAux q Complex.I j).im ≠ 0 := by
    intro j
    rcases momentAux_eq_or q Complex.I j with hj | hj <;> simp [hj]
  have ht := (h _ Complex.I (by simp) (momentAux q Complex.I) haux).norm
  have hsmall : ∀ᶠN in atTop,
      ‖∫ω,loopIntegrand β (X N ω) Complex.I (momentAux q Complex.I) ∂μ‖ ≤ 1 := by
    exact (ht.eventually (gt_mem_nhds (by simp : ‖(0:ℂ)‖ < 1))).mono (fun _ hn => hn.le)
  let D : ℝ := coefficientBound β*(q+(q+2):ℕ)+coefficientBound β+2
  let B : ℝ := 2+2*D*(1+(2*D)^(2*q+3))
  have hlarge : ∀ᶠN in atTop,(∫ω,‖(X N ω).val.2‖^(2*q+4) ∂μ) ≤ B := by
    filter_upwards [hsmall] with N hN
    simpa only [B,Nat.add_assoc,mul_one] using integral_moment_bound_of_loop μ (fun ω => ‖(X N ω).val.2‖)
      (fun ω => loopIntegrand β (X N ω) Complex.I (momentAux q Complex.I))
      (fun _ => norm_nonneg _) (2*q+3) (C := D) (A := 1) (by dsimp [D]; have := (coefficientBound_pos β).le; positivity)
      (hm N _) (hm N _) (integrable_loop_comp μ (X N) (hX N) (hm N) β (by simp) haux)
      hN (fun ω => norm_loopIntegrand_remainder_I β (X N ω) q)
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hlarge
  let B₀ : ℝ := ∑n∈Finset.range N₀,∫ω,‖(X n ω).val.2‖^(2*q+4) ∂μ
  have hall (N : ℕ) : (∫ω,‖(X N ω).val.2‖^(2*q+4) ∂μ) ≤ max B B₀ := by
    by_cases hN : N₀ ≤ N
    · exact (hN₀ N hN).trans (le_max_left _ _)
    · apply le_trans _ (le_max_right _ _)
      change (∫ω,‖(X N ω).val.2‖^(2*q+4) ∂μ) ≤
        ∑n∈Finset.range N₀,∫ω,‖(X n ω).val.2‖^(2*q+4) ∂μ
      exact Finset.single_le_sum (f := fun n => ∫ω,‖(X n ω).val.2‖^(2*q+4) ∂μ)
        (fun n _ => integral_nonneg (fun ω => pow_nonneg (norm_nonneg (X n ω).val.2) _))
        (Finset.mem_range.mpr (lt_of_not_ge hN))
  refine ⟨1+max B B₀,fun N => ?_⟩
  calc
    _ ≤ ∫ω,1+‖(X N ω).val.2‖^(2*q+4) ∂μ :=
      integral_mono (hm N q) ((integrable_const 1).add (hm N _))
        (fun _ => pow_le_one_add_pow_of_le (norm_nonneg _) (by omega))
    _ = 1+∫ω,‖(X N ω).val.2‖^(2*q+4) ∂μ := by
      rw [integral_add (integrable_const 1) (hm N _)]
      simp
    _ ≤ _ := add_le_add_left (hall N) _

end BourgadeHuang.RationalEdge
