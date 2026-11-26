import BourgadeHuang.RationalEdge.VanishingHierarchy

/-! Factorial anchor moments follow from absolute vanishing mixed loop errors
for arbitrary random particle-generated Nevanlinna functions. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalEdge

theorem eventually_adjacent_anchor_moments_of_vanishingHierarchy
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (β : ℝ) (X : ℕ → Ω → AnchoredCountingState) (hX : ∀N,Measurable (X N))
    (hm : ∀N q : ℕ,Integrable (fun ω => ‖(X N ω).val.2‖^q) μ)
    (h : VanishingHierarchy μ β X) (r : ℕ) :
    ∀ᶠN in atTop,(∫ω,‖(X N ω).val.2‖^(2*r+4) ∂μ) ≤
      2+(4*coefficientBound β*r+4*coefficientBound β+(coefficientBound β)^2+2:ℝ)*(∫ω,‖(X N ω).val.2‖^(2*r+2) ∂μ) := by
  have haux : ∀j,(momentAux r Complex.I j).im ≠ 0 := by
    intro j
    rcases momentAux_eq_or r Complex.I j with hj | hj <;> simp [hj]
  have ht := (h _ Complex.I (by simp) (momentAux r Complex.I) haux).norm
  have hsmall := ht.eventually (gt_mem_nhds (by simp : ‖(0:ℂ)‖ < 1))
  filter_upwards [hsmall] with N hN
  have hb := integral_even_moment_recurrence μ (fun ω => ‖(X N ω).val.2‖)
    (fun ω => loopIntegrand β (X N ω) Complex.I (momentAux r Complex.I))
    (fun _ => norm_nonneg _) (2*r+2) (hm N _) (hm N _)
    (integrable_loop_comp μ (X N) (hX N) (hm N) β (by simp) haux) hN.le
    (fun ω => by
      simpa only [anchoredNevanlinna_I,Complex.I_im,Complex.norm_I,one_pow,div_one,Nat.add_assoc] using
        norm_loopIntegrand_remainder_half_leading β (X N ω) r
          (show 0 < Complex.I.im by simp))
  convert hb using 1
  push_cast
  ring

theorem eventually_factorial_anchor_moments_of_vanishingHierarchy
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (β : ℝ) (X : ℕ → Ω → AnchoredCountingState) (hX : ∀N,Measurable (X N))
    (hm : ∀N q : ℕ,Integrable (fun ω => ‖(X N ω).val.2‖^q) μ)
    (h : VanishingHierarchy μ β X) :
    ∃C : ℝ,1 ≤ C ∧ ∀q : ℕ,∀ᶠN in atTop,
      (∫ω,‖(X N ω).val.2‖^(2*q) ∂μ) ≤ C^q*(q.factorial:ℝ) := by
  obtain ⟨B,hB⟩ := uniform_anchor_moments_of_vanishingHierarchy μ β X hX hm h 2
  let C : ℝ := max 1 (max B (4+4*coefficientBound β+(coefficientBound β)^2))
  have hC1 : 1 ≤ C := le_max_left _ _
  have hBC : B ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hDC : 4+4*coefficientBound β+(coefficientBound β)^2 ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hsucc : ∀r : ℕ,∀ᶠN in atTop,
      (∫ω,‖(X N ω).val.2‖^(2*r+2) ∂μ) ≤ C^(r+1)*((r+1).factorial:ℝ) := by
    intro r
    induction r with
    | zero => exact Eventually.of_forall (fun N => by simpa using (hB N).trans hBC)
    | succ r ih =>
      filter_upwards [ih,eventually_adjacent_anchor_moments_of_vanishingHierarchy μ β X hX hm h r]
        with N hprev hnext
      let A : ℝ := C^(r+1)*((r+1).factorial:ℝ)
      have hA1 : 1 ≤ A := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hC1)
        (by exact_mod_cast Nat.factorial_pos (r+1))
      have hpoly : (4*coefficientBound β*r+4*coefficientBound β+(coefficientBound β)^2+4:ℝ) ≤ C*(r+2) := by
        have hh := mul_le_mul_of_nonneg_right hDC (show (0:ℝ) ≤ r+2 by positivity)
        nlinarith [show (0:ℝ) ≤ r by positivity, coefficientBound_pos β, mul_nonneg (sq_nonneg (coefficientBound β)) (show (0:ℝ) ≤ r by positivity)]
      calc
        _ ≤ 2+(4*coefficientBound β*r+4*coefficientBound β+(coefficientBound β)^2+2:ℝ)*A := by
          convert hnext.trans (add_le_add_left
            (mul_le_mul_of_nonneg_left hprev (by have := (coefficientBound_pos β).le; positivity)) 2) using 1
        _ ≤ (4*coefficientBound β*r+4*coefficientBound β+(coefficientBound β)^2+4:ℝ)*A := by nlinarith
        _ ≤ (C*(r+2))*A := mul_le_mul_of_nonneg_right hpoly (by linarith)
        _ = _ := by
          simp only [A,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
          ring
  refine ⟨C,hC1,?_⟩
  intro q
  cases q with
  | zero => exact Eventually.of_forall (fun N => by simp)
  | succ r => simpa [Nat.mul_add] using hsucc r

end BourgadeHuang.RationalEdge
