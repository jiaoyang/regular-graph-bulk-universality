import BourgadeHuang.AnchoredMomentLoop
import BourgadeHuang.ExactAnchoredHierarchy

/-! The absolute-error characterization is formulated for arbitrary random
particle-generated Nevanlinna states, with no finite-size particle number or
polynomial convergence rate. Even pointwise vanishing of the full mixed
hierarchy suffices for the moment and compactness arguments. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang

def VanishingAnchoredHierarchy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (β : Beta) (X : ℕ → Ω → AnchoredCountingState) : Prop :=
  ∀n (w : ℂ),w.im ≠ 0 → ∀aux : Fin n → ℂ,(∀j,(aux j).im ≠ 0) →
    Tendsto (fun N => ∫ω,anchoredLoopIntegrand β (X N ω) w aux ∂μ) atTop (𝓝 0)

theorem integrable_anchoredGrowth_comp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → AnchoredCountingState) (hX : Measurable X)
    (hm : ∀q : ℕ,Integrable (fun ω => ‖(X ω).val.2‖^q) μ)
    {F : AnchoredCountingState → ℂ} (hF : Continuous F) {d : ℕ}
    (hg : AnchoredGrowth F d) : Integrable (fun ω => F (X ω)) μ := by
  obtain ⟨C,hC,hb⟩ := hg
  apply (((integrable_const 1).add (hm d)).const_mul (C*2^(d-1))).mono'
    (hF.measurable.comp hX).aestronglyMeasurable
  apply Eventually.of_forall
  intro ω
  exact (hb (X ω)).trans ((mul_le_mul_of_nonneg_left
    (by simpa only [one_pow] using add_pow_le zero_le_one (norm_nonneg (X ω).val.2) d) hC).trans_eq
      (by simp only [Pi.add_apply]; ring))

theorem integrable_anchoredLoop_comp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → AnchoredCountingState) (hX : Measurable X)
    (hm : ∀q : ℕ,Integrable (fun ω => ‖(X ω).val.2‖^q) μ)
    (β : Beta) {n : ℕ} {w : ℂ} {aux : Fin n → ℂ}
    (hw : w.im ≠ 0) (haux : ∀j,(aux j).im ≠ 0) :
    Integrable (fun ω => anchoredLoopIntegrand β (X ω) w aux) μ :=
  integrable_anchoredGrowth_comp μ X hX hm
    (continuous_anchoredLoopIntegrand β hw haux) (anchoredGrowth_loopIntegrand β hw haux)

theorem uniform_anchor_moments_of_vanishingHierarchy
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (β : Beta) (X : ℕ → Ω → AnchoredCountingState) (hX : ∀N,Measurable (X N))
    (hm : ∀N q : ℕ,Integrable (fun ω => ‖(X N ω).val.2‖^q) μ)
    (h : VanishingAnchoredHierarchy μ β X) (q : ℕ) :
    ∃C : ℝ,∀N,(∫ω,‖(X N ω).val.2‖^q ∂μ) ≤ C := by
  have haux : ∀j,(momentAux q Complex.I j).im ≠ 0 := by
    intro j
    rcases momentAux_eq_or q Complex.I j with hj | hj <;> simp [hj]
  have ht := (h _ Complex.I (by simp) (momentAux q Complex.I) haux).norm
  have hsmall : ∀ᶠN in atTop,
      ‖∫ω,anchoredLoopIntegrand β (X N ω) Complex.I (momentAux q Complex.I) ∂μ‖ ≤ 1 := by
    exact (ht.eventually (gt_mem_nhds (by simp : ‖(0:ℂ)‖ < 1))).mono (fun _ hn => hn.le)
  let D : ℝ := 2*(q+(q+2):ℕ)+2
  let B : ℝ := 2+2*D*(1+(2*D)^(2*q+3))
  have hlarge : ∀ᶠN in atTop,(∫ω,‖(X N ω).val.2‖^(2*q+4) ∂μ) ≤ B := by
    filter_upwards [hsmall] with N hN
    simpa only [B,Nat.add_assoc,mul_one] using integral_moment_bound_of_loop μ (fun ω => ‖(X N ω).val.2‖)
      (fun ω => anchoredLoopIntegrand β (X N ω) Complex.I (momentAux q Complex.I))
      (fun _ => norm_nonneg _) (2*q+3) (C := D) (A := 1) (by dsimp [D]; positivity)
      (hm N _) (hm N _) (integrable_anchoredLoop_comp μ (X N) (hX N) (hm N) β (by simp) haux)
      hN (fun ω => anchored_norm_loopIntegrand_remainder_I β (X N ω) q)
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

end BourgadeHuang
