import BourgadeHuang.RationalBulk.GaussianBetaSample
import BourgadeHuang.RationalBulk.EventVanishing
import BourgadeHuang.RationalBulk.Limits

/-! Passage from the literal finite Gaussian-beta integration-by-parts identity
to the full moment-weighted hypothesis and a genuine Gaussian-beta subsequential
bulk law. The finite identity is the only input of this assembly lemma. -/
noncomputable section
open scoped BigOperators Topology ENNReal
open MeasureTheory Filter
namespace BourgadeHuang.RationalBulk

def resolventMonomial {n : ℕ} (s : AnchoredCountingState) (w : ℂ)
    (aux : Fin n → ℂ) : ℂ :=
  anchoredNevanlinna s w * ∏ a, anchoredNevanlinna s (aux a)

theorem continuous_resolventMonomial {n : ℕ} {w : ℂ} {aux : Fin n → ℂ}
    (hw : w.im ≠ 0) (haux : ∀ a, (aux a).im ≠ 0) :
    Continuous (fun s => resolventMonomial s w aux) := by
  exact (continuous_anchoredNevanlinna hw).mul
    (continuous_finset_prod _ fun a _ => continuous_anchoredNevanlinna (haux a))

theorem growth_resolventMonomial {n : ℕ} {w : ℂ} {aux : Fin n → ℂ}
    (hw : w.im ≠ 0) (haux : ∀ a, (aux a).im ≠ 0) :
    AnchoredGrowth (fun s => resolventMonomial s w aux) (n+1) := by
  have hp : AnchoredGrowth (fun s => ∏ a, anchoredNevanlinna s (aux a)) n := by
    simpa using AnchoredGrowth.finset_prod Finset.univ
      (fun a s => anchoredNevanlinna s (aux a))
      (fun a _ => anchoredGrowth_nevanlinna (haux a))
  simpa only [Nat.add_comm 1] using (anchoredGrowth_nevanlinna hw).mul hp

theorem norm_resolventMonomial_le_maximum {n : ℕ} (s : AnchoredCountingState)
    (w : ℂ) (aux : Fin n → ℂ) :
    ‖resolventMonomial s w aux‖ ≤ coordinateMaximum s w aux ^ (n+1) := by
  let R := coordinateMaximum s w aux
  have hR : 0 ≤ R := coordinateMaximum_nonneg s w aux
  have hm : ‖anchoredNevanlinna s w‖ ≤ R := by
    exact Finset.le_sup' (fun j : Fin (n+1) =>
      ‖anchoredNevanlinna s (Fin.cons (α := fun _ => ℂ) w aux j)‖)
      (Finset.mem_univ 0)
  have ha (a : Fin n) : ‖anchoredNevanlinna s (aux a)‖ ≤ R := by
    exact Finset.le_sup' (fun j : Fin (n+1) =>
      ‖anchoredNevanlinna s (Fin.cons (α := fun _ => ℂ) w aux j)‖)
      (Finset.mem_univ a.succ)
  unfold resolventMonomial
  rw [norm_mul, norm_prod]
  calc
    _ ≤ R * ∏ a : Fin n, R := mul_le_mul hm
      (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun a _ => ha a))
      (Finset.prod_nonneg fun _ _ => norm_nonneg _) hR
    _ = _ := by simp [R, pow_succ, mul_comm]

theorem integrable_resolventMonomial_comp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → AnchoredCountingState)
    (hX : Measurable X) (hm : ∀ q : ℕ, Integrable (fun ω => ‖(X ω).val.2‖^q) μ)
    {n : ℕ} {w : ℂ} {aux : Fin n → ℂ}
    (hw : w.im ≠ 0) (haux : ∀ a, (aux a).im ≠ 0) :
    Integrable (fun ω => resolventMonomial (X ω) w aux) μ :=
  integrable_anchoredGrowth_comp μ X hX hm
    (continuous_resolventMonomial hw haux) (growth_resolventMonomial hw haux)

theorem norm_integral_resolventMonomial_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → AnchoredCountingState)
    (hX : Measurable X) (hm : ∀ q : ℕ, Integrable (fun ω => ‖(X ω).val.2‖^q) μ)
    {n : ℕ} {w : ℂ} {aux : Fin n → ℂ}
    (hw : w.im ≠ 0) (haux : ∀ a, (aux a).im ≠ 0) :
    ‖∫ ω, resolventMonomial (X ω) w aux ∂μ‖ ≤
      1 + ∫ ω, coordinateMaximum (X ω) w aux ^ (n+2) ∂μ := by
  have hi := integrable_resolventMonomial_comp μ X hX hm hw haux
  have hM := integrable_coordinateMaximum_power μ X hX hm hw haux (n+2)
  calc
    _ ≤ ∫ ω, ‖resolventMonomial (X ω) w aux‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, 1 + coordinateMaximum (X ω) w aux ^ (n+2) ∂μ :=
      integral_mono hi.norm ((integrable_const 1).add hM) fun ω =>
        (norm_resolventMonomial_le_maximum _ _ _).trans
          (pow_le_one_add_pow_of_le (coordinateMaximum_nonneg _ _ _) (by omega))
    _ = _ := by rw [integral_add (integrable_const 1) hM]; simp

/-- The exact finite eigenvalue identity gives the literal locally uniform
moment-weighted loop hypothesis, with the good event equal to the whole space. -/
theorem gaussianBeta_eventWeighted_of_finite_identity (β : ℝ) (hβ : 0 < β)
    (hloop : ∀ N n (w : ℂ), w.im ≠ 0 → ∀ aux : Fin n → ℂ,
      (∀ a, (aux a).im ≠ 0) →
      (∫ x, loopIntegrand β (finiteAnchoredState x 0) w aux
        ∂gaussianBetaMeasure β (N+1)) =
        -(w / (N+1:ℂ)) * ∫ x, resolventMonomial (finiteAnchoredState x 0) w aux
          ∂gaussianBetaMeasure β (N+1)) :
    EventWeightedHierarchy (gaussianBetaProduct β hβ) β gaussianBetaState (fun _ => Set.univ) := by
  refine ⟨measurable_gaussianBetaState, fun _ => MeasurableSet.univ, ?_, ?_, ?_⟩
  · simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
  · intro N q
    simpa using gaussianBetaState_moment β hβ N q
  · intro n K hK hoff
    obtain ⟨C,hC,hbound⟩ := hK.isBounded.exists_pos_norm_le
    refine ⟨fun N => C / (N+1), ?_, (fun N => by positivity), ?_⟩
    · simpa only [mul_one_div, mul_zero] using
        tendsto_one_div_add_atTop_nhds_zero_nat.const_mul C
    · intro N w hw aux haux
      simp only [Measure.restrict_univ]
      have hw0 := hoff w hw
      have ha0 (a) := hoff (aux a) (haux a)
      have hi := gaussianBetaProduct_integral β hβ N
        (fun x => loopIntegrand β (finiteAnchoredState x 0) w aux)
        ((continuous_loopIntegrand β hw0 ha0).measurable.comp
          (measurable_finiteAnchoredState (N+1) 0)).stronglyMeasurable
      have hm := gaussianBetaProduct_integral β hβ N
        (fun x => resolventMonomial (finiteAnchoredState x 0) w aux)
        ((continuous_resolventMonomial hw0 ha0).measurable.comp
          (measurable_finiteAnchoredState (N+1) 0)).stronglyMeasurable
      change ‖∫ ω, loopIntegrand β (finiteAnchoredState (ω N) 0) w aux
        ∂gaussianBetaProduct β hβ‖ ≤ _
      rw [hi, hloop N n w hw0 aux ha0, ← hm, norm_mul, norm_neg, norm_div]
      have hn : ‖(N+1:ℂ)‖ = (N+1:ℝ) := by
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_add,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [hn]
      exact mul_le_mul (div_le_div_of_nonneg_right (hbound w hw) (by positivity))
        (norm_integral_resolventMonomial_le (gaussianBetaProduct β hβ) (gaussianBetaState N)
          (measurable_gaussianBetaState N) (gaussianBetaState_moment β hβ N) hw0 ha0)
        (norm_nonneg _) (by positivity)

/-- The same finite identity gives actual Gaussian beta subsequential bulk
limits with exact loop equations and exponential anchor moments. -/
theorem gaussianBeta_exact_subsequence_of_finite_identity (β : ℝ) (hβ : 0 < β)
    (hloop : ∀ N n (w : ℂ), w.im ≠ 0 → ∀ aux : Fin n → ℂ,
      (∀ a, (aux a).im ≠ 0) →
      (∫ x, loopIntegrand β (finiteAnchoredState x 0) w aux
        ∂gaussianBetaMeasure β (N+1)) =
        -(w / (N+1:ℂ)) * ∫ x, resolventMonomial (finiteAnchoredState x 0) w aux
          ∂gaussianBetaMeasure β (N+1)) :
    ∃ (ν : ProbabilityMeasure AnchoredCountingState) (r : ℕ → ℕ), StrictMono r ∧
      WeakLawConverges (gaussianBetaProduct β hβ) (fun N => gaussianBetaState (r N))
        (ν : Measure AnchoredCountingState) ∧ ExactHierarchy (ν : Measure AnchoredCountingState) β ∧
      ∃ a : ℝ, 0 < a ∧ Integrable
        (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2))
        (ν : Measure AnchoredCountingState) := by
  have he := gaussianBeta_eventWeighted_of_finite_identity β hβ hloop
  have hv : VanishingHierarchy (gaussianBetaProduct β hβ) β gaussianBetaState := by
    intro n w hw aux haux
    simpa only [Measure.restrict_univ] using he.restricted_loop_tendsto hw haux
  exact exists_exact_anchored_subsequence_of_vanishingHierarchy
    (gaussianBetaProduct β hβ) β gaussianBetaState measurable_gaussianBetaState
    (gaussianBetaState_moment β hβ) hv

end BourgadeHuang.RationalBulk
