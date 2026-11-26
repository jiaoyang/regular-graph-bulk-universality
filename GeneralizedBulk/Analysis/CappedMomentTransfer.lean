import GeneralizedBulk.ExternalInputs

/-!
# Uncapped limit moments from capped estimates on good events

Only bounded continuous tests are passed through weak convergence. The
exceptional event is multiplied by the fixed test cap, and monotone
convergence removes that cap after taking the weak limit.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace GeneralizedBulk.Analysis

/-- Finite caps are integrable without any integrability premise on f. -/
theorem integrable_nonnegative_cap {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ) (hf : Measurable f)
    (hnonneg : ∀ x, 0 ≤ f x) (K : ℝ) (hK : 0 ≤ K) :
    Integrable (fun x => min (f x) K) P := by
  apply (integrable_const K).mono' ((hf.min measurable_const).aestronglyMeasurable)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hnonneg x) hK)]
  exact min_le_right _ _

/-- Uniform integrals of all finite caps imply an actual uncapped moment,
including integrability of the limiting nonnegative random variable. -/
theorem integrable_of_uniform_capped_integral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (f : Ω → ℝ) (hf : Measurable f) (hnonneg : ∀ x, 0 ≤ f x)
    (C : ℝ) (hC : 0 ≤ C)
    (hcap : ∀ m : ℕ, (∫ x, min (f x) (m : ℝ) ∂P) ≤ C) :
    Integrable f P ∧ (∫ x, f x ∂P) ≤ C := by
  let F := fun m : ℕ => fun x => ENNReal.ofReal (min (f x) (m : ℝ))
  have hF : ∀ m, Measurable (F m) := fun m => (hf.min measurable_const).ennreal_ofReal
  have hmono : Monotone F := by
    intro m n hmn x
    exact ENNReal.ofReal_le_ofReal (min_le_min_left _ (by exact_mod_cast hmn))
  have heq (x : Ω) : (⨆ m, F m x) = ENNReal.ofReal (f x) := by
    apply le_antisymm
    · exact iSup_le (fun m => ENNReal.ofReal_le_ofReal (min_le_left _ _))
    · obtain ⟨m,hm⟩ := exists_nat_ge (f x)
      exact le_iSup_of_le m (by simp only [F, min_eq_left hm, le_refl])
  have hlin : (∫⁻ x, ENNReal.ofReal (f x) ∂P) ≤ ENNReal.ofReal C := by
    simp_rw [← heq]
    rw [lintegral_iSup hF hmono]
    apply iSup_le
    intro m
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_nonnegative_cap P f hf hnonneg m (Nat.cast_nonneg m))
      (Eventually.of_forall (fun x => le_min (hnonneg x) (Nat.cast_nonneg m)))]
    exact ENNReal.ofReal_le_ofReal (hcap m)
  have hi : Integrable f P := ⟨hf.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hnonneg)).mpr
      (hlin.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hnonneg) hf.aestronglyMeasurable]
  simpa only [ENNReal.toReal_ofReal hC] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin

/-- The continuous nonnegative test clipped at a fixed finite height. -/
def nonnegativeCap {E : Type*} [TopologicalSpace E]
    (f : E → ℝ) (hf : Continuous f) (hnonneg : ∀ x, 0 ≤ f x)
    (K : ℝ) (hK : 0 ≤ K) : BoundedContinuousFunction E ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => min (f x) K)
    (hf.min continuous_const) K (fun x => by
      change |min (f x) K| ≤ K
      rw [abs_of_nonneg (le_min (hnonneg x) hK)]
      exact min_le_right _ _)

/-- A finite good-event capped moment controls each fixed weak-convergence
test. The finite-model variable itself need not have an uncapped moment. -/
theorem integral_fixed_cap_le_good_cap_add_bad
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → E) (hX : Measurable X)
    (f : E → ℝ) (hf : Measurable f) (hnonneg : ∀ x, 0 ≤ f x)
    (good : Set Ω) (hgood : MeasurableSet good)
    (K cap C : ℝ) (hK : 0 ≤ K) (hcap : K ≤ cap)
    (hbound : (∫ x, good.indicator (fun x => min (f (X x)) cap) x ∂P) ≤ C) :
    (∫ x, min (f (X x)) K ∂P) ≤ C + K * P.real goodᶜ := by
  have hc : 0 ≤ cap := hK.trans hcap
  have hi0 := integrable_nonnegative_cap P (fun x => f (X x)) (hf.comp hX)
    (fun x => hnonneg (X x)) K hK
  have hi1 := (integrable_nonnegative_cap P (fun x => f (X x)) (hf.comp hX)
    (fun x => hnonneg (X x)) cap hc).indicator hgood
  have hi2 := (integrable_const (μ := P) K).indicator hgood.compl
  have hp (x : Ω) : min (f (X x)) K ≤
      good.indicator (fun x => min (f (X x)) cap) x +
        goodᶜ.indicator (fun _ => K) x := by
    by_cases hx : x ∈ good
    · simp only [Set.indicator_of_mem hx, Set.indicator_of_not_mem (show x ∉ goodᶜ from by simpa only [Set.mem_compl_iff, not_not] using hx), add_zero]
      exact min_le_min_left _ hcap
    · simp only [Set.indicator_of_not_mem hx,
        Set.indicator_of_mem (show x ∈ goodᶜ from hx), zero_add]
      exact min_le_right _ _
  have hh := integral_mono hi0 (hi1.add hi2) hp
  simp only [Pi.add_apply] at hh
  rw [integral_add hi1 hi2, integral_indicator_const K hgood.compl, smul_eq_mul] at hh
  linarith

/-- Capped good-event moments transfer to an actual uncapped moment under
weak convergence, after the exceptional probabilities vanish. -/
theorem weak_limit_moment_of_good_capped_moments
    {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (P : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (P n)]
    (X : ℕ → Ω → E) (hX : ∀ n, Measurable (X n))
    (ν : Measure E) [IsProbabilityMeasure ν]
    (hweak : External.WeakLawConverges (fun n => Measure.map (X n) (P n)) ν)
    (f : E → ℝ) (hf : Continuous f) (hnonneg : ∀ x, 0 ≤ f x)
    (good : ℕ → Set Ω) (hgood : ∀ n, MeasurableSet (good n))
    (hbad : Tendsto (fun n => (P n).real (good n)ᶜ) atTop (𝓝 0))
    (cap : ℕ → ℝ) (hcap : Tendsto cap atTop atTop)
    (C : ℝ) (hC : 0 ≤ C) (bounds : ℕ → ℝ) (hbounds : Tendsto bounds atTop (𝓝 C))
    (hmoment : ∀ᶠ n in atTop, (∫ x, (good n).indicator
      (fun x => min (f (X n x)) (cap n)) x ∂P n) ≤ bounds n) :
    Integrable f ν ∧ (∫ x, f x ∂ν) ≤ C := by
  apply integrable_of_uniform_capped_integral ν f hf.measurable hnonneg C hC
  intro m
  let F := nonnegativeCap f hf hnonneg m (Nat.cast_nonneg m)
  have hlim := hweak F
  have herr : Tendsto (fun n => bounds n + (m : ℝ) * (P n).real (good n)ᶜ)
      atTop (𝓝 C) := by
    simpa only [mul_zero, add_zero] using hbounds.add (hbad.const_mul (m : ℝ))
  apply le_of_tendsto_of_tendsto hlim herr
  filter_upwards [hmoment, hcap.eventually (eventually_ge_atTop (m : ℝ))] with n hn hlarge
  rw [integral_map (hX n).aemeasurable F.continuous.measurable.aestronglyMeasurable]
  exact integral_fixed_cap_le_good_cap_add_bad (P n) (X n) (hX n) f hf.measurable hnonneg
    (good n) (hgood n) m (cap n) (bounds n) (Nat.cast_nonneg m) hlarge hn

end GeneralizedBulk.Analysis
