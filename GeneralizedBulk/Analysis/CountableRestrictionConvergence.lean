import GeneralizedBulk.Analysis.TruncationConvergence

/-! Weak convergence on every natural-number stratum implies convergence
of the full probability laws. The count-tail control follows from the
stratum masses; it is not an additional tightness assumption. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace GeneralizedBulk.Analysis
variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]

theorem integral_count_le_eq_sum (μ : Measure E) [IsFiniteMeasure μ]
    (c : E → ℕ) (hc : Measurable c) (F : BoundedContinuousFunction E ℝ) (R : ℕ) :
    (∫ x in {x | c x ≤ R},F x ∂μ) =
      ∑ m ∈ Finset.range (R+1),∫ x in {x | c x = m},F x ∂μ := by
  classical
  have hs : {x | c x ≤ R} = ⋃ m ∈ Finset.range (R+1),{x | c x=m} := by
    ext x
    simp only [mem_setOf_eq,mem_iUnion,Finset.mem_range]
    constructor
    · intro hx
      exact ⟨c x,by omega,rfl⟩
    · rintro ⟨m,hm,hx⟩
      omega
  rw [hs]
  apply integral_finset_biUnion
  · intro m hm
    exact hc (measurableSet_singleton m)
  · intro m hm l hl hml
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hml (hx.symm.trans hy)
  · intro m hm
    exact F.integrable (μ.restrict _)

theorem tendsto_integral_count_le (μ : Measure E) [IsFiniteMeasure μ]
    (c : E → ℕ) (hc : Measurable c) (F : BoundedContinuousFunction E ℝ) :
    Tendsto (fun R => ∫ x in {x | c x ≤ R},F x ∂μ) atTop (𝓝 (∫ x,F x ∂μ)) := by
  have hs : (⋃ R : ℕ,{x | c x≤R}) = univ := by
    ext x
    simp only [mem_iUnion,mem_setOf_eq,mem_univ,iff_true]
    exact ⟨c x,le_rfl⟩
  have hm : ∀ R,MeasurableSet {x | c x≤R} := fun R => hc (Set.to_countable (Set.Iic R)).measurableSet
  have hmono : Monotone (fun R : ℕ => {x | c x≤R}) := fun R S hRS x hx => hx.trans hRS
  have hi : IntegrableOn F (⋃ R : ℕ,{x | c x≤R}) μ := (F.integrable μ).integrableOn
  simpa only [hs,setIntegral_univ] using tendsto_setIntegral_of_monotone hm hmono hi

theorem norm_integral_sub_count_le_le (μ : Measure E) [IsProbabilityMeasure μ]
    (c : E → ℕ) (hc : Measurable c) (F : BoundedContinuousFunction E ℝ) (R : ℕ) :
    ‖(∫ x,F x ∂μ) - (∫ x in {x | c x≤R},F x ∂μ)‖ ≤
      ‖F‖ * (1 - ∫ x in {x | c x≤R},(1 : ℝ) ∂μ) := by
  have hs : MeasurableSet {x | c x≤R} := hc (Set.to_countable (Set.Iic R)).measurableSet
  have hi := integral_diff hs (show IntegrableOn F univ μ from by simpa using F.integrable μ) (subset_univ _)
  simp only [← compl_eq_univ_diff,setIntegral_univ] at hi
  rw [← hi]
  have hb := norm_integral_le_of_norm_le_const (μ := μ.restrict {x | c x≤R}ᶜ)
    (C := ‖F‖) (ae_of_all _ (fun x => F.norm_coe_le_norm x))
  have ht : (μ.restrict {x | c x≤R}ᶜ).real univ =
      1 - ∫ x in {x | c x≤R},(1 : ℝ) ∂μ := by
    rw [show (μ.restrict {x | c x≤R}ᶜ).real univ = μ.real {x | c x≤R}ᶜ by
      simp only [Measure.real,Measure.restrict_apply_univ]]
    rw [measureReal_compl hs]
    simp
  simpa only [ht] using hb

/-- No mass can escape through the natural-number labels when every stratum
converges to the corresponding stratum of a probability limit. -/
theorem weakLaw_of_countable_restrictions
    (μ : ℕ → Measure E) [∀ n,IsProbabilityMeasure (μ n)]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (cN : ℕ → E → ℕ) (c : E → ℕ)
    (hcN : ∀ n,Measurable (cN n)) (hc : Measurable c)
    (hstrata : ∀ m : ℕ,External.WeakLawConverges
      (fun n => (μ n).restrict {x | cN n x=m}) (ν.restrict {x | c x=m})) :
    External.WeakLawConverges μ ν := by
  intro F
  have hfinite (G : BoundedContinuousFunction E ℝ) (R : ℕ) :
      Tendsto (fun n => ∫ x in {x | cN n x≤R},G x ∂μ n) atTop
        (𝓝 (∫ x in {x | c x≤R},G x ∂ν)) := by
    simp_rw [integral_count_le_eq_sum _ _ (hcN _) G R,
      integral_count_le_eq_sum ν c hc G R]
    exact tendsto_finset_sum _ (fun m hm => hstrata m G)
  let one : BoundedContinuousFunction E ℝ := BoundedContinuousFunction.const E 1
  have htail : Tendsto (fun R => 1 - ∫ x in {x | c x≤R},(1 : ℝ) ∂ν) atTop (𝓝 0) := by
    have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
      (tendsto_integral_count_le ν c hc one)
    simpa only [one,BoundedContinuousFunction.const_apply,integral_const,measureReal_univ_eq_one,smul_eq_mul,mul_one,sub_self] using ht
  apply tendsto_of_metric_truncations (fun n => ∫ x,F x ∂μ n)
    (fun R n => ∫ x in {x | cN n x≤R},F x ∂μ n)
    (fun R => ∫ x in {x | c x≤R},F x ∂ν) (∫ x,F x ∂ν)
    (hfinite F)
  · intro ε hε
    have hden : 0 < ‖F‖+1 := by positivity
    have ht := (tendsto_order.mp htail).2 (ε/(2*(‖F‖+1))) (by positivity)
    obtain ⟨R0,hR0⟩ := eventually_atTop.mp ht
    refine ⟨R0,fun R hR => ?_⟩
    have hn : Tendsto (fun n => 1 - ∫ x in {x | cN n x≤R},(1 : ℝ) ∂μ n) atTop
        (𝓝 (1 - ∫ x in {x | c x≤R},(1 : ℝ) ∂ν)) := by
      simpa only [one,BoundedContinuousFunction.const_apply] using tendsto_const_nhds.sub (hfinite one R)
    have hlimit : 1 - ∫ x in {x | c x≤R},(1 : ℝ) ∂ν < ε/(‖F‖+1) :=
      (hR0 R hR).trans (div_lt_div_of_pos_left hε hden (by linarith))
    filter_upwards [(tendsto_order.mp hn).2 (ε/(‖F‖+1)) hlimit] with n hn
    rw [Real.dist_eq]
    have hb := norm_integral_sub_count_le_le (μ n) (cN n) (hcN n) F R
    have hmul : (ε/(‖F‖+1)) * (‖F‖+1) = ε := div_mul_cancel₀ _ hden.ne'
    have htpos : 0 ≤ ε/(‖F‖+1) := by positivity
    have hbound : ‖F‖ * (1 - ∫ x in {x | cN n x≤R},(1 : ℝ) ∂μ n) ≤ ε := by
      nlinarith [norm_nonneg F]
    exact hb.trans hbound
  · exact tendsto_integral_count_le ν c hc F

end GeneralizedBulk.Analysis
