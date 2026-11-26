import GaussianWave.MatchedCells

/-!
# Weak convergence and fourth moments imply actual Wasserstein convergence

The transport step is constructive: a tight compact set is covered by finitely
many disjoint continuity cells; each cell contributes a normalized product of
the smaller matching mass; the residual is coupled by another product.
Portmanteau controls the residual mass. Fourth moments turn the resulting
near-diagonal probability estimates into vanishing Euclidean quadratic cost.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal

namespace GaussianWave

/-- Two weakly convergent probability sequences with the same limit have
actual near-diagonal couplings at every prescribed fixed metric accuracy. -/
theorem eventually_exists_near_metric_coupling_of_common_weak_limit
    {E : Type*} [MetricSpace E] [CompleteSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E] [HasOuterApproxClosed E]
    (μ ν : ℕ → Measure E) (ρ : Measure E)
    [∀ n, IsProbabilityMeasure (μ n)] [∀ n, IsProbabilityMeasure (ν n)]
    [IsProbabilityMeasure ρ]
    (hμ : WeakLawConverges μ ρ) (hν : WeakLawConverges ν ρ)
    (δ η : ℝ) (hδ : 0 < δ) (hη : 0 < η) :
    ∀ᶠ n in atTop, ∃ γ : Coupling (μ n) (ν n),
      γ.measure.real {z | δ < dist z.1 z.2} < η := by
  have htight : IsTightMeasureSet ({ρ} : Set (Measure E)) := isTightMeasureSet_singleton
  obtain ⟨K, hK, hKmass⟩ :=
    IsTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp htight
      (ENNReal.ofReal (η / 2)) (ENNReal.ofReal_pos.mpr (by positivity))
  have hKmass' : ρ.real Kᶜ ≤ η / 2 := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hKmass ρ (mem_singleton ρ))
    simpa only [measureReal_def, ENNReal.toReal_ofReal (by positivity : 0 ≤ η / 2)] using h
  obtain ⟨m, P, hP, hdisjoint, hcover, hfrontier, hdiam⟩ :=
    exists_finite_continuity_partition ρ K hK δ hδ
  have hres : 1 - ∑ i, (ρ (P i)).toReal = ρ.real (⋃ i, P i)ᶜ := by
    rw [measureReal_compl (MeasurableSet.iUnion hP), measureReal_univ_eq_one,
      measureReal_iUnion_fintype hdisjoint hP]
    rfl
  have hres_bound : 1 - ∑ i, (ρ (P i)).toReal ≤ η / 2 := by
    rw [hres]
    exact (measureReal_mono (compl_subset_compl.mpr hcover)).trans hKmass'
  have hconv := matchedResidual_real_mass_tendsto_two μ ν ρ hμ hν P hP hdisjoint hfrontier
  have hevent := (tendsto_order.mp hconv).2 η (by linarith)
  filter_upwards [hevent] with n hn
  refine ⟨matchedCellCoupling (μ n) (ν n) P hP hdisjoint, ?_⟩
  have hb := matchedCellCoupling_dist_bad_real_le (μ n) (ν n) P hP hdisjoint δ hdiam
  rw [← matchedResidual_real_mass (μ n) (ν n) P hP hdisjoint] at hb
  exact hb.trans_lt hn

/-- The small-diameter construction yields the physical Euclidean cost
accuracy required by the transport moment theorem, including dimension zero. -/
theorem arbitrarilyNearCouplingsTwo_of_common_weak_limit
    {ι : Type*} [Fintype ι]
    (μ ν : ℕ → Measure (ι → ℝ)) (ρ : Measure (ι → ℝ))
    [∀ n, IsProbabilityMeasure (μ n)] [∀ n, IsProbabilityMeasure (ν n)]
    [IsProbabilityMeasure ρ]
    (hμ : WeakLawConverges μ ρ) (hν : WeakLawConverges ν ρ) :
    ArbitrarilyNearCouplingsTwo μ ν := by
  intro ε hε η hη
  let m := (Fintype.card ι : ℝ)
  let δ := min 1 (ε / (2 * (m + 1)))
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ ≤ ε / (2 * (m + 1)) := min_le_right _ _
  have hcost : m * δ ^ 2 < ε := by
    have hmul : δ * (2 * (m + 1)) ≤ ε := (le_div_iff₀ (by positivity)).mp hδε
    have hs : δ ^ 2 ≤ δ := by nlinarith
    nlinarith [mul_nonneg hm (sub_nonneg.mpr hs)]
  filter_upwards [eventually_exists_near_metric_coupling_of_common_weak_limit
    μ ν ρ hμ hν δ η hδ hη] with n hn
  obtain ⟨γ, hγ⟩ := hn
  refine ⟨γ, lt_of_le_of_lt ?_ hγ⟩
  apply measureReal_mono ?_ (measure_ne_top γ.measure _)
  intro z hz
  by_contra hnot
  have hd : dist z.1 z.2 ≤ δ := le_of_not_gt hnot
  have hsq : dist z.1 z.2 ^ 2 ≤ δ ^ 2 :=
    pow_le_pow_left₀ dist_nonneg hd 2
  have hb := (squareTransportCost_le_card_mul_dist_sq z.1 z.2).trans
    (mul_le_mul_of_nonneg_left hsq hm)
  exact (not_lt_of_ge (hb.trans hcost.le)) hz

/-- Full transport upgrade for two varying laws; both may have singular
supports, and the covariance is allowed to vary with the index. -/
theorem wassersteinTwoSquared_tendsto_zero_of_common_weak_limit
    {ι : Type*} [Fintype ι]
    (μ ν : ℕ → Measure (ι → ℝ)) (ρ : Measure (ι → ℝ))
    [∀ n, IsProbabilityMeasure (μ n)] [∀ n, IsProbabilityMeasure (ν n)]
    [IsProbabilityMeasure ρ]
    (hweakμ : WeakLawConverges μ ρ) (hweakν : WeakLawConverges ν ρ)
    (hμ : ∀ n, Integrable (fun x => squareMass x ^ 2) (μ n))
    (hν : ∀ n, Integrable (fun x => squareMass x ^ 2) (ν n))
    (M L : ℝ)
    (hM : ∀ n, (∫ x, squareMass x ^ 2 ∂μ n) ≤ M)
    (hL : ∀ n, (∫ x, squareMass x ^ 2 ∂ν n) ≤ L) :
    Tendsto (fun n => wassersteinTwoSquared (μ n) (ν n)) atTop (𝓝 0) :=
  wassersteinTwoSquared_tendsto_zero_of_arbitrarily_near_couplings_two
    (arbitrarilyNearCouplingsTwo_of_common_weak_limit μ ν ρ hweakμ hweakν)
    hμ hν M L hM hL

theorem wassersteinTwo_tendsto_zero_of_common_weak_limit
    {ι : Type*} [Fintype ι]
    (μ ν : ℕ → Measure (ι → ℝ)) (ρ : Measure (ι → ℝ))
    [∀ n, IsProbabilityMeasure (μ n)] [∀ n, IsProbabilityMeasure (ν n)]
    [IsProbabilityMeasure ρ]
    (hweakμ : WeakLawConverges μ ρ) (hweakν : WeakLawConverges ν ρ)
    (hμ : ∀ n, Integrable (fun x => squareMass x ^ 2) (μ n))
    (hν : ∀ n, Integrable (fun x => squareMass x ^ 2) (ν n))
    (M L : ℝ)
    (hM : ∀ n, (∫ x, squareMass x ^ 2 ∂μ n) ≤ M)
    (hL : ∀ n, (∫ x, squareMass x ^ 2 ∂ν n) ≤ L) :
    Tendsto (fun n => wassersteinTwo (μ n) (ν n)) atTop (𝓝 0) :=
  wassersteinTwo_tendsto_zero_of_squared_two
    (wassersteinTwoSquared_tendsto_zero_of_common_weak_limit μ ν ρ hweakμ hweakν hμ hν M L hM hL)

end GaussianWave

namespace GaussianWave

/-- The weak-convergence theorem also supplies actual coupling witnesses
whose physical quadratic costs tend to zero. -/
theorem exists_couplings_cost_tendsto_zero_of_common_weak_limit
    {ι : Type*} [Fintype ι]
    (μ ν : ℕ → Measure (ι → ℝ)) (ρ : Measure (ι → ℝ))
    [∀ n, IsProbabilityMeasure (μ n)] [∀ n, IsProbabilityMeasure (ν n)]
    [IsProbabilityMeasure ρ]
    (hweakμ : WeakLawConverges μ ρ) (hweakν : WeakLawConverges ν ρ)
    (hμ : ∀ n, Integrable (fun x => squareMass x ^ 2) (μ n))
    (hν : ∀ n, Integrable (fun x => squareMass x ^ 2) (ν n))
    (M L : ℝ)
    (hM : ∀ n, (∫ x, squareMass x ^ 2 ∂μ n) ≤ M)
    (hL : ∀ n, (∫ x, squareMass x ^ 2 ∂ν n) ≤ L) :
    ∃ γ : ∀ n, Coupling (μ n) (ν n),
      Tendsto (fun n => quadraticCouplingCost (γ n)) atTop (𝓝 0) :=
  exists_couplings_cost_tendsto_zero_of_wasserstein_two μ ν hμ hν
    (wassersteinTwoSquared_tendsto_zero_of_common_weak_limit μ ν ρ hweakμ hweakν hμ hν M L hM hL)

end GaussianWave
