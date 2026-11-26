import GaussianWave.Transport
import GaussianWave.ContinuityPartition

/-!
# Actual matched-cell couplings

Each measurable partition cell contributes the smaller of its two masses.
Restricted measures are scaled down to that common mass and coupled by an
actual normalized product. The unused submeasures are coupled independently.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal Function

namespace GaussianWave

variable {E ι : Type*} [MeasurableSpace E]

/-- The portion of `μ` in `A` that can be matched with the mass of `ν` in `A`. -/
def matchedPart (μ ν : Measure E) (A : Set E) : Measure E :=
  (min (μ A) (ν A) / μ A) • μ.restrict A

theorem matchedPart_le_restrict (μ ν : Measure E) [IsFiniteMeasure μ]
    (A : Set E) : matchedPart μ ν A ≤ μ.restrict A := by
  by_cases hzero : μ A = 0
  · simp [matchedPart, hzero]
    exact (μ.restrict A).zero_le
  have hcoeff : min (μ A) (ν A) / μ A ≤ 1 := by
    apply (ENNReal.div_le_iff hzero (measure_ne_top μ A)).mpr
    simp [min_le_left (μ A) (ν A)]
  apply Measure.le_iff.mpr
  intro S hS
  rw [matchedPart, Measure.smul_apply, smul_eq_mul]
  exact (mul_le_mul_right' hcoeff _).trans_eq (one_mul _)

theorem matchedPart_le (μ ν : Measure E) [IsFiniteMeasure μ]
    (A : Set E) : matchedPart μ ν A ≤ μ :=
  (matchedPart_le_restrict μ ν A).trans Measure.restrict_le_self

instance matchedPart_isFinite (μ ν : Measure E) [IsFiniteMeasure μ] (A : Set E) :
    IsFiniteMeasure (matchedPart μ ν A) :=
  isFiniteMeasure_of_le μ (matchedPart_le μ ν A)

theorem matchedPart_mass (μ ν : Measure E) [IsFiniteMeasure μ] (A : Set E) :
    matchedPart μ ν A univ = min (μ A) (ν A) := by
  rw [matchedPart, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
  apply ENNReal.div_mul_cancel'
  · intro h
    simp [h]
  · intro h
    exact False.elim ((measure_ne_top μ A) h)

theorem sum_matchedPart_le [Fintype ι]
    (μ ν : Measure E) [IsFiniteMeasure μ] (P : ι → Set E)
    (hP : ∀ i, MeasurableSet (P i))
    (hdisjoint : Pairwise (Disjoint on P)) :
    (∑ i, matchedPart μ ν (P i)) ≤ μ := by
  calc
    _ ≤ ∑ i, μ.restrict (P i) := by
      apply Measure.le_iff.mpr
      intro S hS
      simp only [Measure.coe_finset_sum, Finset.sum_apply]
      exact Finset.sum_le_sum fun i _ => matchedPart_le_restrict μ ν (P i) S
    _ = μ.restrict (⋃ i, P i) := by
      rw [Measure.restrict_iUnion hdisjoint hP, Measure.sum_fintype]
    _ ≤ μ := Measure.restrict_le_self

/-- `none` is the unmatched residual; `some i` is the matched mass in cell `i`. -/
def matchedComponents [Fintype ι] (μ ν : Measure E) (P : ι → Set E) :
    Option ι → Measure E
  | none => μ - ∑ i, matchedPart μ ν (P i)
  | some i => matchedPart μ ν (P i)

instance matchedComponents_isFinite [Fintype ι]
    (μ ν : Measure E) [IsFiniteMeasure μ] (P : ι → Set E) (i : Option ι) :
    IsFiniteMeasure (matchedComponents μ ν P i) := by
  cases i <;> unfold matchedComponents <;> infer_instance

theorem sum_matchedComponents [Fintype ι]
    (μ ν : Measure E) [IsFiniteMeasure μ] (P : ι → Set E)
    (hP : ∀ i, MeasurableSet (P i)) (hdisjoint : Pairwise (Disjoint on P)) :
    (∑ i, matchedComponents μ ν P i) = μ := by
  rw [Fintype.sum_option]
  exact Measure.sub_add_cancel_of_le (sum_matchedPart_le μ ν P hP hdisjoint)

theorem matchedComponents_mass_eq [Fintype ι]
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (P : ι → Set E) (hP : ∀ i, MeasurableSet (P i))
    (hdisjoint : Pairwise (Disjoint on P)) (i : Option ι) :
    matchedComponents μ ν P i univ = matchedComponents ν μ P i univ := by
  cases i with
  | some i => simp only [matchedComponents, matchedPart_mass, min_comm]
  | none =>
    simp only [matchedComponents]
    rw [Measure.sub_apply MeasurableSet.univ (sum_matchedPart_le μ ν P hP hdisjoint),
      Measure.sub_apply MeasurableSet.univ (sum_matchedPart_le ν μ P hP hdisjoint)]
    simp [Measure.coe_finset_sum, Finset.sum_apply, matchedPart_mass, min_comm]

/-- The genuine finite-cell matched coupling, including its residual. -/
def matchedCellCoupling [Fintype ι]
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (P : ι → Set E) (hP : ∀ i, MeasurableSet (P i))
    (hdisjoint : Pairwise (Disjoint on P)) : Coupling μ ν :=
  couplingOfComponents μ ν (matchedComponents μ ν P) (matchedComponents ν μ P)
    (matchedComponents_mass_eq μ ν P hP hdisjoint)
    (sum_matchedComponents μ ν P hP hdisjoint)
    (sum_matchedComponents ν μ P hP hdisjoint)

theorem matchedResidual_mass [Fintype ι]
    (μ ν : Measure E) [IsProbabilityMeasure μ]
    (P : ι → Set E) (hP : ∀ i, MeasurableSet (P i))
    (hdisjoint : Pairwise (Disjoint on P)) :
    matchedComponents μ ν P none univ = 1 - ∑ i, min (μ (P i)) (ν (P i)) := by
  rw [matchedComponents, Measure.sub_apply MeasurableSet.univ
    (sum_matchedPart_le μ ν P hP hdisjoint)]
  simp [Measure.coe_finset_sum, Finset.sum_apply, matchedPart_mass]

theorem normalizedProduct_mass (α β : Measure E)
    [IsFiniteMeasure α] [IsFiniteMeasure β]
    (hmass : α univ = β univ) : normalizedProduct α β univ = α univ := by
  have h := congrArg (fun m : Measure E => m univ) (normalizedProduct_fst α β hmass)
  simpa only [Measure.map_apply measurable_fst MeasurableSet.univ,
    Set.preimage_univ] using h

theorem matchedPart_compl (μ ν : Measure E) (A : Set E) (hA : MeasurableSet A) :
    matchedPart μ ν A Aᶜ = 0 := by
  simp [matchedPart, Measure.smul_apply, Measure.restrict_apply hA.compl]

theorem normalizedProduct_zero_off_cell
    (α β : Measure E) [IsFiniteMeasure α] [IsFiniteMeasure β]
    (A : Set E) (hα : α Aᶜ = 0) (hβ : β Aᶜ = 0) :
    normalizedProduct α β (A ×ˢ A)ᶜ = 0 := by
  have hp : α.prod β (A ×ˢ A)ᶜ = 0 := by
    rw [Set.compl_prod_eq_union]
    apply measure_union_null <;> simp [Measure.prod_prod, hα, hβ]
  rw [normalizedProduct, Measure.smul_apply, hp, smul_zero]

/-- All the mass of a matched-cell component stays in its cell square. -/
theorem matchedProduct_zero_off_cell (μ ν : Measure E)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (A : Set E) (hA : MeasurableSet A) :
    normalizedProduct (matchedPart μ ν A) (matchedPart ν μ A) (A ×ˢ A)ᶜ = 0 :=
  normalizedProduct_zero_off_cell _ _ A (matchedPart_compl μ ν A hA)
    (matchedPart_compl ν μ A hA)

/-- A set avoiding every cell square can carry only unmatched residual mass. -/
theorem matchedCellCoupling_bad_le [Fintype ι]
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (P : ι → Set E) (hP : ∀ i, MeasurableSet (P i))
    (hdisjoint : Pairwise (Disjoint on P)) (A : Set (E × E))
    (hA : ∀ i, A ⊆ (P i ×ˢ P i)ᶜ) :
    (matchedCellCoupling μ ν P hP hdisjoint).measure A ≤
      1 - ∑ i, min (μ (P i)) (ν (P i)) := by
  have hzero (i : ι) :
      normalizedProduct (matchedPart μ ν (P i)) (matchedPart ν μ (P i)) A = 0 :=
    measure_mono_null (hA i) (matchedProduct_zero_off_cell μ ν (P i) (hP i))
  change (∑ i, normalizedProduct (matchedComponents μ ν P i)
    (matchedComponents ν μ P i)) A ≤ _
  rw [Measure.coe_finset_sum, Finset.sum_apply, Fintype.sum_option]
  simp only [matchedComponents, hzero, Finset.sum_const_zero, add_zero]
  calc
    normalizedProduct (μ - ∑ i, matchedPart μ ν (P i))
        (ν - ∑ i, matchedPart ν μ (P i)) A ≤
        normalizedProduct (μ - ∑ i, matchedPart μ ν (P i))
          (ν - ∑ i, matchedPart ν μ (P i)) univ := measure_mono (subset_univ A)
    _ = matchedComponents μ ν P none univ := normalizedProduct_mass _ _
      (matchedComponents_mass_eq μ ν P hP hdisjoint none)
    _ = _ := matchedResidual_mass μ ν P hP hdisjoint

/-- Small cell diameter gives a quantitative near-diagonal bound for the
actual coupling, with no desired coupling property as a hypothesis. -/
theorem matchedCellCoupling_dist_bad_le [Fintype ι]
    [PseudoMetricSpace E] (μ ν : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (P : ι → Set E) (hP : ∀ i, MeasurableSet (P i))
    (hdisjoint : Pairwise (Disjoint on P)) (δ : ℝ)
    (hdiam : ∀ i, ∀ x ∈ P i, ∀ y ∈ P i, dist x y ≤ δ) :
    (matchedCellCoupling μ ν P hP hdisjoint).measure {z | δ < dist z.1 z.2} ≤
      1 - ∑ i, min (μ (P i)) (ν (P i)) := by
  apply matchedCellCoupling_bad_le μ ν P hP hdisjoint
  intro i z hz hcell
  exact (not_lt_of_ge (hdiam i z.1 hcell.1 z.2 hcell.2)) hz

theorem matchedResidual_real_mass [Fintype ι]
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsFiniteMeasure ν]
    (P : ι → Set E) (hP : ∀ i, MeasurableSet (P i))
    (hdisjoint : Pairwise (Disjoint on P)) :
    (matchedComponents μ ν P none univ).toReal =
      1 - ∑ i, min (μ (P i)).toReal (ν (P i)).toReal := by
  have hsum : (∑ i, min (μ (P i)) (ν (P i))) ≤ 1 := by
    have h := sum_matchedPart_le μ ν P hP hdisjoint univ
    simpa only [Measure.coe_finset_sum, Finset.sum_apply, matchedPart_mass, measure_univ] using h
  rw [matchedResidual_mass μ ν P hP hdisjoint,
    ENNReal.toReal_sub_of_le hsum ENNReal.one_ne_top, ENNReal.toReal_one]
  congr 1
  rw [ENNReal.toReal_sum (fun i _ => ne_of_lt
    ((min_le_left _ _).trans_lt (measure_lt_top μ (P i))))]
  apply Finset.sum_congr rfl
  intro i _
  exact ENNReal.toReal_min (measure_ne_top μ (P i)) (measure_ne_top ν (P i))

theorem matchedCellCoupling_dist_bad_real_le [Fintype ι]
    [PseudoMetricSpace E] (μ ν : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (P : ι → Set E) (hP : ∀ i, MeasurableSet (P i))
    (hdisjoint : Pairwise (Disjoint on P)) (δ : ℝ)
    (hdiam : ∀ i, ∀ x ∈ P i, ∀ y ∈ P i, dist x y ≤ δ) :
    ((matchedCellCoupling μ ν P hP hdisjoint).measure {z | δ < dist z.1 z.2}).toReal ≤
      1 - ∑ i, min (μ (P i)).toReal (ν (P i)).toReal := by
  have h := matchedCellCoupling_dist_bad_le μ ν P hP hdisjoint δ hdiam
  rw [← matchedResidual_mass μ ν P hP hdisjoint] at h
  have hr := ENNReal.toReal_mono (measure_ne_top (matchedComponents μ ν P none) univ) h
  rwa [matchedResidual_real_mass μ ν P hP hdisjoint] at hr

end GaussianWave

namespace GaussianWave

/-- Portmanteau gives convergence of the actual matching residual for any
fixed finite continuity partition. -/
theorem matchedResidual_real_mass_tendsto
    {E ι : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [HasOuterApproxClosed E] [Fintype ι]
    (μ : ℕ → Measure E) (ν : Measure E)
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    (hweak : WeakLawConverges μ ν) (P : ι → Set E)
    (hP : ∀ i, MeasurableSet (P i)) (hdisjoint : Pairwise (Disjoint on P))
    (hfrontier : ∀ i, ν (frontier (P i)) = 0) :
    Tendsto (fun n => (matchedComponents (μ n) ν P none univ).toReal) atTop
      (𝓝 (1 - ∑ i, (ν (P i)).toReal)) := by
  simp_rw [matchedResidual_real_mass _ _ P hP hdisjoint]
  apply tendsto_const_nhds.sub
  apply tendsto_finset_sum
  intro i _
  simpa only [min_self] using
    (weakLawConverges_cell_real_mass μ ν hweak (P i) (hfrontier i)).min
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (ν (P i)).toReal) atTop
        (𝓝 ((ν (P i)).toReal)))

/-- Both marginals may vary, provided they converge weakly to the same law. -/
theorem matchedResidual_real_mass_tendsto_two
    {E ι : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [HasOuterApproxClosed E] [Fintype ι]
    (μ ν : ℕ → Measure E) (ρ : Measure E)
    [∀ n, IsProbabilityMeasure (μ n)] [∀ n, IsProbabilityMeasure (ν n)]
    [IsProbabilityMeasure ρ]
    (hweakμ : WeakLawConverges μ ρ) (hweakν : WeakLawConverges ν ρ)
    (P : ι → Set E) (hP : ∀ i, MeasurableSet (P i))
    (hdisjoint : Pairwise (Disjoint on P))
    (hfrontier : ∀ i, ρ (frontier (P i)) = 0) :
    Tendsto (fun n => (matchedComponents (μ n) (ν n) P none univ).toReal) atTop
      (𝓝 (1 - ∑ i, (ρ (P i)).toReal)) := by
  simp_rw [matchedResidual_real_mass _ _ P hP hdisjoint]
  apply tendsto_const_nhds.sub
  apply tendsto_finset_sum
  intro i _
  simpa only [min_self] using
    (weakLawConverges_cell_real_mass μ ρ hweakμ (P i) (hfrontier i)).min
      (weakLawConverges_cell_real_mass ν ρ hweakν (P i) (hfrontier i))

/-- The limiting residual is the mass outside the cell union. -/
theorem residualLimit_eq_compl_mass
    {E ι : Type*} [MeasurableSpace E] [Fintype ι]
    (ν : Measure E) [IsProbabilityMeasure ν] (P : ι → Set E)
    (hP : ∀ i, MeasurableSet (P i)) (hdisjoint : Pairwise (Disjoint on P)) :
    1 - ∑ i, (ν (P i)).toReal = ν.real (⋃ i, P i)ᶜ := by
  rw [measureReal_compl (MeasurableSet.iUnion hP), measureReal_univ_eq_one]
  congr 1
  exact (measureReal_iUnion_fintype hdisjoint hP).symm

/-- Covering a compact set bounds the limiting residual by its outside mass. -/
theorem residualLimit_le_compact_compl
    {E ι : Type*} [MeasurableSpace E] [Fintype ι]
    (ν : Measure E) [IsProbabilityMeasure ν] (P : ι → Set E)
    (hP : ∀ i, MeasurableSet (P i)) (hdisjoint : Pairwise (Disjoint on P))
    (K : Set E) (hcover : K ⊆ ⋃ i, P i) :
    1 - ∑ i, (ν (P i)).toReal ≤ ν.real Kᶜ := by
  rw [residualLimit_eq_compl_mass ν P hP hdisjoint]
  exact measureReal_mono (compl_subset_compl.mpr hcover)

end GaussianWave
