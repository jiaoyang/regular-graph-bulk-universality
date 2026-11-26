import GeneralizedBulk.Analysis.CountableStrata

/-! Common almost-sure analytic events pass through the actual countable
mixture even when they quantify over all spectral parameters. -/
noncomputable section
open MeasureTheory
namespace GeneralizedBulk.Analysis

theorem measurableEmbedding_sigma_mk {I : Type*} {S : I → Type*}
    [∀ i,MeasurableSpace (S i)] (i : I) : MeasurableEmbedding (Sigma.mk i : S i → Sigma S) := by
  classical
  refine ⟨fun x y h => by cases h; rfl,measurable_sigma_mk i,?_⟩
  intro s hs
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro j
  change MeasurableSet ((Sigma.mk j) ⁻¹' (Sigma.mk i '' s))
  by_cases hij : j=i
  · subst j
    have he : (Sigma.mk i) ⁻¹' (Sigma.mk i '' s) = s :=
      Set.preimage_image_eq _ (fun x y h => by cases h; rfl)
    simpa only [he] using hs
  · have he : (Sigma.mk j) ⁻¹' (Sigma.mk i '' s) = ∅ := by
      apply Set.eq_empty_iff_forall_not_mem.mpr
      intro x hx
      rcases hx with ⟨y,hy,hxy⟩
      exact hij (congrArg Sigma.fst hxy).symm
    rw [he]
    exact MeasurableSet.empty

theorem ae_stratumMarkedLaw_of_fibers
    {E I : Type*} [MeasurableSpace E] [MeasurableSpace I] [Countable I]
    [MeasurableSingletonClass I]
    (ν : Measure E) [IsProbabilityMeasure ν] (c : E → I) (hc : Measurable c)
    (T : ActiveStratum ν c → Type*) [∀ i,MeasurableSpace (T i)] (Q : ∀ i,Measure (T i))
    (p : StratumSample ν c T → Prop)
    (hf : ∀ i,∀ᵐ z ∂(stratumProbability ν c hc i : Measure (stratumSet c i.val)).prod (Q i),p ⟨i,z⟩) :
    ∀ᵐ z ∂stratumMarkedLaw ν c hc T Q,p z := by
  letI : Countable (ActiveStratum ν c) := inferInstanceAs (Countable {i : I // ν (stratumSet c i) ≠ 0})
  rw [stratumMarkedLaw,Measure.ae_sum_iff]
  intro i
  apply Measure.ae_smul_measure
  exact (measurableEmbedding_sigma_mk i).ae_map_iff.mpr (hf i)

end GeneralizedBulk.Analysis
