import GeneralizedBulk.Analysis.StratumMoments

/-! Exact conditional kernels through a countable mixture of marked strata. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace GeneralizedBulk.Analysis
variable {E I B Y G : Type*} [MeasurableSpace E] [MeasurableSpace I]
variable [Countable I] [MeasurableSingletonClass I]
variable [MeasurableSpace B] [MeasurableSpace Y] [MeasurableSpace G]
variable (ν : Measure E) [IsProbabilityMeasure ν] (c : E → I) (hc : Measurable c)
variable (T : ActiveStratum ν c → Type*) [∀ i, MeasurableSpace (T i)]
variable (Q : ∀ i, Measure (T i)) [∀ i, IsProbabilityMeasure (Q i)]

/-- A pointwise equality of the genuine mark kernels gives equality of the
restricted joint laws. No measurable choice of a mark relabeling is needed. -/
theorem stratum_joint_kernel_law
    (R : Measure Y) [IsProbabilityMeasure R] (S : Set E) (hS : MeasurableSet S)
    (f : E → B) (hf : Measurable f)
    (H : StratumSample ν c T → G) (hH : Measurable H)
    (K : E × Y → G) (hK : Measurable K)
    (hkernel : ∀ i (s : stratumSet c i.val), s.val ∈ S →
      Measure.map (fun y : T i => H ⟨i,(s,y)⟩) (Q i) =
        Measure.map (fun y => K (s.val,y)) R) :
    Measure.map (fun z => (f (stratumSampleValue ν c T z),H z))
      ((stratumMarkedLaw ν c hc T Q).restrict (stratumSampleValue ν c T ⁻¹' S)) =
    Measure.map (fun z : E × Y => (f z.1,K z)) ((ν.restrict S).prod R) := by
  let value := stratumSampleValue ν c T
  have hvalue : Measurable value := measurable_stratumSampleValue ν c T
  have hjoint : Measurable (fun z => (f (value z),H z)) := (hf.comp hvalue).prodMk hH
  have hjointK : Measurable (fun z : E × Y => (f z.1,K z)) := (hf.comp measurable_fst).prodMk hK
  ext A hA
  rw [Measure.map_apply hjoint hA,Measure.map_apply hjointK hA]
  let g : StratumSample ν c T → ℝ≥0∞ :=
    (value ⁻¹' S).indicator (fun z => A.indicator (fun _ => 1) (f (value z),H z))
  let k : E → ℝ≥0∞ := fun s => S.indicator
    (fun s => MeasureTheory.lintegral R (fun y : Y => A.indicator (fun _ => (1 : ℝ≥0∞)) (f s,K (s,y)))) s
  have hg : Measurable g := (measurable_const.indicator hA |>.comp hjoint).indicator (hvalue hS)
  have hk0 : Measurable (fun z : E × Y => A.indicator (fun _ => (1 : ℝ≥0∞)) (f z.1,K z)) :=
    (measurable_const.indicator hA).comp hjointK
  have hk : Measurable k := (hk0.lintegral_prod_right' (ν := R)).indicator hS
  have heq : (∫⁻ z, g z ∂stratumMarkedLaw ν c hc T Q) =
      ∫⁻ z, k (value z) ∂stratumMarkedLaw ν c hc T Q := by
    rw [lintegral_stratumMarkedLaw ν c hc T Q g hg,
      lintegral_stratumMarkedLaw ν c hc T Q (fun z => k (value z)) (hk.comp hvalue)]
    apply tsum_congr
    intro i
    congr 1
    rw [lintegral_prod (fun z => g ⟨i,z⟩) ((hg.comp (measurable_sigma_mk i)).aemeasurable),
      lintegral_prod (fun z => k (value ⟨i,z⟩)) (((hk.comp hvalue).comp (measurable_sigma_mk i)).aemeasurable)]
    apply lintegral_congr
    intro s
    by_cases hs : s.val ∈ S
    · have hHi : Measurable (fun y : T i => H ⟨i,(s,y)⟩) :=
        hH.comp ((measurable_sigma_mk i).comp (measurable_const.prodMk measurable_id))
      have hKi : Measurable (fun y => K (s.val,y)) := hK.comp (measurable_const.prodMk measurable_id)
      have htest : Measurable (fun x : G => A.indicator (fun _ => (1 : ℝ≥0∞)) (f s.val,x)) :=
        (measurable_const.indicator hA).comp (measurable_const.prodMk measurable_id)
      have hh := congrArg (fun μ : Measure G => ∫⁻ x, A.indicator (fun _ => (1 : ℝ≥0∞)) (f s.val,x) ∂μ)
        (hkernel i s hs)
      dsimp only at hh
      rw [lintegral_map htest hHi,lintegral_map htest hKi] at hh
      have hgs (y : T i) : g ⟨i,(s,y)⟩ =
          A.indicator (fun _ => (1 : ℝ≥0∞)) (f s.val,H ⟨i,(s,y)⟩) :=
        Set.indicator_of_mem (show ⟨i,(s,y)⟩ ∈ value ⁻¹' S from hs) _
      have hks : k s.val = ∫⁻ y, A.indicator (fun _ => (1 : ℝ≥0∞)) (f s.val,K (s.val,y)) ∂ R :=
        Set.indicator_of_mem hs _
      change (∫⁻ y, g ⟨i,(s,y)⟩ ∂Q i) = ∫⁻ _ : T i, k s.val ∂Q i
      simp_rw [hgs,hks]
      simpa only [lintegral_const,measure_univ,mul_one] using hh
    · simp [g,k,value,stratumSampleValue,hs]
  have hmap : (∫⁻ z, k (value z) ∂stratumMarkedLaw ν c hc T Q) = ∫⁻ s, k s ∂ν := by
    calc
      _ = ∫⁻ s, k s ∂Measure.map value (stratumMarkedLaw ν c hc T Q) := (lintegral_map hk hvalue).symm
      _ = _ := congrArg (fun μ : Measure E => ∫⁻ s, k s ∂μ)
        (stratumMarkedLaw_value_marginal ν c hc T Q)
  have hleft : (stratumMarkedLaw ν c hc T Q).restrict (value ⁻¹' S)
      ((fun z => (f (value z),H z)) ⁻¹' A) = ∫⁻ z, g z ∂stratumMarkedLaw ν c hc T Q := by
    rw [← lintegral_indicator_one (hjoint hA),← lintegral_indicator (hvalue hS)]
    rfl
  have hright : (ν.restrict S).prod R ((fun z : E × Y => (f z.1,K z)) ⁻¹' A) = ∫⁻ s, k s ∂ν := by
    rw [← lintegral_indicator_one (hjointK hA)]
    change (∫⁻ z : E × Y, A.indicator (fun _ => (1 : ℝ≥0∞)) (f z.1,K z) ∂(ν.restrict S).prod R) = _
    rw [lintegral_prod _ (hk0.aemeasurable),← lintegral_indicator hS]
  exact hleft.trans ((heq.trans hmap).trans hright.symm)

end GeneralizedBulk.Analysis
