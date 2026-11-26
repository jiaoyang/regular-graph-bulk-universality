import GeneralizedBulk.Graph.WindowMarkLaw

/-! The zero-count window stratum requires no BS theorem: its mark space is
a singleton and its convergence is entirely scalar counting-state convergence. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter Set
open scoped Topology
namespace GeneralizedBulk.External.RegularSpectralData
open Graph GeneralizedBulk.Counting GeneralizedBulk.Analysis GeneralizedBulk.Gaussian
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

private theorem zeroMarkLaw_dirac (p : ℝ) : finiteMarkLaw p 0=Measure.dirac (default : (Fin 0 × Fin 4) → ℝ) := by
  apply Measure.ext
  intro A hA
  by_cases hmem : (default : (Fin 0 × Fin 4) → ℝ) ∈ A
  · have heq : A=univ := eq_univ_of_forall (fun x => by simpa only [Subsingleton.elim x default] using hmem)
    simp [heq]
  · have heq : A=∅ := eq_empty_iff_forall_not_mem.mpr (fun x hx => hmem (by simpa only [Subsingleton.elim x default] using hx))
    simp [heq]

private theorem measure_prod_zeroMark (p : ℝ)
    (μ : Measure (WindowData 0 × ((Fin 0 × Fin 4) → ℝ))) [IsFiniteMeasure μ] :
    μ=(μ.map Prod.fst).prod (finiteMarkLaw p 0) := by
  rw [zeroMarkLaw_dirac,Measure.prod_dirac,Measure.map_map measurable_prodMk_right measurable_fst]
  have heq : (fun z : WindowData 0 × ((Fin 0 × Fin 4) → ℝ) => (z.1,default))=id := by
    funext z
    exact Prod.ext rfl (Subsingleton.elim _ _)
  change μ=Measure.map (fun z : WindowData 0 × ((Fin 0 × Fin 4) → ℝ) => (z.1,default)) μ
  rw [heq,Measure.map_id]

set_option maxHeartbeats 2000000 in
theorem windowMarkLaw_zero_restrict_converges
    (P : Measure Ω) [IsProbabilityMeasure P] (hd : 0 < d)
    (E sigma center R p : ℝ) (r : ℕ → ℕ)
    (selection : ∀ n,Ω → Fin 0 → Fin (N n))
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hscalar : WeakLawConverges
      (fun n => P.map (fun ω => D.microscopicCountingState (r n) ω E sigma center)) ν)
    (hboundary : ∀ᵐ s ∂ν,s.val.1.measure {-R}=0 ∧ s.val.1.measure {R}=0) :
    WeakLawConverges
      (fun n => (D.windowMarkLaw P (r n) E sigma center R (selection (r n))).restrict
        (Prod.fst ⁻¹' {x : WindowData 0 | x.2.1=0}))
      (((ν.map (windowData 0 (-R) R)).restrict {x : WindowData 0 | x.2.1=0}).prod (finiteMarkLaw p 0)) := by
  letI : ∀ n,IsProbabilityMeasure (P.map (fun ω => D.microscopicCountingState (r n) ω E sigma center)) :=
    fun n => isProbabilityMeasure_map (D.measurable_microscopicCountingState (r n) E sigma center).aemeasurable
  let η := fun n => P.map (fun ω => windowData 0 (-R) R (D.microscopicCountingState (r n) ω E sigma center))
  let ξ := ν.map (windowData 0 (-R) R)
  letI : IsProbabilityMeasure ξ := isProbabilityMeasure_map (measurable_windowData 0 (-R) R).aemeasurable
  letI : ∀ n,IsProbabilityMeasure (η n) := fun n => isProbabilityMeasure_map
    (((measurable_windowData 0 (-R) R).comp (D.measurable_microscopicCountingState (r n) E sigma center)).aemeasurable)
  letI : ∀ n,IsProbabilityMeasure (D.windowMarkLaw P (r n) E sigma center R (selection (r n))) :=
    fun n => D.windowMarkLaw_isProbability P hd (r n) E sigma center R (selection (r n)) (fun i => Fin.elim0 i)
  let g : WindowData 0 → WindowData 0 × ((Fin 0 × Fin 4) → ℝ) := fun x => (x,default)
  have hg : Continuous g := continuous_id.prodMk continuous_const
  have hwindow : WeakLawConverges η ξ := by
    have hw := weakLaw_windowData_of_weak _ ν hscalar 0 (-R) R hboundary
    simpa only [Measure.map_map (measurable_windowData 0 (-R) R)
      (D.measurable_microscopicCountingState _ E sigma center),Function.comp_def] using hw
  have hfull (n) : D.windowMarkLaw P (r n) E sigma center R (selection (r n))=(η n).map g := by
    rw [measure_prod_zeroMark p (D.windowMarkLaw P (r n) E sigma center R (selection (r n))),D.windowMarkLaw_fst P hd _ E sigma center R _ (fun i => Fin.elim0 i),
      zeroMarkLaw_dirac,Measure.prod_dirac]
  have htarget : ξ.prod (finiteMarkLaw p 0)=ξ.map g := by rw [zeroMarkLaw_dirac,Measure.prod_dirac]
  have hweak : WeakLawConverges
      (fun n => D.windowMarkLaw P (r n) E sigma center R (selection (r n))) (ξ.prod (finiteMarkLaw p 0)) := by
    simpa only [hfull,htarget] using weakLaw_map η ξ hwindow g hg
  let B : Set (WindowData 0) := {x | x.2.1=0}
  let A : Set (WindowData 0 × ((Fin 0 × Fin 4) → ℝ)) := Prod.fst ⁻¹' B
  have hA : MeasurableSet A := (measurable_fst.comp (measurable_snd.comp measurable_fst)) (measurableSet_singleton 0)
  intro Ψ
  let T : BoundedContinuousFunction (WindowData 0 × ((Fin 0 × Fin 4) → ℝ)) ℝ :=
    (countStratumIndicator 0).compContinuous ⟨Prod.fst,continuous_fst⟩*Ψ
  have hweight (μ : Measure (WindowData 0 × ((Fin 0 × Fin 4) → ℝ))) [IsFiniteMeasure μ] :
      (∫ z,T z ∂μ)=∫ z,Ψ z ∂μ.restrict A := by
    rw [← integral_indicator hA]
    apply integral_congr_ae
    filter_upwards [] with z
    change countStratumIndicator 0 z.1*Ψ z=A.indicator (fun z => Ψ z) z
    have hI : countStratumIndicator 0 z.1=(if z.1.2.1=0 then (1 : ℝ) else 0) := rfl
    rw [hI]
    by_cases hz : z.1.2.1=0 <;> simp [A,B,Set.indicator,hz]
  have htgt : (ξ.prod (finiteMarkLaw p 0)).restrict A=(ξ.restrict B).prod (finiteMarkLaw p 0) := by
    have heq : A=B ×ˢ univ := by ext z; simp [A]
    rw [heq,Measure.restrict_prod_eq_prod_univ]
  have hw := hweak T
  simpa only [hweight,htgt] using hw

end GeneralizedBulk.External.RegularSpectralData
