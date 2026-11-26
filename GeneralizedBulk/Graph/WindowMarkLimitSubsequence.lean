import GeneralizedBulk.Graph.WindowMarkLimit

/-! Product-law identification along the actual scalar/joint subsequence.
The finite kernel remains the original model kernel at the selected indices. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped Topology
namespace GeneralizedBulk.External.RegularSpectralData
open Graph GeneralizedBulk.Counting GeneralizedBulk.Analysis
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

theorem windowMarkLimit_restrict_of_kernel_factorization_subsequence {m : ℕ}
    (r : ℕ → ℕ)
    (P : Measure Ω) [IsProbabilityMeasure P] (hd : 0 < d)
    (E sigma center R : ℝ)
    (selection : ∀ n, Ω → Fin m → Fin (N (r n)))
    (hselection : ∀ n i, Measurable (fun ω => selection n ω i))
    (leaf : Fin d)
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hscalar : WeakLawConverges
      (fun n => Measure.map (fun ω => D.microscopicCountingState (r n) ω E sigma center) P) ν)
    (hboundary : ∀ᵐ s ∂ν, s.val.1.measure {-R} = 0 ∧ s.val.1.measure {R} = 0)
    (ρ : Measure (WindowData m × ((Fin m × Fin 4) → ℝ))) [IsFiniteMeasure ρ]
    (hjoint : WeakLawConverges
      (fun n => D.windowMarkLaw P (r n) E sigma center R (selection n)) ρ)
    (hkernel : ∀ (G : BoundedContinuousFunction (WindowData m) ℝ)
      (F : BoundedContinuousFunction ((Fin m × Fin 4) → ℝ) ℝ),
      Tendsto (fun n => (∫ ω, D.windowCountWeight (r n) E sigma R m
        (fun ω => (G (windowData m (-R) R (D.microscopicCountingState (r n) ω E sigma center)) : ℂ)) ω *
        (↑(∫ x, F x ∂D.twoEdgeLaw (r n) ω (selection n ω) leaf) : ℂ) ∂P) -
        (∫ ω, D.windowCountWeight (r n) E sigma R m
          (fun ω => (G (windowData m (-R) R (D.microscopicCountingState (r n) ω E sigma center)) : ℂ)) ω ∂P) *
          (↑(∫ x, F x ∂Gaussian.finiteMarkLaw (E / d) m) : ℂ)) atTop (𝓝 0)) :
    ρ.restrict (Prod.fst ⁻¹' {x : WindowData m | x.2.1 = m}) =
      ((Measure.map (windowData m (-R) R) ν).restrict {x : WindowData m | x.2.1 = m}).prod
        (Gaussian.finiteMarkLaw (E / d) m) := by
  letI : PolishSpace AnchoredCountingState := isClosed_validAnchoredCountingState.polishSpace
  letI : MetricSpace AnchoredCountingState := TopologicalSpace.metrizableSpaceMetric AnchoredCountingState
  let μ := fun n => D.windowMarkLaw P (r n) E sigma center R (selection n)
  let η := Measure.map (windowData m (-R) R) ν
  letI : ∀ n, IsProbabilityMeasure (Measure.map (fun ω => D.microscopicCountingState (r n) ω E sigma center) P) :=
    fun n => MeasureTheory.isProbabilityMeasure_map
      (D.measurable_microscopicCountingState (r n) E sigma center).aemeasurable
  have hfirst : WeakLawConverges (fun n => Measure.map Prod.fst (μ n)) η := by
    have hw := weakLaw_windowData_of_weak _ ν hscalar m (-R) R hboundary
    simpa only [μ,η,D.windowMarkLaw_fst P hd (r _) E sigma center R _ (hselection _),
      Measure.map_map (measurable_windowData m (-R) R)
        (D.measurable_microscopicCountingState _ E sigma center),Function.comp_def] using hw
  have hfactor (G : BoundedContinuousFunction (WindowData m) ℝ)
      (F : BoundedContinuousFunction ((Fin m × Fin 4) → ℝ) ℝ) :
      Tendsto (fun n => (∫ z, (G z.1 * countStratumIndicator m z.1) * F z.2 ∂μ n) -
        (∫ x, G x * countStratumIndicator m x ∂Measure.map Prod.fst (μ n)) *
          (∫ x, F x ∂Gaussian.finiteMarkLaw (E / d) m)) atTop (𝓝 0) := by
    have hc := hkernel G F
    have hr := Complex.continuous_re.continuousAt.tendsto.comp hc
    have heq (n : ℕ) :
        ((∫ ω, D.windowCountWeight (r n) E sigma R m
          (fun ω => (G (windowData m (-R) R (D.microscopicCountingState (r n) ω E sigma center)) : ℂ)) ω *
          (↑(∫ x, F x ∂D.twoEdgeLaw (r n) ω (selection n ω) leaf) : ℂ) ∂P) -
          (∫ ω, D.windowCountWeight (r n) E sigma R m
            (fun ω => (G (windowData m (-R) R (D.microscopicCountingState (r n) ω E sigma center)) : ℂ)) ω ∂P) *
            (↑(∫ x, F x ∂Gaussian.finiteMarkLaw (E / d) m) : ℂ)).re =
        (∫ z, (G z.1 * countStratumIndicator m z.1) * F z.2 ∂μ n) -
          (∫ x, G x * countStratumIndicator m x ∂Measure.map Prod.fst (μ n)) *
            (∫ x, F x ∂Gaussian.finiteMarkLaw (E / d) m) := by
      simp only [windowCountWeight_eq_indicator,← Complex.ofReal_mul,integral_complex_ofReal]
      have hT : (∫ z, (G z.1 * countStratumIndicator m z.1) * F z.2 ∂μ n) =
          ∫ ω, (G (windowData m (-R) R (D.microscopicCountingState (r n) ω E sigma center)) *
            countStratumIndicator m (windowData m (-R) R (D.microscopicCountingState (r n) ω E sigma center))) *
              (∫ x, F x ∂D.twoEdgeLaw (r n) ω (selection n ω) leaf) ∂P :=
        D.windowMarkLaw_tensor_integral P hd (r n) E sigma center R (selection n) (hselection n) leaf
          (G * countStratumIndicator m) F
      rw [hT]
      have hS : (∫ x, G x * countStratumIndicator m x ∂Measure.map Prod.fst (μ n)) =
          ∫ ω, G (windowData m (-R) R (D.microscopicCountingState (r n) ω E sigma center)) *
            countStratumIndicator m (windowData m (-R) R (D.microscopicCountingState (r n) ω E sigma center)) ∂P := by
        rw [show Measure.map Prod.fst (μ n) = _ from
          D.windowMarkLaw_fst P hd (r n) E sigma center R (selection n) (hselection n)]
        exact integral_map
          (((measurable_windowData m (-R) R).comp (D.measurable_microscopicCountingState (r n) E sigma center)).aemeasurable)
          (G * countStratumIndicator m).continuous.measurable.aestronglyMeasurable
      rw [hS]
      simp only [← Complex.ofReal_sub,← Complex.ofReal_mul,Complex.ofReal_re]
    simpa only [Function.comp_def,heq,Complex.zero_re] using hr
  have h := weakLimit_restrict_eq_prod_of_tensor_factorization μ ρ η
    (Gaussian.finiteMarkLaw (E / d) m) (countStratumIndicator m)
    (countStratumIndicator_zero_or_one m) hjoint hfirst hfactor
  have heq : {x : WindowData m | countStratumIndicator m x = 1} = {x | x.2.1 = m} := by
    ext x
    change (if x.2.1 = m then (1 : ℝ) else 0) = 1 ↔ x.2.1 = m
    by_cases hx : x.2.1 = m <;> simp [hx]
  simpa only [heq,η] using h


end GeneralizedBulk.External.RegularSpectralData
