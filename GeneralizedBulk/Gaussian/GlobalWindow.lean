import GeneralizedBulk.Gaussian.WindowBounds
import GeneralizedBulk.Gaussian.GlobalConstruction

/-! Jointly measurable actual retained-window fields over random states. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped Topology BigOperators
namespace GeneralizedBulk.Gaussian
variable {I S : Type*} [Countable I] [MeasurableSpace S]

def globalWindowTerm (X : S → PresentedState I) (p : ℝ) (sigma : ℂ) (R : ℝ)
    (v : ℂ × Bool) (i j : Fin 4) (k : I) (z : S × (I → Fin 4 → ℝ)) : ℂ := by
  classical
  exact if (X z.1).location k ∈ Set.Icc (-R) R then
    sigma * particleCoefficient ((X z.1).location k) v * (rawQuadratic p i j (z.2 k) : ℂ) else 0

def globalWindowField (X : S → PresentedState I) (parameters : Parameters) (R : ℝ)
    (v : ℂ × Bool) (z : S × (I → Fin 4 → ℝ)) : EndpointMatrix :=
  fun i j => ∑' k, globalWindowTerm X parameters.p parameters.scale R v i j k z

theorem summable_globalWindowTerm (X : S → PresentedState I) (p : ℝ) (sigma : ℂ) (R : ℝ)
    (v : ℂ × Bool) (i j : Fin 4) (z : S × (I → Fin 4 → ℝ)) :
    Summable (fun k => globalWindowTerm X p sigma R v i j k z) := by
  classical
  apply summable_of_ne_finset_zero (s := presentationWindowFinset (X z.1).presentation R)
  intro k hk
  have hn : (X z.1).location k ∉ Set.Icc (-R) R := by
    simpa only [mem_presentationWindowFinset,PresentedState.presentation] using hk
  simp only [globalWindowTerm,hn,ite_false]

theorem globalWindowField_eq_windowField (X : S → PresentedState I) (parameters : Parameters)
    (R : ℝ) (v : ℂ × Bool) (z : S × (I → Fin 4 → ℝ)) :
    globalWindowField X parameters R v z = windowField parameters (X z.1).presentation (-R) R v z.2 := by
  classical
  ext i j
  change (∑' k, globalWindowTerm X parameters.p parameters.scale R v i j k z) = _
  rw [tsum_eq_sum (s := presentationWindowFinset (X z.1).presentation R) (fun k hk => by
    have hn : (X z.1).location k ∉ Set.Icc (-R) R := by
      simpa only [mem_presentationWindowFinset,PresentedState.presentation] using hk
    simp only [globalWindowTerm,hn,ite_false])]
  calc
    _ = ∑ k ∈ presentationWindowFinset (X z.1).presentation R,
        (parameters.scale : ℂ) * particleCoefficient ((X z.1).location k) v *
          (rawQuadratic parameters.p i j (z.2 k) : ℂ) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hm : (X z.1).location k ∈ Set.Icc (-R) R :=
        (mem_presentationWindowFinset (X z.1).presentation R k).mp hk
      simp only [globalWindowTerm,hm,ite_true]
    _ = _ := sum_presentationWindowFinset (X z.1).presentation R _

/-- Joint measurability is proved from the literal finite-support sum; no
measurable state-dependent enumeration of retained labels is assumed. -/
theorem measurable_globalWindowField (X : S → PresentedState I) (hX : Measurable X)
    (parameters : Parameters) (R : ℝ) (v : ℂ × Bool) :
    Measurable (globalWindowField X parameters R v) := by
  classical
  change @Measurable _ (Fin 4 → Fin 4 → ℂ) _ (borel _) _
  rw [← @BorelSpace.measurable_eq (Fin 4 → Fin 4 → ℂ) _ MeasurableSpace.pi (by infer_instance)]
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  apply GeneralizedBulk.Analysis.measurable_tsum_of_summable
  · intro k
    have hx : Measurable (fun z : S × (I → Fin 4 → ℝ) => (X z.1).location k) :=
      ((PresentedState.measurable_location k).comp hX).comp measurable_fst
    apply Measurable.ite (measurableSet_Icc.preimage hx)
    · exact (((measurable_particleCoefficient v).comp hx).const_mul (parameters.scale : ℂ)).mul
        ((measurable_rawQuadratic parameters.p i j).complex_ofReal.comp
          ((measurable_pi_apply k).comp measurable_snd))
    · exact measurable_const
  · exact summable_globalWindowTerm X parameters.p parameters.scale R v i j

end GeneralizedBulk.Gaussian
