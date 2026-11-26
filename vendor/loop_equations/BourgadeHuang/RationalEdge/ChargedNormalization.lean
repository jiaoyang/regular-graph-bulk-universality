import BourgadeHuang.RationalEdge.CompactSourceBounds
import BourgadeHuang.RationalBulk.ChargedObservables

/-! Normalization of the actual rational charged observable around an
arbitrary continuous deterministic path center.  At the edge the center is
the chosen analytic square root along each path. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalEdge
open RationalBulk

/-- Deterministic integral of the center along a straight path. -/
def centeredPathPhase (u v : ℂ) (m : RatioInterval → ℂ) : ℂ :=
  ∫ t, (u-v)*m t ∂ratioIntervalMeasure

/-- Weighted pathwise difference from the deterministic center. -/
def centeredPathIntegrand (c u v : ℂ) (m : RatioInterval → ℂ)
    (t : RatioInterval) (s : AnchoredCountingState) : ℂ :=
  c*(u-v)*(anchoredNevanlinna s (ratioPath u v t)-m t)

theorem continuous_centeredPathIntegrand (c u v : ℂ) (m : RatioInterval → ℂ)
    (huv : SameOpenHalfPlane u v) (hm : Continuous m) (s : AnchoredCountingState) :
    Continuous (fun t => centeredPathIntegrand c u v m t s) := by
  apply continuous_const.mul
  apply Continuous.sub _ hm
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (differentiableAt_anchoredNevanlinna s (ratioPath_offReal huv t.property)).continuousAt.comp (f := fun t : RatioInterval => ratioPath u v t)
    ((continuous_ratioPath u v).comp continuous_subtype_val).continuousAt

theorem measurable_centeredPathIntegrand (c u v : ℂ) (m : RatioInterval → ℂ)
    (huv : SameOpenHalfPlane u v) (t : RatioInterval) :
    Measurable (centeredPathIntegrand c u v m t) :=
  (continuous_const.mul ((continuous_anchoredNevanlinna
    (ratioPath_offReal huv t.property)).sub continuous_const)).measurable

theorem nevanlinnaPathPrimitive_centered_by (s : AnchoredCountingState)
    (c u v : ℂ) (m : RatioInterval → ℂ) (huv : SameOpenHalfPlane u v) (hm : Continuous m) :
    c*nevanlinnaPathPrimitive s u v = c*centeredPathPhase u v m +
      integratedSource ratioIntervalMeasure (centeredPathIntegrand c u v m) s := by
  have hS : Continuous (fun t : RatioInterval => (u-v)*anchoredNevanlinna s (ratioPath u v t)) := by
    apply continuous_const.mul
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (differentiableAt_anchoredNevanlinna s (ratioPath_offReal huv t.property)).continuousAt.comp (f := fun t : RatioInterval => ratioPath u v t)
      ((continuous_ratioPath u v).comp continuous_subtype_val).continuousAt
  have hM : Continuous (fun t : RatioInterval => (u-v)*m t) := continuous_const.mul hm
  have hiS : Integrable (fun t : RatioInterval => (u-v)*anchoredNevanlinna s (ratioPath u v t)) ratioIntervalMeasure := hS.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiM : Integrable (fun t : RatioInterval => (u-v)*m t) ratioIntervalMeasure := hM.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp only [nevanlinnaPathPrimitive, centeredPathPhase, integratedSource, centeredPathIntegrand]
  simp_rw [show ∀ x y : ℂ, c*(u-v)*(x-y)=c*((u-v)*x)-c*((u-v)*y) by intros; ring]
  rw [integral_sub (hiS.const_mul c) (hiM.const_mul c)]
  simp only [integral_const_mul]
  ring

/-- The normalized actual expectation differs from one by a controlled amount
whenever the centered path sources have the given genuine moment estimates. -/
theorem expectedChargedObservable_normalized_source_bound
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    {d : ℕ} (hd : 0<d) (c u v : Fin d → ℂ) (m : Fin d → RatioInterval → ℂ)
    (huv : ∀ j, SameOpenHalfPlane (u j) (v j)) (hm : ∀ j, Continuous (m j))
    {δ C E : ℝ} (hδ : 0<δ)
    (h2i : ∀ j t, Integrable (fun s => ‖centeredPathIntegrand (c j) (u j) (v j) (m j) t s‖^2) ν)
    (h2b : ∀ j t, (∫ s, ‖centeredPathIntegrand (c j) (u j) (v j) (m j) t s‖^2 ∂ν) ≤ C*δ^2)
    (hEi : ∀ j t, Integrable (fun s => Real.exp (2*(d:ℝ)*
      ‖centeredPathIntegrand (c j) (u j) (v j) (m j) t s‖)) ν)
    (hEb : ∀ j t, (∫ s, Real.exp (2*(d:ℝ)*
      ‖centeredPathIntegrand (c j) (u j) (v j) (m j) t s‖) ∂ν) ≤ E) :
    ‖Complex.exp (-(∑ j, c j*centeredPathPhase (u j) (v j) (m j)))*
      expectedChargedObservable ν c v u-1‖ ≤ δ*((d:ℝ)^2*C/2+(d:ℝ)*E/2) := by
  let X := fun j => centeredPathIntegrand (c j) (u j) (v j) (m j)
  have hXc j := continuous_centeredPathIntegrand (c j) (u j) (v j) (m j) (huv j) (hm j)
  have hXm j := measurable_centeredPathIntegrand (c j) (u j) (v j) (m j) (huv j)
  obtain ⟨_,hb⟩ := finite_integratedSource_exponential_close ratioIntervalMeasure ν hd
    X hXc hXm hδ h2i h2b hEi hEb
  have heq s : chargedObservable c v s u =
      Complex.exp (∑ j, c j*centeredPathPhase (u j) (v j) (m j))*
        Complex.exp (∑ j, integratedSource ratioIntervalMeasure (X j) s) := by
    rw [chargedObservable_eq_exp c v u huv, ← Complex.exp_add]
    congr 1
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    exact nevanlinnaPathPrimitive_centered_by s (c j) (u j) (v j) (m j) (huv j) (hm j)
  simp only [expectedChargedObservable, heq, integral_const_mul]
  rw [← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]
  exact hb

end BourgadeHuang.RationalEdge
