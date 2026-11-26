import BourgadeHuang.OrthogonalRatioDerivatives
import BourgadeHuang.OrthogonalRatioSlices

/-! Actual first and second partial derivatives of orthogonal ratio expectations.
Every interchange of differentiation and integration uses the proved common
measurable power series and exponential-square anchor control. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang
namespace OrthogonalCMS

abbrev RatioFunction (q : ℕ) := (Fin q → ℂ) → (Fin q → ℂ) → (Fin q → ℂ) → ℂ

def numeratorPartial {q : ℕ} (i : Fin q) (F : RatioFunction q) (u v w : Fin q → ℂ) : ℂ :=
  deriv (fun z => F (Function.update u i z) v w) (u i)

def firstDenominatorPartial {q : ℕ} (i : Fin q) (F : RatioFunction q) (u v w : Fin q → ℂ) : ℂ :=
  deriv (fun z => F u (Function.update v i z) w) (v i)

def secondDenominatorPartial {q : ℕ} (i : Fin q) (F : RatioFunction q) (u v w : Fin q → ℂ) : ℂ :=
  deriv (fun z => F u v (Function.update w i z)) (w i)

end OrthogonalCMS

theorem expectedOrthogonalCharacteristicRatios_numerator_first {q : ℕ}
    (ν : Measure AnchoredCountingState) {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (u v w : Fin q → ℂ) (hwv : ∀ j, SameOpenHalfPlane (w j) (v j)) (i : Fin q) (hu : (u i).im ≠ 0) :
    Integrable (fun s => (-anchoredNevanlinna s (u i))*orthogonalCharacteristicRatios s u v w) ν ∧
    OrthogonalCMS.numeratorPartial i (expectedOrthogonalCharacteristicRatios ν) u v w =
      ∫ s, (-anchoredNevanlinna s (u i))*orthogonalCharacteristicRatios s u v w ∂ν := by
  have h := (hasAnchoredPowerSeries_orthogonalRatios_numerator u v w hwv i).integral_iteratedDeriv ν ha he 1
  simp only [iteratedDeriv_succ,iteratedDeriv_zero] at h
  have hpoint (s : AnchoredCountingState) := (hasDerivAt_orthogonalCharacteristicRatios_numerator s u v w i hu).deriv
  simp_rw [hpoint] at h
  refine ⟨h.1, ?_⟩
  simpa only [OrthogonalCMS.numeratorPartial,expectedOrthogonalCharacteristicRatios,
    Function.update_idem,Function.update_self] using h.2

theorem expectedOrthogonalCharacteristicRatios_numerator_second {q : ℕ}
    (ν : Measure AnchoredCountingState) {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (u v w : Fin q → ℂ) (hwv : ∀ j, SameOpenHalfPlane (w j) (v j)) (i : Fin q) (hu : (u i).im ≠ 0) :
    Integrable (fun s => (anchoredNevanlinna s (u i)^2-anchoredDerivative s (u i))*orthogonalCharacteristicRatios s u v w) ν ∧
    OrthogonalCMS.numeratorPartial i (OrthogonalCMS.numeratorPartial i (expectedOrthogonalCharacteristicRatios ν)) u v w =
      ∫ s, (anchoredNevanlinna s (u i)^2-anchoredDerivative s (u i))*orthogonalCharacteristicRatios s u v w ∂ν := by
  have h := (hasAnchoredPowerSeries_orthogonalRatios_numerator u v w hwv i).integral_iteratedDeriv ν ha he 2
  simp only [iteratedDeriv_succ,iteratedDeriv_zero] at h
  have hpoint (s : AnchoredCountingState) := (hasDerivAt_orthogonalCharacteristicRatios_numerator_second s u v w i hu).deriv
  simp_rw [hpoint] at h
  refine ⟨h.1, ?_⟩
  simpa only [OrthogonalCMS.numeratorPartial,expectedOrthogonalCharacteristicRatios,
    Function.update_idem,Function.update_self] using h.2

theorem expectedOrthogonalCharacteristicRatios_firstDenominator_first {q : ℕ}
    (ν : Measure AnchoredCountingState) {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (u v w : Fin q → ℂ) (hwv : ∀ j, SameOpenHalfPlane (w j) (v j)) (i : Fin q) :
    Integrable (fun s => ((1/2:ℂ)*anchoredNevanlinna s (v i))*orthogonalCharacteristicRatios s u v w) ν ∧
    OrthogonalCMS.firstDenominatorPartial i (expectedOrthogonalCharacteristicRatios ν) u v w =
      ∫ s, ((1/2:ℂ)*anchoredNevanlinna s (v i))*orthogonalCharacteristicRatios s u v w ∂ν := by
  have h := (hasAnchoredPowerSeries_orthogonalRatios_firstDenominator u v w hwv i).integral_iteratedDeriv ν ha he 1
  simp only [iteratedDeriv_succ,iteratedDeriv_zero] at h
  have hpoint (s : AnchoredCountingState) := (hasDerivAt_orthogonalCharacteristicRatios_firstDenominator s u v w i (hwv i)).deriv
  simp_rw [hpoint] at h
  refine ⟨h.1, ?_⟩
  simpa only [OrthogonalCMS.firstDenominatorPartial,expectedOrthogonalCharacteristicRatios,
    Function.update_idem,Function.update_self] using h.2

theorem expectedOrthogonalCharacteristicRatios_firstDenominator_second {q : ℕ}
    (ν : Measure AnchoredCountingState) {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (u v w : Fin q → ℂ) (hwv : ∀ j, SameOpenHalfPlane (w j) (v j)) (i : Fin q) :
    Integrable (fun s => ((1/2:ℂ)*anchoredDerivative s (v i)+(1/4:ℂ)*anchoredNevanlinna s (v i)^2)*orthogonalCharacteristicRatios s u v w) ν ∧
    OrthogonalCMS.firstDenominatorPartial i (OrthogonalCMS.firstDenominatorPartial i (expectedOrthogonalCharacteristicRatios ν)) u v w =
      ∫ s, ((1/2:ℂ)*anchoredDerivative s (v i)+(1/4:ℂ)*anchoredNevanlinna s (v i)^2)*orthogonalCharacteristicRatios s u v w ∂ν := by
  have h := (hasAnchoredPowerSeries_orthogonalRatios_firstDenominator u v w hwv i).integral_iteratedDeriv ν ha he 2
  simp only [iteratedDeriv_succ,iteratedDeriv_zero] at h
  have hpoint (s : AnchoredCountingState) := (hasDerivAt_orthogonalCharacteristicRatios_firstDenominator_second s u v w i (hwv i)).deriv
  simp_rw [hpoint] at h
  refine ⟨h.1, ?_⟩
  simpa only [OrthogonalCMS.firstDenominatorPartial,expectedOrthogonalCharacteristicRatios,
    Function.update_idem,Function.update_self] using h.2

theorem expectedOrthogonalCharacteristicRatios_secondDenominator_first {q : ℕ}
    (ν : Measure AnchoredCountingState) {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (u v w : Fin q → ℂ) (hwv : ∀ j, SameOpenHalfPlane (w j) (v j)) (i : Fin q) :
    Integrable (fun s => ((1/2:ℂ)*anchoredNevanlinna s (w i))*orthogonalCharacteristicRatios s u v w) ν ∧
    OrthogonalCMS.secondDenominatorPartial i (expectedOrthogonalCharacteristicRatios ν) u v w =
      ∫ s, ((1/2:ℂ)*anchoredNevanlinna s (w i))*orthogonalCharacteristicRatios s u v w ∂ν := by
  have h := (hasAnchoredPowerSeries_orthogonalRatios_secondDenominator u v w hwv i).integral_iteratedDeriv ν ha he 1
  simp only [iteratedDeriv_succ,iteratedDeriv_zero] at h
  have hpoint (s : AnchoredCountingState) := (hasDerivAt_orthogonalCharacteristicRatios_secondDenominator s u v w i (hwv i)).deriv
  simp_rw [hpoint] at h
  refine ⟨h.1, ?_⟩
  simpa only [OrthogonalCMS.secondDenominatorPartial,expectedOrthogonalCharacteristicRatios,
    Function.update_idem,Function.update_self] using h.2

theorem expectedOrthogonalCharacteristicRatios_secondDenominator_second {q : ℕ}
    (ν : Measure AnchoredCountingState) {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (u v w : Fin q → ℂ) (hwv : ∀ j, SameOpenHalfPlane (w j) (v j)) (i : Fin q) :
    Integrable (fun s => ((1/2:ℂ)*anchoredDerivative s (w i)+(1/4:ℂ)*anchoredNevanlinna s (w i)^2)*orthogonalCharacteristicRatios s u v w) ν ∧
    OrthogonalCMS.secondDenominatorPartial i (OrthogonalCMS.secondDenominatorPartial i (expectedOrthogonalCharacteristicRatios ν)) u v w =
      ∫ s, ((1/2:ℂ)*anchoredDerivative s (w i)+(1/4:ℂ)*anchoredNevanlinna s (w i)^2)*orthogonalCharacteristicRatios s u v w ∂ν := by
  have h := (hasAnchoredPowerSeries_orthogonalRatios_secondDenominator u v w hwv i).integral_iteratedDeriv ν ha he 2
  simp only [iteratedDeriv_succ,iteratedDeriv_zero] at h
  have hpoint (s : AnchoredCountingState) := (hasDerivAt_orthogonalCharacteristicRatios_secondDenominator_second s u v w i (hwv i)).deriv
  simp_rw [hpoint] at h
  refine ⟨h.1, ?_⟩
  simpa only [OrthogonalCMS.secondDenominatorPartial,expectedOrthogonalCharacteristicRatios,
    Function.update_idem,Function.update_self] using h.2

end BourgadeHuang
