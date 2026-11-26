import BourgadeHuang.RationalBulk.ChargedObservables

noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalBulk

theorem hasDerivAt_chargedObservable_second {d : ℕ} (c b z : Fin d → ℂ)
    (s : AnchoredCountingState) (i : Fin d) (hz : (z i).im ≠ 0)
    (hb : c i ≠ -1 → SameOpenHalfPlane (z i) (b i)) :
    HasDerivAt (deriv (fun w => chargedObservable c b s (Function.update z i w)))
      ((c i * anchoredDerivative s (z i) + c i^2 * anchoredNevanlinna s (z i)^2) *
        chargedObservable c b s z) (z i) := by
  have hd := ((hasDerivAt_anchoredNevanlinna s hz).const_mul (c i)).mul
    (hasDerivAt_chargedObservable c b z s i hz hb)
  simp only [Function.update_eq_self] at hd
  have hd' : HasDerivAt
      (fun w => (c i * anchoredNevanlinna s w) * chargedObservable c b s (Function.update z i w))
      ((c i * anchoredDerivative s (z i) + c i^2 * anchoredNevanlinna s (z i)^2) *
        chargedObservable c b s z) (z i) := by
    convert hd using 1
    ring
  apply hd'.congr_of_eventuallyEq
  have hne := (isOpen_ne_fun Complex.continuous_im continuous_const).mem_nhds hz
  have hsame : ∀ᶠ w in 𝓝 (z i), c i ≠ -1 → SameOpenHalfPlane w (b i) := by
    by_cases hc : c i = -1
    · exact Filter.Eventually.of_forall (fun _ h => (h hc).elim)
    · filter_upwards [sameOpenHalfPlane_nhds (hb hc)] with w hw
      exact fun _ => hw
  filter_upwards [hne, hsame] with w hw hwb
  simpa only [Function.update_idem, Function.update_self] using
    (hasDerivAt_chargedObservable c b (Function.update z i w) s i
      (by simpa using hw) (by simpa using hwb)).deriv

theorem expectedChargedObservable_first {d : ℕ}
    (ν : Measure AnchoredCountingState) {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (c b z : Fin d → ℂ) (hz : ChargedDomain c b z) (i : Fin d)
    (hi : (z i).im ≠ 0) :
    Integrable (fun s => c i * anchoredNevanlinna s (z i) * chargedObservable c b s z) ν ∧
    CMS.coordDeriv i (expectedChargedObservable ν c b) z =
      ∫ s, c i * anchoredNevanlinna s (z i) * chargedObservable c b s z ∂ν := by
  have h := (hasAnchoredPowerSeries_chargedObservable_slice c b z hz i).integral_iteratedDeriv ν ha he 1
  simp only [iteratedDeriv_succ, iteratedDeriv_zero] at h
  have hpoint (s : AnchoredCountingState) := (hasDerivAt_chargedObservable c b z s i hi (hz.2 i)).deriv
  simp_rw [hpoint] at h
  exact h

theorem expectedChargedObservable_second {d : ℕ}
    (ν : Measure AnchoredCountingState) {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (c b z : Fin d → ℂ) (hz : ChargedDomain c b z) (i : Fin d)
    (hi : (z i).im ≠ 0) :
    Integrable (fun s => (c i * anchoredDerivative s (z i) +
      c i^2 * anchoredNevanlinna s (z i)^2) * chargedObservable c b s z) ν ∧
    CMS.secondPartial i (expectedChargedObservable ν c b) z =
      ∫ s, (c i * anchoredDerivative s (z i) +
        c i^2 * anchoredNevanlinna s (z i)^2) * chargedObservable c b s z ∂ν := by
  have h := (hasAnchoredPowerSeries_chargedObservable_slice c b z hz i).integral_iteratedDeriv ν ha he 2
  simp only [iteratedDeriv_succ, iteratedDeriv_zero] at h
  have hpoint (s : AnchoredCountingState) := (hasDerivAt_chargedObservable_second c b z s i hi (hz.2 i)).deriv
  simp_rw [hpoint] at h
  refine ⟨h.1, ?_⟩
  simpa only [CMS.secondPartial, CMS.coordDeriv, expectedChargedObservable,
    Function.update_idem, Function.update_self] using h.2

end BourgadeHuang.RationalBulk
