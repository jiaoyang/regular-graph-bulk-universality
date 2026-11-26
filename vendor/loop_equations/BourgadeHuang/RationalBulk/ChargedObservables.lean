import BourgadeHuang.OrthogonalRatioAnalytic
import BourgadeHuang.CMS.GeneralCoupling

/-! Genuine charged characteristic ratios for arbitrary coupling. Numerator
charges use the canonical entire numerator, rather than a formal continuation.
Every denominator uses the actual holomorphic path primitive. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalBulk

/-- Charge −1 gives the entire characteristic-ratio numerator. -/
def chargedFactor (c : ℂ) (s : AnchoredCountingState) (z b : ℂ) : ℂ :=
  if c = -1 then entireCharacteristicRatio s z b
  else Complex.exp (c * nevanlinnaPathPrimitive s z b)

def chargedObservable {d : ℕ} (c b : Fin d → ℂ) (s : AnchoredCountingState)
    (z : Fin d → ℂ) : ℂ := ∏ j, chargedFactor (c j) s (z j) (b j)

def expectedChargedObservable {d : ℕ} (ν : Measure AnchoredCountingState)
    (c b z : Fin d → ℂ) : ℂ := ∫ s, chargedObservable c b s z ∂ν

/-- Admissibility includes all complex numerator values and each chosen
open half-plane for the denominator coordinates. -/
def ChargedDomain {d : ℕ} (c b z : Fin d → ℂ) : Prop :=
  (∀ j, (b j).im ≠ 0) ∧ ∀ j, c j ≠ -1 → SameOpenHalfPlane (z j) (b j)

theorem chargedFactor_eq_exp (c : ℂ) (s : AnchoredCountingState) {z b : ℂ}
    (hz : SameOpenHalfPlane z b) :
    chargedFactor c s z b = Complex.exp (c * nevanlinnaPathPrimitive s z b) := by
  by_cases hc : c = -1
  · simp only [chargedFactor, if_pos hc, hc, neg_one_mul]
    simp only [ite_true]
    rw [entireCharacteristicRatio_eq_anchored s hz, anchoredCharacteristicRatio_eq_exp_primitive]
  · simp only [chargedFactor, if_neg hc]

theorem chargedObservable_eq_exp {d : ℕ} (c b z : Fin d → ℂ)
    (hz : ∀ j, SameOpenHalfPlane (z j) (b j)) (s : AnchoredCountingState) :
    chargedObservable c b s z =
      Complex.exp (∑ j, c j * nevanlinnaPathPrimitive s (z j) (b j)) := by
  simp only [chargedObservable, chargedFactor_eq_exp _ _ (hz _), Complex.exp_sum]

theorem hasDerivAt_chargedFactor (c : ℂ) (s : AnchoredCountingState)
    {z b : ℂ} (hz : z.im ≠ 0) (hb : c ≠ -1 → SameOpenHalfPlane z b) :
    HasDerivAt (fun w => chargedFactor c s w b)
      (c * anchoredNevanlinna s z * chargedFactor c s z b) z := by
  by_cases hc : c = -1
  · simpa only [chargedFactor, if_pos hc, hc, neg_one_mul] using
      hasDerivAt_entireCharacteristicRatio_numerator s (v := b) hz
  · simpa only [chargedFactor, if_neg hc, mul_comm (Complex.exp _)] using
      ((hasDerivAt_nevanlinnaPathPrimitive_numerator s (hb hc)).const_mul c).cexp

theorem hasAnchoredPowerSeries_chargedFactor (c : ℂ) {z b : ℂ} (hb : b.im ≠ 0)
    (hz : c ≠ -1 → SameOpenHalfPlane z b) :
    HasAnchoredPowerSeries (fun s w => chargedFactor c s w b) z := by
  by_cases hc : c = -1
  · simpa only [chargedFactor, if_pos hc] using hasAnchoredPowerSeries_entireRatio_numerator z hb
  · simpa only [chargedFactor, if_neg hc] using hasAnchoredPowerSeries_exp_primitive c (hz hc)

theorem chargedObservable_update {d : ℕ} (c b z : Fin d → ℂ)
    (s : AnchoredCountingState) (i : Fin d) (w : ℂ) :
    chargedObservable c b s (Function.update z i w) =
      (∏ j ∈ Finset.univ.erase i, chargedFactor (c j) s (z j) (b j)) *
        chargedFactor (c i) s w (b i) := by
  rw [chargedObservable, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

theorem hasDerivAt_chargedObservable {d : ℕ} (c b z : Fin d → ℂ)
    (s : AnchoredCountingState) (i : Fin d) (hz : (z i).im ≠ 0)
    (hb : c i ≠ -1 → SameOpenHalfPlane (z i) (b i)) :
    HasDerivAt (fun w => chargedObservable c b s (Function.update z i w))
      (c i * anchoredNevanlinna s (z i) * chargedObservable c b s z) (z i) := by
  simp_rw [chargedObservable_update]
  convert (hasDerivAt_chargedFactor (c i) s hz hb).const_mul
    (∏ j ∈ Finset.univ.erase i, chargedFactor (c j) s (z j) (b j)) using 1
  rw [chargedObservable, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  ring

theorem hasAnchoredPowerSeries_chargedObservable {d : ℕ} (c b z : Fin d → ℂ)
    (hz : ChargedDomain c b z) :
    HasAnchoredPowerSeries (fun s w => chargedObservable c b s w) z := by
  apply HasAnchoredPowerSeries.finset_prod
  intro j _
  exact (hasAnchoredPowerSeries_chargedFactor (c j) (hz.1 j) (hz.2 j)).pullback
    (ContinuousLinearMap.proj j) (by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro p
      simpa only [one_mul] using norm_le_pi_norm p j) z

theorem analyticAt_expectedChargedObservable {d : ℕ}
    (ν : Measure AnchoredCountingState) {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (c b z : Fin d → ℂ) (hz : ChargedDomain c b z) :
    AnalyticAt ℂ (expectedChargedObservable ν c b) z :=
  (hasAnchoredPowerSeries_chargedObservable c b z hz).analyticAt_integral ν ha he

theorem hasAnchoredPowerSeries_chargedObservable_slice {d : ℕ}
    (c b z : Fin d → ℂ) (hz : ChargedDomain c b z) (i : Fin d) :
    HasAnchoredPowerSeries (fun s w => chargedObservable c b s (Function.update z i w)) (z i) := by
  let L : ℂ →L[ℂ] (Fin d → ℂ) := ContinuousLinearMap.single ℂ (fun _ : Fin d => ℂ) i
  let v := Function.update z i 0
  have hL : ‖L‖ ≤ 1 := by
    apply L.opNorm_le_bound zero_le_one
    intro w
    simp [L, Pi.norm_single]
  have hmap (w : ℂ) : L w + v = Function.update z i w := by
    ext j
    simp [L, v, Pi.single_apply, Function.update_apply]
    split_ifs <;> simp_all
  have hcenter : L (z i) + v = z := by rw [hmap, Function.update_eq_self]
  have hp : HasAnchoredPowerSeries (fun s w => chargedObservable c b s w) (L (z i) + v) := by
    rw [hcenter]
    exact hasAnchoredPowerSeries_chargedObservable c b z hz
  simpa only [hmap] using hp.comp_affine L hL v (z i)

end BourgadeHuang.RationalBulk
