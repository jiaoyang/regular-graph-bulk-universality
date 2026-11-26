import BourgadeHuang.RationalBulk.ChargedDerivatives
import BourgadeHuang.RationalEdge.WeightedPathLoop
import BourgadeHuang.RationalBulk.ChargedCMS
import BourgadeHuang.EdgeCMS.Basic

/-! The edge deformed CMS system for genuine arbitrary-coupling expectations.
The exact mixed hierarchy is the only integration-by-parts input. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalEdge
open RationalBulk

theorem chargedObservable_integrable_and_endpoint_loop {d : ℕ}
    (ν : Measure AnchoredCountingState) (β : ℝ) (hh : ExactHierarchy ν β)
    {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (c b z : Fin d → ℂ) (hz : ∀ j, SameOpenHalfPlane (z j) (b j))
    (hbalance : BaseBalanced c b) {w : ℂ} (hw : w.im ≠ 0) :
    Integrable (fun s => chargedObservable c b s z) ν ∧
    Integrable (fun s => (loopHead β s w + (2/(β:ℂ)) *
      ∑ j, c j * anchoredDividedDifference s w (z j)) * chargedObservable c b s z) ν ∧
    (∫ s, (loopHead β s w + (2/(β:ℂ)) *
      ∑ j, c j * anchoredDividedDifference s w (z j)) * chargedObservable c b s z ∂ν) = 0 := by
  have h := weightedRatioPrimitives_integrable_and_endpoint_loop ν β hh ha he c z b hz hw
  have hcancel (s : AnchoredCountingState) :
      (∑ j, c j * (anchoredDividedDifference s w (z j) -
        anchoredDividedDifference s w (b j))) = ∑ j, c j * anchoredDividedDifference s w (z j) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hbalance.sum_comp (anchoredDividedDifference s w), sub_zero]
  simpa only [hcancel, ← chargedObservable_eq_exp c b z hz] using h

/-- Genuine coordinate derivatives of the expectation satisfy all rows of the
CMS system, for arbitrary nonzero real coupling and the two physical charges. -/
theorem expectedChargedObservable_deformedCMS {d : ℕ}
    (ν : Measure AnchoredCountingState) (β : ℝ) (hβ : β ≠ 0)
    (hh : ExactHierarchy ν β) {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (c b z : Fin d → ℂ) (hc : ∀ j, c j = -1 ∨ c j = (β:ℂ)/2)
    (hz : ∀ j, SameOpenHalfPlane (z j) (b j))
    (hbalance : BaseBalanced c b) (hcoll : CMS.CollisionFree z) (i : Fin d) :
    EdgeCMS.edgeOperator (β:ℂ) c i (expectedChargedObservable ν c b) z = 0 := by
  have hdomain : ChargedDomain c b z := ⟨fun j => (hz j).right_offReal, fun j _ => hz j⟩
  have hfirst j := expectedChargedObservable_first ν ha he c b z hdomain j (hz j).left_offReal
  have hsecond := expectedChargedObservable_second ν ha he c b z hdomain i (hz i).left_offReal
  have hloop := chargedObservable_integrable_and_endpoint_loop ν β hh ha he c b z hz hbalance (hz i).left_offReal
  let P := fun s => chargedObservable c b s z
  let A := fun j s => c j * anchoredNevanlinna s (z j) * P s
  let Q := fun s => (c i * anchoredDerivative s (z i) + c i^2 * anchoredNevanlinna s (z i)^2) * P s
  let T := fun j s => (c i * c j * A i s - c i^2 * A j s) / (z i - z j)
  have hiP : Integrable P ν := hloop.1
  have hiA j : Integrable (A j) ν := (hfirst j).1
  have hiQ : Integrable Q ν := hsecond.1
  have hiT j : Integrable (T j) ν :=
    (((hiA i).const_mul (c i*c j)).sub ((hiA j).const_mul (c i^2))).div_const _
  have hT j :
      (c i*c j*CMS.coordDeriv i (expectedChargedObservable ν c b) z -
        c i^2*CMS.coordDeriv j (expectedChargedObservable ν c b) z)/(z i-z j) =
          ∫ s, T j s ∂ν := by
    rw [(hfirst i).2, (hfirst j).2, ← integral_const_mul, ← integral_const_mul,
      ← integral_sub ((hiA i).const_mul _) ((hiA j).const_mul _), ← integral_div]
  have hOp : EdgeCMS.edgeOperator (β:ℂ) c i (expectedChargedObservable ν c b) z =
      ∫ s, Q s - c i^2*z i*P s + (2/(β:ℂ))*∑ j ∈ Finset.univ.erase i, T j s ∂ν := by
    unfold EdgeCMS.edgeOperator
    simp_rw [hT, hsecond.2]
    change (∫ s, Q s ∂ν) - c i^2*z i*(∫ s, P s ∂ν) +
      (2/(β:ℂ))*∑ j ∈ Finset.univ.erase i, ∫ s, T j s ∂ν = _
    rw [integral_add
      (show Integrable (fun s => Q s - c i^2*z i*P s) ν from hiQ.sub (hiP.const_mul _))
      (show Integrable (fun s => (2/(β:ℂ))*∑ j ∈ Finset.univ.erase i, T j s) ν from
        (integrable_finset_sum _ (fun j _ => hiT j)).const_mul _),
      integral_sub hiQ (hiP.const_mul (c i^2*z i)), integral_const_mul, integral_const_mul,
      integral_finset_sum _ (fun j _ => hiT j)]
  rw [hOp]
  have hzero : (∫ s, c i^2 * ((loopHead β s (z i) + (2/(β:ℂ)) *
      ∑ j, c j * anchoredDividedDifference s (z i) (z j)) * P s) ∂ν) = 0 := by
    rw [integral_const_mul, hloop.2.2, mul_zero]
  convert hzero using 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro s
  apply EdgeCMS.edge_loop_algebra (β:ℂ) c
    (fun j => anchoredNevanlinna s (z j)) (fun j => anchoredDerivative s (z j))
    (fun j k => anchoredDividedDifference s (z j) (z k)) z (P s) i
    (CMS.charge_self_interaction (by exact_mod_cast hβ) (hc i))
    (anchoredDividedDifference_self s (hz i).left_offReal)
  intro j hj
  exact (anchoredDividedDifference_eq_quotient s (hz i).left_offReal (hz j).left_offReal
    (fun h => (Finset.mem_erase.mp hj).1 (hcoll h).symm)).symm

end BourgadeHuang.RationalEdge
