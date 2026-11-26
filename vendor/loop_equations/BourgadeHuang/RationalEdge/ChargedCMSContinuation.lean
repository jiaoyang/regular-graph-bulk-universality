import BourgadeHuang.RationalEdge.ChargedCMS
import BourgadeHuang.RationalBulk.ChargedCMSContinuation
import BourgadeHuang.EntireRatioCMS

noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalEdge
open RationalBulk

/-- The actual expectation obeys the edge deformed system at every complex numerator
tuple. The only surviving sign restrictions are those of denominator branches. -/
theorem expectedChargedObservable_deformedCMS_all_numerators {n m : ℕ}
    (ν : Measure AnchoredCountingState) (β : ℝ) (hβ : β ≠ 0)
    (hh : ExactHierarchy ν β) {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (c b : Fin (n+m) → ℂ) (hc : ∀ j, c j = -1 ∨ c j = (β:ℂ)/2)
    (hcN : ∀ j : Fin n, c (Fin.castAdd m j) = -1)
    (hb : ∀ j, (b j).im ≠ 0) (hbalance : BaseBalanced c b)
    (u : Fin n → ℂ) (v : Fin m → ℂ)
    (hv : ∀ j, SameOpenHalfPlane (v j) (b (Fin.natAdd n j)))
    (hfree : CMS.CollisionFree (Fin.append u v)) :
    ∀ i, EdgeCMS.edgeOperator (β:ℂ) c i (expectedChargedObservable ν c b) (Fin.append u v) = 0 := by
  obtain ⟨u₀,hpair,hfree₀⟩ := exists_charged_collisionFree_numerators
    (fun j => b (Fin.castAdd m j)) v (fun j => hb _)
    ((CMS.collisionFree_append u v).mp hfree).2.1
  have hf (t : Fin n → ℂ) : AnalyticAt ℂ (expectedChargedObservable ν c b) (Fin.append t v) := by
    apply analyticAt_expectedChargedObservable ν ha he c b (Fin.append t v)
    refine ⟨hb, ?_⟩
    intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · exact fun h => (h (hcN j)).elim
    · exact fun _ => by simpa only [Fin.append_right] using hv j
  have hlocal : ∀ᶠ t in nhds u₀, CMS.CollisionFree (Fin.append t v) ∧
      ∀ i, EdgeCMS.edgeOperator (β:ℂ) c i (expectedChargedObservable ν c b) (Fin.append t v) = 0 := by
    have hcont := (CMS.analyticAt_append_left v u₀).continuousAt.tendsto
    have hp : ∀ᶠ t in nhds u₀, ∀j, SameOpenHalfPlane (t j) (b (Fin.castAdd m j)) := by
      apply Filter.eventually_all.mpr
      intro j
      exact (continuous_apply j).continuousAt.eventually (sameOpenHalfPlane_nhds (hpair j))
    filter_upwards [hcont.eventually (eventually_collisionFree hfree₀), hp] with t ht htp
    refine ⟨ht, fun i => expectedChargedObservable_deformedCMS ν β hβ hh ha he c b (Fin.append t v) hc ?_ hbalance ht i⟩
    intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa only [Fin.append_left] using htp j
    · simpa only [Fin.append_right] using hv j
  exact EdgeCMS.edgeOperator_eq_zero_of_local_numerator (β:ℂ) c
    (expectedChargedObservable ν c b) v hf u₀ hlocal u hfree

end BourgadeHuang.RationalEdge
