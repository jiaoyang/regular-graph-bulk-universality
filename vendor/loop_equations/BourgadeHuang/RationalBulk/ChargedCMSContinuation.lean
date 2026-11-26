import BourgadeHuang.RationalBulk.ChargedCMS
import BourgadeHuang.EntireRatioCMS

noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalBulk

/-- Arbitrarily many numerators can be placed in prescribed half-planes while
avoiding all fixed, distinct denominators. -/
theorem exists_charged_collisionFree_numerators {n m : ℕ}
    (b : Fin n → ℂ) (v : Fin m → ℂ) (hb : ∀ j, (b j).im ≠ 0)
    (hv : Function.Injective v) :
    ∃ u : Fin n → ℂ, (∀ j, SameOpenHalfPlane (u j) (b j)) ∧
      CMS.CollisionFree (Fin.append u v) := by
  let A : ℝ := 1+∑ j, |(v j).re|
  let u : Fin n → ℂ := fun j => (A+j.val : ℝ)+Complex.I*(if 0 < (b j).im then 1 else -1)
  have hure (j : Fin n) : (u j).re = A+j.val := by
    dsimp [u]
    split_ifs <;> simp
  have hpair (j : Fin n) : SameOpenHalfPlane (u j) (b j) := by
    by_cases hp : 0 < (b j).im
    · exact Or.inl ⟨by simp [u,hp],hp⟩
    · have hn : (b j).im < 0 := lt_of_le_of_ne (le_of_not_gt hp) (hb j)
      exact Or.inr ⟨by simp [u,hp],hn⟩
  have hui : Function.Injective u := by
    intro i j he
    have hr := congrArg Complex.re he
    rw [hure,hure,add_right_inj] at hr
    exact Fin.ext (by exact_mod_cast hr)
  have hc : CMS.CrossDistinct u v := by
    intro i j he
    have hsum : |(v j).re| ≤ ∑ k, |(v k).re| :=
      Finset.single_le_sum (f := fun k : Fin m => |(v k).re|) (fun k _ => abs_nonneg _) (Finset.mem_univ j)
    have hr := congrArg Complex.re he
    rw [hure] at hr
    have hn : (0:ℝ) ≤ i.val := Nat.cast_nonneg _
    dsimp [A] at hr
    linarith [le_abs_self (v j).re]
  exact ⟨u,hpair,(CMS.collisionFree_append u v).mpr ⟨hui,hv,hc⟩⟩

/-- The actual expectation obeys the deformed system at every complex numerator
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
    ∀ i, CMS.deformedOperator (β:ℂ) c i (expectedChargedObservable ν c b) (Fin.append u v) = 0 := by
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
      ∀ i, CMS.deformedOperator (β:ℂ) c i (expectedChargedObservable ν c b) (Fin.append t v) = 0 := by
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
  exact CMS.deformedOperator_eq_zero_of_local_numerator (β:ℂ) c
    (expectedChargedObservable ν c b) v hf u₀ hlocal u hfree

end BourgadeHuang.RationalBulk
