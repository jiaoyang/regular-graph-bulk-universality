import BourgadeHuang.RationalBulk.RationalReplication
import BourgadeHuang.RationalBulk.ChargedSectorial

/-! Every ordinary characteristic-ratio test is an exact specialization of a
rational replicated observable; consequently these observables determine the
full anchored law, and hence its counting-measure marginal. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter Set
namespace BourgadeHuang.RationalBulk

theorem blockAnchors_repeated {k : ℕ} (p q : ℕ) (eta : Fin k → Bool) :
    blockAnchors (repeatedSigns p eta) (repeatedSigns q eta) =
      Fin.append (replicateCoordinates p (fun j => signAnchor (eta j) 1))
        (replicateCoordinates q (fun j => signAnchor (eta j) 1)) := by
  rfl

theorem anchored_law_eq_of_rational_expectations
    {β : ℝ} {p q : ℕ} (hp : 0<p) (hrat : β*(q:ℝ)=2*(p:ℝ))
    (μ ν : ProbabilityMeasure AnchoredCountingState) {a b : ℝ}
    (ha : 0<a) (hb : 0<b)
    (hμ : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2))
      (μ : Measure AnchoredCountingState))
    (hν : Integrable (fun s : AnchoredCountingState => Real.exp (b*‖s.val.2‖^2))
      (ν : Measure AnchoredCountingState))
    (heq : ∀ (k : ℕ) (eta : Fin k → Bool),
      EqOn
        (expectedChargedObservable (μ : Measure AnchoredCountingState) (charges β (k*p) (k*q))
          (blockAnchors (repeatedSigns p eta) (repeatedSigns q eta)))
        (expectedChargedObservable (ν : Measure AnchoredCountingState) (charges β (k*p) (k*q))
          (blockAnchors (repeatedSigns p eta) (repeatedSigns q eta)))
        (denominatorDomain (k*p) (repeatedSigns q eta))) : μ=ν := by
  apply anchored_law_eq_of_characteristic_ratio_expectations μ ν ha hb hμ hν
  intro k u v huv
  let eta : Fin k → Bool := fun j => decide (0<(v j).im)
  let base : Fin k → ℂ := fun j => signAnchor (eta j) 1
  have hvb j : SameOpenHalfPlane (v j) (base j) := by
    by_cases hj : 0<(v j).im
    · exact Or.inl ⟨hj,by simp [base,eta,hj,signAnchor,CMS.signValue]⟩
    · have hn : (v j).im<0 := lt_of_le_of_ne (le_of_not_gt hj) (huv j).right_offReal
      exact Or.inr ⟨hn,by simp [base,eta,hj,signAnchor,CMS.signValue]⟩
  have hub j : SameOpenHalfPlane (u j) (base j) := (huv j).trans (hvb j)
  let z := Fin.append (degenerateNumerators p hp u v) (replicateCoordinates q v)
  have hz : z ∈ denominatorDomain (k*p) (repeatedSigns q eta) := by
    intro j
    simp only [z,Fin.append_right,repeatedSigns,replicateCoordinates,eta]
    split_ifs with hj
    · exact of_decide_eq_true hj
    · have hn : ¬ 0 < (v (finProdFinEquiv.symm j).1).im := by
        intro hp
        exact hj (decide_eq_true hp)
      exact lt_of_le_of_ne (le_of_not_gt hn) (huv _).right_offReal
  have h := heq k eta hz
  rw [blockAnchors_repeated] at h
  have hm := expectedChargedObservable_rational_diagonal (μ : Measure AnchoredCountingState)
    hp hrat u v base hub hvb
  have hn := expectedChargedObservable_rational_diagonal (ν : Measure AnchoredCountingState)
    hp hrat u v base hub hvb
  exact hm.symm.trans (h.trans hn)

/-- Equality on the constructed open sectorial chamber already determines the
entire anchored law; all remaining domain continuation is proved analytically. -/
theorem anchored_law_eq_of_rational_sectorial_expectations
    {β : ℝ} (hβ : 0<β) {p q : ℕ} (hp : 0<p) (hrat : β*(q:ℝ)=2*(p:ℝ))
    (μ ν : ProbabilityMeasure AnchoredCountingState) {a b : ℝ}
    (ha : 0<a) (hb : 0<b)
    (hμ : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2))
      (μ : Measure AnchoredCountingState))
    (hν : Integrable (fun s : AnchoredCountingState => Real.exp (b*‖s.val.2‖^2))
      (ν : Measure AnchoredCountingState))
    (heq : ∀ (k : ℕ) (eta : Fin k → Bool),
      EqOn
        (expectedChargedObservable (μ : Measure AnchoredCountingState) (charges β (k*p) (k*q))
          (blockAnchors (repeatedSigns p eta) (repeatedSigns q eta)))
        (expectedChargedObservable (ν : Measure AnchoredCountingState) (charges β (k*p) (k*q))
          (blockAnchors (repeatedSigns p eta) (repeatedSigns q eta)))
        (sectorialChamber hβ (k*p) (repeatedSigns q eta))) : μ=ν := by
  apply anchored_law_eq_of_rational_expectations hp hrat μ ν ha hb hμ hν
  intro k eta
  exact eqOn_denominatorDomain_of_largeChamber _ _ (sectorialRadius hβ (k*p) (k*q))
    (repeatedSigns q eta)
    (analyticOn_expectedChargedObservable (μ : Measure AnchoredCountingState) ha hμ β
      (repeatedSigns p eta) (repeatedSigns q eta))
    (analyticOn_expectedChargedObservable (ν : Measure AnchoredCountingState) hb hν β
      (repeatedSigns p eta) (repeatedSigns q eta))
    (heq k eta)

end BourgadeHuang.RationalBulk
