import BourgadeHuang.RationalEdge.ChargedProportionality
import BourgadeHuang.RationalEdge.LawDetermination
import BourgadeHuang.RationalBulk.Parameter

/-! Exact edge hierarchy uniqueness at every positive rational beta. The
analytic comparison is obtained from actual charged expectations, and the
diagonal normalization and rational replication determine their full laws. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalEdge
open RationalBulk

theorem anchored_law_eq_of_exactHierarchy_of_multiplicities
    {beta : ℝ} (hbeta : 0<beta) {p q : ℕ} (hp : 0<p)
    (hrat : beta*(q:ℝ)=2*(p:ℝ))
    (mu nu : ProbabilityMeasure AnchoredCountingState)
    (hmu : ExactHierarchy (mu : Measure AnchoredCountingState) beta)
    (hnu : ExactHierarchy (nu : Measure AnchoredCountingState) beta)
    {a b : ℝ} (ha : 0<a) (hb : 0<b)
    (hemu : Integrable (fun s : AnchoredCountingState=>Real.exp (a*‖s.val.2‖^2))
      (mu : Measure AnchoredCountingState))
    (henu : Integrable (fun s : AnchoredCountingState=>Real.exp (b*‖s.val.2‖^2))
      (nu : Measure AnchoredCountingState)) : mu=nu := by
  apply anchored_law_eq_of_rational_local_proportionality hp hrat mu nu ha hb hemu henu
  intro k eta
  by_cases hk : k=0
  · subst k
    letI : IsEmpty (Fin (0*p+0*q)) := ⟨fun i => by have hi:=i.isLt; omega⟩
    let z : CMS.Point (0*p+0*q) := fun _=>0
    refine ⟨1,z,?_,?_⟩
    · intro j
      have hj:=j.isLt
      omega
    · apply Filter.Eventually.of_forall
      intro w
      dsimp only
      have hw : w=blockAnchors (repeatedSigns p eta) (repeatedSigns q eta) :=
        Subsingleton.elim _ _
      rw [hw,expectedChargedObservable_at_bases _ _ _ (fun i=>isEmptyElim i),
        expectedChargedObservable_at_bases _ _ _ (fun i=>isEmptyElim i),mul_one]
  · have hd : 0<k*p+k*q := lt_of_lt_of_le
      (Nat.mul_pos (Nat.pos_of_ne_zero hk) hp) (Nat.le_add_right _ _)
    have hn : ((k*p:ℕ):ℝ)=((k*q:ℕ):ℝ)*beta/2 := by
      push_cast
      linear_combination -(k:ℝ)/2*hrat
    have hbal : beta*(CMS.signCount (repeatedSigns q eta) true:ℝ)=
        2*(CMS.signCount (repeatedSigns p eta) true:ℝ) := by
      rw [signCount_repeated,signCount_repeated]
      push_cast
      linear_combination (CMS.signCount eta true:ℝ)*hrat
    exact expectedChargedObservable_local_proportionality mu nu beta hbeta hmu hnu
      ha hb hemu henu hd (repeatedSigns p eta) (repeatedSigns q eta) hn hbal

/-- Bourgade--Huang edge uniqueness for every positive rational coupling.
The only analytic hypotheses are the exact edge hierarchy and the stated
exponential-square integrability of the anchored transform. -/
theorem anchored_law_eq_of_exactHierarchy_rational
    (beta : ℚ) (hbeta : 0<beta)
    (mu nu : ProbabilityMeasure AnchoredCountingState)
    (hmu : ExactHierarchy (mu : Measure AnchoredCountingState) (beta:ℝ))
    (hnu : ExactHierarchy (nu : Measure AnchoredCountingState) (beta:ℝ))
    {a b : ℝ} (ha : 0<a) (hb : 0<b)
    (hemu : Integrable (fun s : AnchoredCountingState=>Real.exp (a*‖s.val.2‖^2))
      (mu : Measure AnchoredCountingState))
    (henu : Integrable (fun s : AnchoredCountingState=>Real.exp (b*‖s.val.2‖^2))
      (nu : Measure AnchoredCountingState)) : mu=nu := by
  obtain ⟨p,q,hp,_,hrat⟩ := exists_positive_charge_multiplicities beta hbeta
  exact anchored_law_eq_of_exactHierarchy_of_multiplicities
    (by exact_mod_cast hbeta) hp hrat mu nu hmu hnu ha hb hemu henu

theorem counting_law_eq_of_exactHierarchy_rational
    (beta : ℚ) (hbeta : 0<beta)
    (mu nu : ProbabilityMeasure AnchoredCountingState)
    (hmu : ExactHierarchy (mu : Measure AnchoredCountingState) (beta:ℝ))
    (hnu : ExactHierarchy (nu : Measure AnchoredCountingState) (beta:ℝ))
    {a b : ℝ} (ha : 0<a) (hb : 0<b)
    (hemu : Integrable (fun s : AnchoredCountingState=>Real.exp (a*‖s.val.2‖^2))
      (mu : Measure AnchoredCountingState))
    (henu : Integrable (fun s : AnchoredCountingState=>Real.exp (b*‖s.val.2‖^2))
      (nu : Measure AnchoredCountingState)) : anchoredCountingLaw mu=anchoredCountingLaw nu :=
  congrArg anchoredCountingLaw
    (anchored_law_eq_of_exactHierarchy_rational beta hbeta mu nu hmu hnu ha hb hemu henu)

end BourgadeHuang.RationalEdge
