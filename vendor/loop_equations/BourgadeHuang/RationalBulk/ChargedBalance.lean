import BourgadeHuang.RationalBulk.ChargedCMSContinuation
import BourgadeHuang.RationalBulk.ChargeReanchoring
import BourgadeHuang.RationalBulk.RationalReplication

noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalBulk

theorem baseBalanced_signAnchor {d : ℕ} (c : Fin d → ℂ) (sigma : Fin d → Bool)
    (hzero : ∑ i, c i = 0) (hsigned : ∑ i, c i * CMS.signValue (sigma i) = 0)
    (height : ℝ) : BaseBalanced c (fun i => signAnchor (sigma i) height) := by
  classical
  intro x
  have h := sum_charge_bool_eq_zero c sigma hzero hsigned
    (fun e => if signAnchor e height = x then 1 else 0)
  simpa only [Finset.sum_filter, mul_ite, mul_one, mul_zero] using h

/-- A block of `p` numerator bases and `q` denominator bases is exactly neutral
at each individual base point when beta/2=p/q. -/
theorem baseBalanced_rational_replication {k p q : ℕ} {β : ℝ}
    (hrat : β*(q:ℝ) = 2*(p:ℝ)) (b : Fin k → ℂ) :
    BaseBalanced (charges β (k*p) (k*q))
      (Fin.append (replicateCoordinates p b) (replicateCoordinates q b)) := by
  classical
  intro x
  simp only [Finset.sum_filter, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
    charges, realCharges, Complex.ofReal_neg, Complex.ofReal_one,
    Complex.ofReal_div, Complex.ofReal_ofNat]
  have hN : (∑ i : Fin (k*p), if replicateCoordinates p b i = x then (-1:ℂ) else 0) =
      -(p:ℂ)*(∑ j : Fin k, if b j = x then (1:ℂ) else 0) := by
    have h := sum_replicateCoordinates p (fun j => if b j = x then (1:ℂ) else 0)
    have he i : (if replicateCoordinates p b i=x then (-1:ℂ) else 0) =
        -(replicateCoordinates p (fun j => if b j=x then (1:ℂ) else 0) i) := by
      simp only [replicateCoordinates]
      split_ifs <;> simp
    simp_rw [he, Finset.sum_neg_distrib]
    rw [h]
    ring
  have hD : (∑ i : Fin (k*q), if replicateCoordinates q b i=x then (β:ℂ)/2 else 0) =
      ((β:ℂ)/2)*(q:ℂ)*(∑ j : Fin k, if b j=x then (1:ℂ) else 0) := by
    have h := sum_replicateCoordinates q (fun j => if b j=x then (1:ℂ) else 0)
    have he i : (if replicateCoordinates q b i=x then (β:ℂ)/2 else 0) =
        ((β:ℂ)/2)*replicateCoordinates q (fun j => if b j=x then (1:ℂ) else 0) i := by
      simp only [replicateCoordinates]
      split_ifs <;> simp
    simp_rw [he, ← Finset.mul_sum]
    rw [h]
    ring
  rw [hN,hD]
  have he : (β:ℂ)*(q:ℂ)=2*(p:ℂ) := by exact_mod_cast hrat
  linear_combination (∑ j : Fin k, if b j=x then (1:ℂ) else 0)/2 * he

/-- Full Proposition 5.1 PDE conclusion for rational replicated blocks, with
all numerator variables holomorphically extended to the complex plane. -/
theorem rationalExpectedObservable_deformedCMS {k p q : ℕ}
    (ν : Measure AnchoredCountingState) (β : ℝ) (hβ : β ≠ 0)
    (hh : ExactHierarchy ν β) {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (hrat : β*(q:ℝ)=2*(p:ℝ)) (b : Fin k → ℂ) (hb : ∀ j, (b j).im ≠ 0)
    (u : Fin (k*p) → ℂ) (v : Fin (k*q) → ℂ)
    (hv : ∀ j, SameOpenHalfPlane (v j) (replicateCoordinates q b j))
    (hfree : CMS.CollisionFree (Fin.append u v)) :
    ∀ i, CMS.deformedOperator (β:ℂ) (charges β (k*p) (k*q)) i
      (expectedChargedObservable ν (charges β (k*p) (k*q))
        (Fin.append (replicateCoordinates p b) (replicateCoordinates q b))) (Fin.append u v) = 0 := by
  apply expectedChargedObservable_deformedCMS_all_numerators ν β hβ hh ha he
    (charges β (k*p) (k*q))
    (Fin.append (replicateCoordinates p b) (replicateCoordinates q b))
    (charges_physical β (k*p) (k*q))
    (by intro j; simp [charges, realCharges]) _
    (baseBalanced_rational_replication hrat b) u v
    (by simpa only [Fin.append_right] using hv) hfree
  intro j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simpa only [Fin.append_left, replicateCoordinates] using hb (finProdFinEquiv.symm j).1
  · simpa only [Fin.append_right, replicateCoordinates] using hb (finProdFinEquiv.symm j).1

end BourgadeHuang.RationalBulk
