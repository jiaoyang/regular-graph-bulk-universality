import BourgadeHuang.RationalBulk.ChargedSectorial
import BourgadeHuang.RationalBulk.ChargedTwoScaleNormalization

/-! Actual balanced comparison limits, with the original global numerator
anchors retained through a proved finite permutation identity. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalBulk

theorem expectedChargedObservable_balanced_twoScale_normalized {n m : ℕ}
    (nu : Measure AnchoredCountingState) [IsProbabilityMeasure nu]
    (beta : ℝ) (hh : ExactHierarchy nu beta) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState=>Real.exp (a*‖s.val.2‖^2)) nu)
    (theta epsilon : Fin n → Bool) (eta : Fin m → Bool)
    (hn : (n:ℝ)=(m:ℝ)*beta/2)
    (htheta : beta*(CMS.signCount eta true:ℝ)=2*(CMS.signCount theta true:ℝ))
    (hepsilon : beta*(CMS.signCount eta true:ℝ)=2*(CMS.signCount epsilon true:ℝ))
    (xi : Fin (n+m) → ℝ) :
    Tendsto (fun r : ℝ=>Complex.exp (-CMS.generalRayPhase (charges beta n m) (Fin.append epsilon eta)
        (CMS.twoScaleRay xi (Fin.append (fun _=>1) (fun _=> -1)) (Fin.append epsilon eta) 2 r))*
      expectedChargedObservable nu (charges beta n m) (blockAnchors theta eta)
        (CMS.twoScaleRay xi (Fin.append (fun _=>1) (fun _=> -1)) (Fin.append epsilon eta) 2 r))
      atTop (𝓝 1) := by
  have hzero : (∑i,realCharges beta n m i)=0 := by rw [sum_realCharges,hn]; ring
  have hsign : (∑i,realCharges beta n m i*CMS.realSign (Fin.append epsilon eta i))=0 := by
    rw [signedCharge_neutral beta hn,hepsilon]
    ring
  have hdelta (i : Fin (n+m)) : |Fin.append (fun _ : Fin n =>(1:ℝ)) (fun _ : Fin m => -1) i|≤1 := by
    refine Fin.addCases (fun j=>?_) (fun j=>?_) i <;> simp
  have hcount : CMS.signCount theta true=CMS.signCount epsilon true := by
    have hc : (CMS.signCount theta true:ℝ)=(CMS.signCount epsilon true:ℝ) := by linarith
    exact_mod_cast hc
  have hlim := expectedChargedObservable_twoScale_normalized nu beta hh ha he
    (realCharges beta n m) xi (Fin.append (fun _=>1) (fun _=> -1)) (Fin.append epsilon eta)
    hzero hsign hdelta
  apply hlim.congr'
  apply Eventually.of_forall
  intro r
  change Complex.exp (-CMS.generalRayPhase (charges beta n m) (Fin.append epsilon eta) _)*_=_
  rw [←blockAnchors_eq_signAnchor epsilon eta]
  exact congrArg (fun w=>Complex.exp (-CMS.generalRayPhase (charges beta n m) (Fin.append epsilon eta)
    (CMS.twoScaleRay xi (Fin.append (fun _=>1) (fun _=> -1)) (Fin.append epsilon eta) 2 r))*w)
      (expectedChargedObservable_eq_of_numerator_base_count nu beta theta epsilon eta hcount _).symm

end BourgadeHuang.RationalBulk
