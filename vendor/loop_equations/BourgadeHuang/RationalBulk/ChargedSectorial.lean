import BourgadeHuang.RationalBulk.ChargedBalance
import BourgadeHuang.RationalBulk.NumeratorReanchoring
import BourgadeHuang.RationalSectorialExpansion

/-! The actual rational charged expectation in the constructed physical CMS
basis. All analytic and PDE hypotheses are proved from the exact hierarchy. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Set
namespace BourgadeHuang.RationalBulk

@[simp] theorem signAnchor_offReal (sigma : Bool) : (signAnchor sigma 1).im≠0 := by
  cases sigma <;> simp [signAnchor,CMS.signValue]

theorem blockAnchors_eq_signAnchor {n m : ℕ} (theta : Fin n → Bool) (eta : Fin m → Bool) :
    blockAnchors theta eta = fun i=>signAnchor (Fin.append theta eta i) 1 := by
  funext i
  refine Fin.addCases (fun i=>?_) (fun j=>?_) i <;> simp [blockAnchors]

theorem blockAnchors_balanced {n m : ℕ} {beta : ℝ}
    (theta : Fin n → Bool) (eta : Fin m → Bool)
    (hn : (n:ℝ)=(m:ℝ)*beta/2)
    (hbal : beta*(CMS.signCount eta true:ℝ)=2*(CMS.signCount theta true:ℝ)) :
    BaseBalanced (charges beta n m) (blockAnchors theta eta) := by
  rw [blockAnchors_eq_signAnchor]
  apply baseBalanced_signAnchor
  · unfold charges
    rw [←Complex.ofReal_sum,sum_realCharges,hn]
    simp
  · unfold charges
    simp only [←CMS.ofReal_realSign,←Complex.ofReal_mul,←Complex.ofReal_sum]
    rw [signedCharge_neutral beta hn,hbal]
    simp

theorem chargedDomain_of_denominatorDomain {n m : ℕ} (beta : ℝ)
    (theta : Fin n → Bool) (eta : Fin m → Bool) (z : CMS.Point (n+m))
    (hz : z∈denominatorDomain n eta) :
    ChargedDomain (charges beta n m) (blockAnchors theta eta) z := by
  refine ⟨?_,?_⟩
  · intro i
    rw [blockAnchors_eq_signAnchor]
    exact signAnchor_offReal _
  · intro i
    refine Fin.addCases (fun i=>?_) (fun j=>?_) i
    · intro h
      exact (h (by simp [charges,realCharges])).elim
    · intro _
      have hj := hz j
      cases hs : eta j <;> simp only [hs,Bool.false_eq_true,↓reduceIte] at hj
      · exact Or.inr ⟨hj,by simp [blockAnchors,signAnchor,CMS.signValue,hs]⟩
      · exact Or.inl ⟨hj,by simp [blockAnchors,signAnchor,CMS.signValue,hs]⟩

theorem analyticOn_expectedChargedObservable {n m : ℕ}
    (nu : Measure AnchoredCountingState) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState=>Real.exp (a*‖s.val.2‖^2)) nu)
    (beta : ℝ) (theta : Fin n → Bool) (eta : Fin m → Bool) :
    AnalyticOnNhd ℂ (expectedChargedObservable nu (charges beta n m) (blockAnchors theta eta))
      (denominatorDomain n eta) := by
  intro z hz
  exact analyticAt_expectedChargedObservable nu ha he _ _ _
    (chargedDomain_of_denominatorDomain beta theta eta z hz)

theorem expectedChargedObservable_sectorial_solution {n m : ℕ}
    (nu : Measure AnchoredCountingState) (beta : ℝ) (hbeta : 0<beta)
    (hh : ExactHierarchy nu beta) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState=>Real.exp (a*‖s.val.2‖^2)) nu)
    (theta : Fin n → Bool) (eta : Fin m → Bool)
    (hn : (n:ℝ)=(m:ℝ)*beta/2)
    (hbal : beta*(CMS.signCount eta true:ℝ)=2*(CMS.signCount theta true:ℝ)) :
    AnalyticOnNhd ℂ (expectedChargedObservable nu (charges beta n m) (blockAnchors theta eta))
      (sectorialChamber hbeta n eta) ∧
    ∀z∈sectorialChamber hbeta n eta,∀i,
      CMS.deformedOperator (beta:ℂ) (charges beta n m) i
        (expectedChargedObservable nu (charges beta n m) (blockAnchors theta eta)) z=0 := by
  have hsub := largeChamber_subset_denominatorDomain (n:=n) (sectorialRadius hbeta n m) eta
  constructor
  · exact (analyticOn_expectedChargedObservable nu ha he beta theta eta).mono hsub
  · intro z hz
    let u : Fin n → ℂ := fun i=>z (Fin.castAdd m i)
    let v : Fin m → ℂ := fun j=>z (Fin.natAdd n j)
    have happ : Fin.append u v=z := by
      funext i
      refine Fin.addCases (fun i=>?_) (fun j=>?_) i <;> simp [u,v]
    have hdom := chargedDomain_of_denominatorDomain beta theta eta z (hsub hz)
    have hcN i : charges beta n m (Fin.castAdd m i)= -1 := by simp [charges,realCharges]
    have hv j : SameOpenHalfPlane (v j) (blockAnchors theta eta (Fin.natAdd n j)) := by
      apply hdom.2
      simp only [charges,realCharges,Fin.append_right,Complex.ofReal_div,Complex.ofReal_ofNat]
      intro hf
      have hfr := congrArg Complex.re hf
      simp at hfr
      linarith
    have hfree : CMS.CollisionFree (Fin.append u v) := by
      rw [happ]
      exact CMS.orderedGapMixedDomain_collisionFree (sectorialRadius_pos hbeta).le hz
    have h := expectedChargedObservable_deformedCMS_all_numerators nu beta hbeta.ne' hh ha he
      (charges beta n m) (blockAnchors theta eta) (charges_physical beta n m) hcN
      hdom.1 (blockAnchors_balanced theta eta hn hbal) u v hv hfree
    simpa only [happ] using h

theorem existsUnique_charged_sectorial_expansion {n m : ℕ}
    (nu : Measure AnchoredCountingState) (beta : ℝ) (hbeta : 0<beta)
    (hh : ExactHierarchy nu beta) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState=>Real.exp (a*‖s.val.2‖^2)) nu)
    (theta : Fin n → Bool) (eta : Fin m → Bool)
    (hn : (n:ℝ)=(m:ℝ)*beta/2)
    (hbal : beta*(CMS.signCount eta true:ℝ)=2*(CMS.signCount theta true:ℝ)) :
    ∃!b : (Fin (n+m) → CMS.Sign) → ℂ,
      EqOn (expectedChargedObservable nu (charges beta n m) (blockAnchors theta eta))
        (fun z=>∑sigma,b sigma*sectorialBranch hbeta sigma z) (sectorialChamber hbeta n eta) := by
  have hsol := expectedChargedObservable_sectorial_solution nu beta hbeta hh ha he theta eta hn hbal
  exact existsUnique_sectorial_expansion hbeta _ eta hsol.1 hsol.2

def chargedCoefficients {n m : ℕ}
    (nu : Measure AnchoredCountingState) (beta : ℝ) (hbeta : 0<beta)
    (hh : ExactHierarchy nu beta) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState=>Real.exp (a*‖s.val.2‖^2)) nu)
    (theta : Fin n → Bool) (eta : Fin m → Bool)
    (hn : (n:ℝ)=(m:ℝ)*beta/2)
    (hbal : beta*(CMS.signCount eta true:ℝ)=2*(CMS.signCount theta true:ℝ)) :
    (Fin (n+m) → CMS.Sign) → ℂ :=
  (existsUnique_charged_sectorial_expansion nu beta hbeta hh ha he theta eta hn hbal).choose

theorem chargedCoefficients_spec {n m : ℕ}
    (nu : Measure AnchoredCountingState) (beta : ℝ) (hbeta : 0<beta)
    (hh : ExactHierarchy nu beta) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState=>Real.exp (a*‖s.val.2‖^2)) nu)
    (theta : Fin n → Bool) (eta : Fin m → Bool)
    (hn : (n:ℝ)=(m:ℝ)*beta/2)
    (hbal : beta*(CMS.signCount eta true:ℝ)=2*(CMS.signCount theta true:ℝ)) :
    EqOn (expectedChargedObservable nu (charges beta n m) (blockAnchors theta eta))
      (fun z=>∑sigma,chargedCoefficients nu beta hbeta hh ha he theta eta hn hbal sigma*
        sectorialBranch hbeta sigma z) (sectorialChamber hbeta n eta) :=
  (existsUnique_charged_sectorial_expansion nu beta hbeta hh ha he theta eta hn hbal).choose_spec.1

end BourgadeHuang.RationalBulk
