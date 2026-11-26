import BourgadeHuang.RationalEdge.ChargedCMSContinuation
import BourgadeHuang.RationalBulk.ChargedSectorial

/-! Actual edge hierarchy expectations solve the genuine edge CMS system
on every sufficiently separated chamber with the prescribed denominator signs. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Set
namespace BourgadeHuang.RationalEdge
open RationalBulk

/-- The exact edge equations hold at every collision-free point of the
actual denominator domain, with no ordering restriction on numerators. -/
theorem expectedChargedObservable_edgeOperator_eq_zero {n m : ℕ}
    (nu : Measure AnchoredCountingState) (beta : ℝ) (hbeta : 0<beta)
    (hh : ExactHierarchy nu beta) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState=>Real.exp (a*‖s.val.2‖^2)) nu)
    (theta : Fin n → Bool) (eta : Fin m → Bool)
    (hn : (n:ℝ)=(m:ℝ)*beta/2)
    (hbal : beta*(CMS.signCount eta true:ℝ)=2*(CMS.signCount theta true:ℝ))
    {z : CMS.Point (n+m)} (hz : z∈denominatorDomain n eta)
    (hfree : CMS.CollisionFree z) (i : Fin (n+m)) :
    EdgeCMS.edgeOperator (beta:ℂ) (charges beta n m) i
      (expectedChargedObservable nu (charges beta n m) (blockAnchors theta eta)) z=0 := by
  let u : Fin n → ℂ := fun i=>z (Fin.castAdd m i)
  let v : Fin m → ℂ := fun j=>z (Fin.natAdd n j)
  have happ : Fin.append u v=z := by
    funext i
    refine Fin.addCases (fun i=>?_) (fun j=>?_) i <;> simp [u,v]
  have hdom := chargedDomain_of_denominatorDomain beta theta eta z hz
  have hcN i : charges beta n m (Fin.castAdd m i)= -1 := by simp [charges,realCharges]
  have hv j : SameOpenHalfPlane (v j) (blockAnchors theta eta (Fin.natAdd n j)) := by
    apply hdom.2
    simp only [charges,realCharges,Fin.append_right,Complex.ofReal_div,Complex.ofReal_ofNat]
    intro hf
    have hfr := congrArg Complex.re hf
    simp at hfr
    linarith
  have h := expectedChargedObservable_deformedCMS_all_numerators nu beta hbeta.ne' hh ha he
    (charges beta n m) (blockAnchors theta eta) (charges_physical beta n m) hcN
    hdom.1 (blockAnchors_balanced theta eta hn hbal) u v hv (by simpa [happ] using hfree)
  simpa only [happ] using h i

/-- The actual expectation solves edge CMS on any collision-free subdomain.
This includes the concrete Airy-coordinate comparison chamber. -/
theorem expectedChargedObservable_domain_solution {n m : ℕ}
    (nu : Measure AnchoredCountingState) (beta : ℝ) (hbeta : 0<beta)
    (hh : ExactHierarchy nu beta) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState=>Real.exp (a*‖s.val.2‖^2)) nu)
    (theta : Fin n → Bool) (eta : Fin m → Bool)
    (hn : (n:ℝ)=(m:ℝ)*beta/2)
    (hbal : beta*(CMS.signCount eta true:ℝ)=2*(CMS.signCount theta true:ℝ))
    (U : Set (CMS.Point (n+m))) (hsub : U⊆denominatorDomain n eta)
    (hfree : ∀z∈U,CMS.CollisionFree z) :
    AnalyticOnNhd ℂ (expectedChargedObservable nu (charges beta n m) (blockAnchors theta eta)) U ∧
    ∀z∈U,∀i, EdgeCMS.edgeOperator (beta:ℂ) (charges beta n m) i
      (expectedChargedObservable nu (charges beta n m) (blockAnchors theta eta)) z=0 :=
  ⟨(analyticOn_expectedChargedObservable nu ha he beta theta eta).mono hsub,
    fun z hz i => expectedChargedObservable_edgeOperator_eq_zero nu beta hbeta hh ha he
      theta eta hn hbal (hsub hz) (hfree z hz) i⟩

theorem expectedChargedObservable_largeChamber_solution {n m : ℕ}
    (nu : Measure AnchoredCountingState) (beta : ℝ) (hbeta : 0<beta)
    (hh : ExactHierarchy nu beta) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState=>Real.exp (a*‖s.val.2‖^2)) nu)
    (theta : Fin n → Bool) (eta : Fin m → Bool)
    (R : ℝ) (hR : 0≤R)
    (hn : (n:ℝ)=(m:ℝ)*beta/2)
    (hbal : beta*(CMS.signCount eta true:ℝ)=2*(CMS.signCount theta true:ℝ)) :
    AnalyticOnNhd ℂ (expectedChargedObservable nu (charges beta n m) (blockAnchors theta eta))
      (largeChamber n R eta) ∧
    ∀z∈largeChamber n R eta,∀i,
      EdgeCMS.edgeOperator (beta:ℂ) (charges beta n m) i
        (expectedChargedObservable nu (charges beta n m) (blockAnchors theta eta)) z=0 := by
  have hsub := largeChamber_subset_denominatorDomain (n:=n) R eta
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
      exact CMS.orderedGapMixedDomain_collisionFree hR hz
    have h := expectedChargedObservable_deformedCMS_all_numerators nu beta hbeta.ne' hh ha he
      (charges beta n m) (blockAnchors theta eta) (charges_physical beta n m) hcN
      hdom.1 (blockAnchors_balanced theta eta hn hbal) u v hv hfree
    simpa only [happ] using h


end BourgadeHuang.RationalEdge
