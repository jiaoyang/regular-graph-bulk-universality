import BourgadeHuang.RationalBulk.ChargeReanchoring
import BourgadeHuang.RationalChargeMatching

/-! The global charged observable has no dependence on how same-half-plane
base points are assigned to its numerator coordinates. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace BourgadeHuang.RationalBulk

def blockAnchors {n m : ℕ} (theta : Fin n → Bool) (eta : Fin m → Bool) :
    Fin (n+m) → ℂ :=
  Fin.append (fun i=>signAnchor (theta i) 1) (fun j=>signAnchor (eta j) 1)

theorem chargedObservable_permute_numerator_bases {n m : ℕ}
    (beta : ℝ) (theta : Fin n → Bool) (eta : Fin m → Bool)
    (e : Equiv.Perm (Fin n)) (s : AnchoredCountingState) (z : Fin (n+m) → ℂ) :
    chargedObservable (charges beta n m) (blockAnchors (fun i=>theta (e i)) eta) s z =
      chargedObservable (charges beta n m) (blockAnchors theta eta) s z := by
  simp only [chargedObservable,Fin.prod_univ_add,charges,realCharges,blockAnchors,
    Fin.append_left,Fin.append_right,Complex.ofReal_neg,Complex.ofReal_one]
  congr 1
  simp only [chargedFactor,if_true,entireCharacteristicRatio,Finset.prod_div_distrib]
  rw [Equiv.prod_comp e (fun i=>anchoredEntireNumerator s (signAnchor (theta i) 1))]

theorem chargedObservable_eq_of_numerator_base_count {n m : ℕ}
    (beta : ℝ) (theta epsilon : Fin n → Bool) (eta : Fin m → Bool)
    (hcount : CMS.signCount theta true=CMS.signCount epsilon true)
    (s : AnchoredCountingState) (z : Fin (n+m) → ℂ) :
    chargedObservable (charges beta n m) (blockAnchors theta eta) s z =
      chargedObservable (charges beta n m) (blockAnchors epsilon eta) s z := by
  obtain ⟨e,he⟩ := OrthogonalCMS.exists_signMatching epsilon theta hcount.symm
  have hfun : (fun i=>theta (e i))=epsilon := funext he
  have hp := chargedObservable_permute_numerator_bases beta theta eta e s z
  rw [hfun] at hp
  exact hp.symm

theorem expectedChargedObservable_eq_of_numerator_base_count {n m : ℕ}
    (nu : Measure AnchoredCountingState) (beta : ℝ)
    (theta epsilon : Fin n → Bool) (eta : Fin m → Bool)
    (hcount : CMS.signCount theta true=CMS.signCount epsilon true)
    (z : Fin (n+m) → ℂ) :
    expectedChargedObservable nu (charges beta n m) (blockAnchors theta eta) z =
      expectedChargedObservable nu (charges beta n m) (blockAnchors epsilon eta) z := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun s=>chargedObservable_eq_of_numerator_base_count
    beta theta epsilon eta hcount s z)

end BourgadeHuang.RationalBulk
