import BourgadeHuang.OrthogonalBranchBalance
import BourgadeHuang.OrthogonalRatioMatching

/-! Exact equality of the matched observable phase and the negative phase of
the distinguished physical CMS branch. The matching permutes both genuine
square-root denominator blocks simultaneously. -/
noncomputable section
open scoped BigOperators
namespace BourgadeHuang
namespace OrthogonalCMS

theorem generalRayPhase_branchSigns {q : ℕ} (ε η : Fin q → CMS.Sign)
    (z : CMS.Point (q+(q+q))) :
    CMS.generalRayPhase (charges q) (branchSigns ε η) z=
      Complex.I*(-(∑j,CMS.signValue (ε j)*z (numeratorIndex j))+
        (1/2:ℂ)*(∑j,CMS.signValue (η j)*z (firstDenominatorIndex j))+
        (1/2:ℂ)*(∑j,CMS.signValue (η j)*z (secondDenominatorIndex j))) := by
  unfold CMS.generalRayPhase
  rw [Fin.sum_univ_add,Fin.sum_univ_add]
  simp only [charges,branchSigns,Fin.append_left,Fin.append_right,
    numeratorIndex,firstDenominatorIndex,secondDenominatorIndex,neg_one_mul,
    neg_mul,Finset.sum_neg_distrib,mul_assoc,←Finset.mul_sum]
  ring

/-- Actual phase matching, including the coherent denominator pairing. -/
theorem signedOrthogonalRatioPhase_sum_eq {q : ℕ} (ε η : Fin q → CMS.Sign)
    (p : Equiv.Perm (Fin q)) (hp : ∀j,η (p j)=ε j)
    (z : CMS.Point (q+(q+q))) :
    (∑j,signedOrthogonalRatioPhase (ε j) (z (numeratorIndex j))
      (z (firstDenominatorIndex (p j))) (z (secondDenominatorIndex (p j))))=
      -CMS.generalRayPhase (charges q) (branchSigns ε η) z := by
  have he (j : Fin q) :
      signedOrthogonalRatioPhase (ε j) (z (numeratorIndex j))
        (z (firstDenominatorIndex (p j))) (z (secondDenominatorIndex (p j)))=
      Complex.I*(CMS.signValue (ε j)*z (numeratorIndex j))-
        (Complex.I/2)*(CMS.signValue (η (p j))*z (firstDenominatorIndex (p j)))-
        (Complex.I/2)*(CMS.signValue (η (p j))*z (secondDenominatorIndex (p j))) := by
    rw [hp j]
    cases hs : ε j <;> simp only [signedOrthogonalRatioPhase,signedRatioPhase,hs,
      Bool.false_eq_true,↓reduceIte,CMS.signValue_false,CMS.signValue_true] <;> ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.mul_sum,←Finset.mul_sum,
    Equiv.sum_comp p (fun j=>CMS.signValue (η j)*z (firstDenominatorIndex j)),
    Equiv.sum_comp p (fun j=>CMS.signValue (η j)*z (secondDenominatorIndex j)),
    generalRayPhase_branchSigns]
  ring

end OrthogonalCMS
end BourgadeHuang
