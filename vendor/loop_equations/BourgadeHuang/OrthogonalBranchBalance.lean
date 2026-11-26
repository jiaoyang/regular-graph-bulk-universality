import BourgadeHuang.OrthogonalSectorialExpansion
import BourgadeHuang.CMS.GeneralBranchDegree
import BourgadeHuang.BalancedRatioMatching

/-! Exact orthogonal charge balance and its positive quadratic branch degree.
Balanced numerator signs admit an actual denominator-pair permutation. -/
noncomputable section
open scoped BigOperators
namespace BourgadeHuang
namespace OrthogonalCMS

def realCharges (q : ℕ) : Fin (q+(q+q)) → ℝ :=
  Fin.append (fun _=> -1) (Fin.append (fun _=>1/2) (fun _=>1/2))

theorem charges_eq_real (q : ℕ) : charges q=fun i=>(realCharges q i:ℂ) := by
  funext i
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · simp only [charges,realCharges,Fin.append_left,Fin.append_right,Complex.ofReal_neg,Complex.ofReal_one]
  · refine Fin.addCases (fun j=>?_) (fun j=>?_) j <;>
      simp only [charges,realCharges,Fin.append_left,Fin.append_right,
        Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]

theorem sum_realCharges (q : ℕ) : (∑i,realCharges q i)=0 := by
  simp only [realCharges,Fin.sum_univ_add,Fin.append_left,Fin.append_right]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

def branchSigns {q : ℕ} (ε η : Fin q → CMS.Sign) : Fin (q+(q+q)) → CMS.Sign :=
  Fin.append ε (Fin.append η η)

theorem sum_realSign {n : ℕ} (σ : Fin n → CMS.Sign) :
    (∑i,CMS.realSign (σ i))=2*(CMS.signCount σ true:ℝ)-n := by
  classical
  have he (i : Fin n) : CMS.realSign (σ i)=2*(if σ i=true then (1:ℝ) else 0)-1 := by
    cases hs : σ i <;> norm_num [CMS.realSign,hs]
  simp_rw [he]
  rw [Finset.sum_sub_distrib,←Finset.mul_sum]
  simp [CMS.signCount]

theorem signedCharge_eq {q : ℕ} (ε η : Fin q → CMS.Sign) :
    (∑i,realCharges q i*CMS.realSign (branchSigns ε η i))=
      2*((CMS.signCount η true:ℝ)-(CMS.signCount ε true:ℝ)) := by
  simp only [realCharges,branchSigns,Fin.sum_univ_add,Fin.append_left,Fin.append_right]
  simp only [neg_one_mul,Finset.sum_neg_distrib,←Finset.mul_sum]
  rw [sum_realSign,sum_realSign]
  ring

/-- The precise degree is twice the square of the sign-count imbalance. -/
theorem branch_degree {q : ℕ} (ε η : Fin q → CMS.Sign) :
    CMS.generalRayDegree 1 (charges q) (branchSigns ε η)=
      ((2*((CMS.signCount η true:ℝ)-(CMS.signCount ε true:ℝ))^2:ℝ):ℂ) := by
  rw [charges_eq_real]
  have he := CMS.generalRayDegree_real (β:=1) (by norm_num : (1:ℝ)≠0)
    (realCharges q) (branchSigns ε η)
  simp only [Complex.ofReal_one] at he
  rw [he,sum_realCharges,signedCharge_eq]
  congr 1
  ring

theorem branch_degree_pos_iff {q : ℕ} (ε η : Fin q → CMS.Sign) :
    0<(CMS.generalRayDegree 1 (charges q) (branchSigns ε η)).re ↔
      CMS.signCount ε true≠CMS.signCount η true := by
  rw [branch_degree,Complex.ofReal_re]
  have he : ((CMS.signCount η true:ℝ)-(CMS.signCount ε true:ℝ))≠0 ↔
      CMS.signCount ε true≠CMS.signCount η true := by
    rw [sub_ne_zero]
    exact not_congr (by norm_cast; exact eq_comm)
  exact (mul_pos_iff_of_pos_left (by norm_num : (0:ℝ)<2)).trans (sq_pos_iff.trans he)

theorem branch_degree_eq_zero {q : ℕ} (ε η : Fin q → CMS.Sign)
    (hb : CMS.signCount ε true=CMS.signCount η true) :
    CMS.generalRayDegree 1 (charges q) (branchSigns ε η)=0 := by
  rw [branch_degree,hb]
  simp

/-- Genuine matching of each balanced numerator to a denominator pair. -/
theorem exists_signMatching {q : ℕ} (ε η : Fin q → CMS.Sign)
    (hb : CMS.signCount ε true=CMS.signCount η true) :
    ∃p : Equiv.Perm (Fin q),∀j,η (p j)=ε j := by
  have hn : CMS.signCount (fun i=> !(ε i)) false=CMS.signCount ε true := by
    unfold CMS.signCount
    congr 1
    ext i
    cases hs : ε i <;> simp [hs]
  obtain ⟨p,hp⟩ := exists_balanced_signMatching (fun i=> !(ε i)) η (hn.trans hb)
  exact ⟨p,fun j=>by simpa using hp j⟩

end OrthogonalCMS
end BourgadeHuang
