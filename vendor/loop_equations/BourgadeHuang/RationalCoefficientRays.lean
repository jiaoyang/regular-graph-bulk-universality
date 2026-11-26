import BourgadeHuang.RationalChargeGeometry

/-! Denominator sign separation for all positive couplings. Scaling each
imaginary denominator coordinate by `1/beta` preserves the binary phase code. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace BourgadeHuang.RationalBulk
variable {n m : ℕ}

def coefficientDirection (beta : ℝ) (n : ℕ) (eta : Fin m → CMS.Sign) : CMS.Point (n+m) :=
  Fin.append (fun i : Fin n => (i.val:ℂ)+Complex.I*((2:ℝ)^i.val:ℂ))
    (fun j : Fin m => ((n+j.val:ℕ):ℂ)+
      Complex.I*(CMS.realSign (eta j)*(2:ℝ)^(n+j.val+1)/beta:ℝ))

@[simp] theorem coefficientDirection_re (beta : ℝ) (eta : Fin m → CMS.Sign)
    (i : Fin (n+m)) : (coefficientDirection beta n eta i).re = i.val := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · simp [coefficientDirection]
  · cases hs : eta j <;> simp [coefficientDirection, hs, CMS.realSign, CMS.signValue]

theorem coefficientDirection_ordered (beta : ℝ) (eta : Fin m → CMS.Sign) :
    coefficientDirection beta n eta ∈ CMS.OrderedDomain (n+m) := by
  intro i j hij
  simp only [coefficientDirection_re]
  exact_mod_cast hij

theorem coefficientDirection_phase {beta : ℝ} (hbeta : beta ≠ 0)
    (eta : Fin m → CMS.Sign) (sigma : Fin (n+m) → CMS.Sign) :
    (CMS.generalRayPhase (charges beta n m) sigma (coefficientDirection beta n eta)).re =
      (CMS.generalRayPhase (CMS.binaryCharges n m) sigma (CMS.binaryChargeDirection n eta)).re := by
  rw [CMS.generalRayPhase_binary_re]
  unfold CMS.generalRayPhase
  rw [Finset.mul_sum, Complex.re_sum, Fin.sum_univ_add, sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  apply congrArg₂ (·+·)
  · apply Finset.sum_congr rfl
    intro i _
    cases hs : sigma (Fin.castAdd m i) <;>
      simp [charges,realCharges,coefficientDirection,hs,CMS.signValue,CMS.realSign,
        Complex.mul_re,Complex.mul_im]
  · apply Finset.sum_congr rfl
    intro j _
    cases hs : sigma (Fin.natAdd n j) <;> cases ht : eta j <;>
      simp [charges,realCharges,coefficientDirection,hs,ht,CMS.signValue,CMS.realSign,
        Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im,pow_succ] <;>
      field_simp <;> ring

theorem coefficientDirection_phase_injective {beta : ℝ} (hbeta : beta ≠ 0)
    (eta : Fin m → CMS.Sign) :
    Function.Injective (fun sigma : Fin (n+m) → CMS.Sign =>
      (CMS.generalRayPhase (charges beta n m) sigma (coefficientDirection beta n eta)).re) := by
  intro sigma tau h
  simp only [coefficientDirection_phase hbeta] at h
  exact CMS.generalRayPhase_binary_injective eta h

theorem coefficientDirection_wrong_denominator {beta : ℝ} (hbeta : beta ≠ 0)
    (eta : Fin m → CMS.Sign) (sigma : Fin (n+m) → CMS.Sign)
    (hwrong : ∃j,sigma (Fin.natAdd n j)≠eta j) :
    CMS.binaryObservableRate n m <
      (CMS.generalRayPhase (charges beta n m) sigma (coefficientDirection beta n eta)).re := by
  rw [coefficientDirection_phase hbeta]
  exact CMS.generalRayPhase_binary_gt_observable_of_wrong_denominator eta sigma hwrong

/-- A proved exponential observable bound removes all wrong denominator signs
from the genuinely constructed physical CMS expansion at every positive beta. -/
theorem physical_expansion_denominator_support {beta : ℝ} (hbeta : 0<beta)
    (eta : Fin m → CMS.Sign) (a : (Fin (n+m) → CMS.Sign) → ℂ) (F : ℝ → ℂ) (C : ℝ)
    (hexp : ∀ᶠr : ℝ in atTop,F r=∑sigma,a sigma*
      CMS.RadialConstructionData.physicalBranch hbeta (charges beta n m) sigma
        (charges_physical beta n m) (fun i=>(r:ℂ)*coefficientDirection beta n eta i))
    (hbound : ∀ᶠr : ℝ in atTop,‖F r‖≤C*Real.exp (r*CMS.binaryObservableRate n m)) :
    ∀sigma,(∃j,sigma (Fin.natAdd n j)≠eta j) → a sigma=0 := by
  intro sigma hsigma
  exact CMS.RadialConstructionData.physical_expansion_phase_support
    hbeta (charges beta n m) (charges_physical beta n m)
    (coefficientDirection beta n eta) (coefficientDirection_ordered beta eta)
    (coefficientDirection_phase_injective hbeta.ne' eta) a F (CMS.binaryObservableRate n m) C
    hexp hbound sigma (coefficientDirection_wrong_denominator hbeta.ne' eta sigma hsigma)

end BourgadeHuang.RationalBulk
