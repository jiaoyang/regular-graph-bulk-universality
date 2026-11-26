import BourgadeHuang.RationalSectorialExpansion
import BourgadeHuang.RationalCoefficientRays
import BourgadeHuang.CMS.TwoScaleCoefficientSelection

/-! Coefficient determination for neutral general-beta CMS observables.
The finite sectorial solution space, phase suppression, and branch degree are
proved. The observable-specific growth and normalization estimates are explicit
inputs here and are discharged separately for expected characteristic ratios. -/
noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace BourgadeHuang.RationalBulk
variable {n m : ℕ} {beta : ℝ}

private theorem zero_offset_eq_append :
    (fun _ : Fin (n+m) => (0:ℝ)) =
      Fin.append (fun _ : Fin n => (0:ℝ)) (fun _ : Fin m => (0:ℝ)) := by
  funext i
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i <;> simp

/-- Positive signed charge degree removes all unbalanced numerator signs. -/
theorem coefficient_unbalanced_eq_zero (hbeta : 0<beta)
    (hn : (n:ℝ)=(m:ℝ)*beta/2) (eta : Fin m → CMS.Sign)
    (F : CMS.Point (n+m) → ℂ) (a : (Fin (n+m) → CMS.Sign) → ℂ)
    (hexp : EqOn F (fun z=>∑sigma,a sigma*sectorialBranch hbeta sigma z)
      (sectorialChamber hbeta n eta))
    (hsupport : ∀sigma,a sigma≠0 → ∀j,sigma (Fin.natAdd n j)=eta j)
    (epsilon : Fin n → CMS.Sign)
    (hbal : beta*(CMS.signCount eta true:ℝ)≠2*(CMS.signCount epsilon true:ℝ))
    (hbound : ∃C : ℝ,∀ᶠr : ℝ in atTop,
      ‖F (CMS.twoScaleRay (fun i=>(i.val:ℝ)) (fun _=>0) (Fin.append epsilon eta) 0 r)‖≤C) :
    a (Fin.append epsilon eta)=0 := by
  let xi : Fin (n+m) → ℝ := fun i=>(i.val:ℝ)
  have hxi : StrictMono xi := by
    intro i j hij
    dsimp [xi]
    exact_mod_cast (show i.val < j.val from hij)
  apply CMS.RadialConstructionData.physical_coefficient_zero_of_twoScale_bounded
    hbeta (charges beta n m) (charges_physical beta n m)
    xi (fun _=>0) (Fin.append epsilon eta) 0 hxi a ?_
    (fun r=>F (CMS.twoScaleRay xi (fun _=>0) (Fin.append epsilon eta) 0 r)) ?_ ?_ ?_ hbound
  · intro tau htau hne
    simpa only [←zero_offset_eq_append] using
      twoScalePhase_gap beta xi epsilon eta 0 0 0 tau (by rfl) (hsupport tau htau) hne
  · filter_upwards [twoScaleRay_eventually_sectorialChamber hbeta xi (fun _=>0) epsilon eta 0 hxi]
      with r hr
    exact hexp hr
  · exact Filter.Eventually.of_forall (fun r=>twoScalePhase_neutral_zero beta hn xi epsilon eta 0 r)
  · exact (branch_degree_pos_iff hbeta hn epsilon eta).mpr hbal

/-- Zero signed charge degree plus matched two-scale normalization gives the
universal, nonzero branch coefficient for every positive beta. -/
theorem coefficient_balanced_eq (hbeta : 0<beta)
    (hn : (n:ℝ)=(m:ℝ)*beta/2) (eta : Fin m → CMS.Sign)
    (F : CMS.Point (n+m) → ℂ) (a : (Fin (n+m) → CMS.Sign) → ℂ)
    (hexp : EqOn F (fun z=>∑sigma,a sigma*sectorialBranch hbeta sigma z)
      (sectorialChamber hbeta n eta))
    (hsupport : ∀sigma,a sigma≠0 → ∀j,sigma (Fin.natAdd n j)=eta j)
    (epsilon : Fin n → CMS.Sign)
    (hbal : beta*(CMS.signCount eta true:ℝ)=2*(CMS.signCount epsilon true:ℝ))
    (hlimit : Tendsto (fun r : ℝ=>
      Complex.exp (-CMS.generalRayPhase (charges beta n m) (Fin.append epsilon eta)
        (CMS.twoScaleRay (fun i=>(i.val:ℝ)) (Fin.append (fun _=>1) (fun _=> -1))
          (Fin.append epsilon eta) 2 r))*
      F (CMS.twoScaleRay (fun i=>(i.val:ℝ)) (Fin.append (fun _=>1) (fun _=> -1))
        (Fin.append epsilon eta) 2 r)) atTop (𝓝 1)) :
    a (Fin.append epsilon eta)=
      (CMS.twoScaleBranchConstant (beta:ℂ) (charges beta n m) (Fin.append epsilon eta))⁻¹ := by
  let xi : Fin (n+m) → ℝ := fun i=>(i.val:ℝ)
  have hxi : StrictMono xi := by
    intro i j hij
    dsimp [xi]
    exact_mod_cast (show i.val < j.val from hij)
  apply CMS.RadialConstructionData.physical_coefficient_eq_inv_of_twoScale_phase_limit
    hbeta (charges beta n m) (charges_physical beta n m)
    xi (Fin.append (fun _=>1) (fun _=> -1)) (Fin.append epsilon eta) 2 hxi a ?_
    (fun r=>F (CMS.twoScaleRay xi (Fin.append (fun _=>1) (fun _=> -1))
      (Fin.append epsilon eta) 2 r)) ?_ ?_ hlimit
  · intro tau htau hne
    exact twoScalePhase_gap beta xi epsilon eta 1 (-1) 2 tau zero_le_one (hsupport tau htau) hne
  · filter_upwards [twoScaleRay_eventually_sectorialChamber hbeta xi
      (Fin.append (fun _=>1) (fun _=> -1)) epsilon eta 2 hxi] with r hr
    exact hexp hr
  · exact branch_degree_zero hbeta hn epsilon eta hbal

/-- Prescribed denominator signs reduce comparison to numerator sign patterns. -/
theorem coefficients_eq_of_numerator_comparison
    (eta : Fin m → CMS.Sign) (a b : (Fin (n+m) → CMS.Sign) → ℂ)
    (ha : ∀sigma,(∃j,sigma (Fin.natAdd n j)≠eta j) → a sigma=0)
    (hb : ∀sigma,(∃j,sigma (Fin.natAdd n j)≠eta j) → b sigma=0)
    (heq : ∀epsilon : Fin n → CMS.Sign,a (Fin.append epsilon eta)=b (Fin.append epsilon eta)) : a=b := by
  classical
  funext sigma
  by_cases hd : ∀j,sigma (Fin.natAdd n j)=eta j
  · have hs : sigma=Fin.append (fun i=>sigma (Fin.castAdd m i)) eta := by
      funext i
      refine Fin.addCases (fun j=>?_) (fun j=>?_) i
      · simp
      · simpa only [Fin.append_right] using hd j
    rw [hs]
    exact heq _
  · push_neg at hd
    rw [ha sigma hd,hb sigma hd]

end BourgadeHuang.RationalBulk
