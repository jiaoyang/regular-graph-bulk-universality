import BourgadeHuang.RationalBulk.ChargedCoefficientNormalization
import BourgadeHuang.RationalBulk.ChargedRayGrowth
import BourgadeHuang.RationalCoefficientSelection

/-! The actual general-beta expectation determines every CMS coefficient.
No growth, support, branch asymptotic, or coefficient identity is assumed. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter Set
namespace BourgadeHuang.RationalBulk

@[simp] theorem upperRepresentative_signAnchor (sigma : Bool) :
    upperRepresentative (signAnchor sigma 1)=Complex.I := by
  cases sigma <;> simp [upperRepresentative,signAnchor,CMS.signValue]

theorem blockAnchors_upperRepresentative {n m : ℕ} (theta : Fin n → Bool)
    (eta : Fin m → Bool) (i : Fin (n+m)) :
    upperRepresentative (blockAnchors theta eta i)=Complex.I := by
  rw [blockAnchors_eq_signAnchor]
  exact upperRepresentative_signAnchor _

theorem coefficientDirection_denominatorDomain {n m : ℕ} {beta : ℝ}
    (hbeta : 0<beta) (eta : Fin m → Bool) :
    coefficientDirection beta n eta∈denominatorDomain n eta := by
  intro j
  cases hs : eta j <;> simp [coefficientDirection,hs,CMS.realSign,CMS.signValue]
  · exact div_neg_of_neg_of_pos (neg_neg_of_pos (pow_pos (by norm_num) _)) hbeta
  · exact hbeta

theorem coefficientDirection_offReal {n m : ℕ} {beta : ℝ}
    (hbeta : 0<beta) (eta : Fin m → Bool) (i : Fin (n+m)) :
    (coefficientDirection beta n eta i).im≠0 := by
  refine Fin.addCases (fun i=>?_) (fun j=>?_) i
  · simp [coefficientDirection]
  · have h := coefficientDirection_denominatorDomain (n:=n) hbeta eta j
    cases hs : eta j <;> simp only [hs,Bool.false_eq_true,↓reduceIte] at h
    · exact ne_of_lt h
    · exact h.ne'

theorem coefficientDirection_eventually_chamber {n m : ℕ} {beta : ℝ}
    (hbeta : 0<beta) (eta : Fin m → Bool) :
    ∀ᶠr : ℝ in atTop,(fun i=>(r:ℂ)*coefficientDirection beta n eta i)∈
      sectorialChamber hbeta n eta := by
  filter_upwards [CMS.ordered_scale_gaps (coefficientDirection_ordered beta eta)
    (sectorialRadius hbeta n m),eventually_gt_atTop (0:ℝ)] with r hgap hr
  refine ⟨hgap,?_⟩
  intro i hi
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
  have hsign := coefficientDirection_denominatorDomain (n:=n) hbeta eta j
  simp only [chamberSigns,Fin.append_right]
  cases hs : eta j <;> simp only [hs,Bool.false_eq_true,↓reduceIte] at hsign ⊢
  · simpa using mul_neg_of_pos_of_neg hr hsign
  · simpa using mul_pos hr hsign

theorem chargedCoefficients_denominator_support {n m : ℕ}
    (nu : Measure AnchoredCountingState) [IsProbabilityMeasure nu]
    (beta : ℝ) (hbeta : 0<beta) (hh : ExactHierarchy nu beta) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState=>Real.exp (a*‖s.val.2‖^2)) nu)
    (theta : Fin n → Bool) (eta : Fin m → Bool)
    (hn : (n:ℝ)=(m:ℝ)*beta/2)
    (hbal : beta*(CMS.signCount eta true:ℝ)=2*(CMS.signCount theta true:ℝ))
    (sigma : Fin (n+m) → CMS.Sign) (hwrong : ∃j,sigma (Fin.natAdd n j)≠eta j) :
    chargedCoefficients nu beta hbeta hh ha he theta eta hn hbal sigma=0 := by
  let F := fun r : ℝ=>expectedChargedObservable nu (charges beta n m) (blockAnchors theta eta)
    (fun i=>(r:ℂ)*coefficientDirection beta n eta i)
  obtain ⟨C,_,hC⟩ := expectedChargedObservable_coefficient_growth nu beta hbeta hh ha he eta
    (blockAnchors theta eta) (coefficientDirection_offReal hbeta eta)
    (chargedDomain_of_denominatorDomain beta theta eta _ (coefficientDirection_denominatorDomain hbeta eta))
    hn (by simp : 0<Complex.I.im) (blockAnchors_upperRepresentative theta eta)
  apply physical_expansion_denominator_support hbeta eta
    (chargedCoefficients nu beta hbeta hh ha he theta eta hn hbal) F C ?_ ?_ sigma hwrong
  · filter_upwards [coefficientDirection_eventually_chamber hbeta eta] with r hr
    exact chargedCoefficients_spec nu beta hbeta hh ha he theta eta hn hbal hr
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
    exact hC r hr

theorem chargedCoefficients_denominator_eq_of_ne_zero {n m : ℕ}
    (nu : Measure AnchoredCountingState) [IsProbabilityMeasure nu]
    (beta : ℝ) (hbeta : 0<beta) (hh : ExactHierarchy nu beta) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState=>Real.exp (a*‖s.val.2‖^2)) nu)
    (theta : Fin n → Bool) (eta : Fin m → Bool)
    (hn : (n:ℝ)=(m:ℝ)*beta/2)
    (hbal : beta*(CMS.signCount eta true:ℝ)=2*(CMS.signCount theta true:ℝ))
    (sigma : Fin (n+m) → CMS.Sign)
    (hsigma : chargedCoefficients nu beta hbeta hh ha he theta eta hn hbal sigma≠0) :
    ∀j,sigma (Fin.natAdd n j)=eta j := by
  intro j
  by_contra hj
  exact hsigma (chargedCoefficients_denominator_support nu beta hbeta hh ha he theta eta hn hbal sigma ⟨j,hj⟩)

theorem chargedCoefficients_unbalanced_eq_zero {n m : ℕ}
    (nu : Measure AnchoredCountingState) [IsProbabilityMeasure nu]
    (beta : ℝ) (hbeta : 0<beta) (hh : ExactHierarchy nu beta) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState=>Real.exp (a*‖s.val.2‖^2)) nu)
    (theta : Fin n → Bool) (eta : Fin m → Bool)
    (hn : (n:ℝ)=(m:ℝ)*beta/2)
    (hbal : beta*(CMS.signCount eta true:ℝ)=2*(CMS.signCount theta true:ℝ))
    (epsilon : Fin n → Bool)
    (hepsilon : beta*(CMS.signCount eta true:ℝ)≠2*(CMS.signCount epsilon true:ℝ)) :
    chargedCoefficients nu beta hbeta hh ha he theta eta hn hbal (Fin.append epsilon eta)=0 := by
  apply coefficient_unbalanced_eq_zero hbeta hn eta
    (expectedChargedObservable nu (charges beta n m) (blockAnchors theta eta))
    (chargedCoefficients nu beta hbeta hh ha he theta eta hn hbal)
    (chargedCoefficients_spec nu beta hbeta hh ha he theta eta hn hbal)
    (chargedCoefficients_denominator_eq_of_ne_zero nu beta hbeta hh ha he theta eta hn hbal)
    epsilon hepsilon
  apply expectedChargedObservable_zeroOffset_twoScale_bounded nu beta hh ha he
    (realCharges beta n m) (blockAnchors theta eta) (fun i=>(i.val:ℝ)) (Fin.append epsilon eta)
    (by rw [sum_realCharges,hn]; ring)
    (by simp : 0<Complex.I.im) (blockAnchors_upperRepresentative theta eta)
  intro i
  refine Fin.addCases (fun i=>?_) (fun j=>?_) i
  · intro hi
    exact (hi (by simp [realCharges])).elim
  · intro _
    simp [blockAnchors,reflect_signAnchor_im]

theorem chargedCoefficients_balanced_eq {n m : ℕ}
    (nu : Measure AnchoredCountingState) [IsProbabilityMeasure nu]
    (beta : ℝ) (hbeta : 0<beta) (hh : ExactHierarchy nu beta) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState=>Real.exp (a*‖s.val.2‖^2)) nu)
    (theta : Fin n → Bool) (eta : Fin m → Bool)
    (hn : (n:ℝ)=(m:ℝ)*beta/2)
    (hbal : beta*(CMS.signCount eta true:ℝ)=2*(CMS.signCount theta true:ℝ))
    (epsilon : Fin n → Bool)
    (hepsilon : beta*(CMS.signCount eta true:ℝ)=2*(CMS.signCount epsilon true:ℝ)) :
    chargedCoefficients nu beta hbeta hh ha he theta eta hn hbal (Fin.append epsilon eta)=
      (CMS.twoScaleBranchConstant (beta:ℂ) (charges beta n m) (Fin.append epsilon eta))⁻¹ := by
  exact coefficient_balanced_eq hbeta hn eta
    (expectedChargedObservable nu (charges beta n m) (blockAnchors theta eta))
    (chargedCoefficients nu beta hbeta hh ha he theta eta hn hbal)
    (chargedCoefficients_spec nu beta hbeta hh ha he theta eta hn hbal)
    (chargedCoefficients_denominator_eq_of_ne_zero nu beta hbeta hh ha he theta eta hn hbal)
    epsilon hepsilon (expectedChargedObservable_balanced_twoScale_normalized nu beta hh ha he
      theta epsilon eta hn hbal hepsilon (fun i=>(i.val:ℝ)))

/-- Universal coefficient formula for the actual hierarchy expectation. -/
theorem chargedCoefficients_formula {n m : ℕ}
    (nu : Measure AnchoredCountingState) [IsProbabilityMeasure nu]
    (beta : ℝ) (hbeta : 0<beta) (hh : ExactHierarchy nu beta) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState=>Real.exp (a*‖s.val.2‖^2)) nu)
    (theta : Fin n → Bool) (eta : Fin m → Bool)
    (hn : (n:ℝ)=(m:ℝ)*beta/2)
    (hbal : beta*(CMS.signCount eta true:ℝ)=2*(CMS.signCount theta true:ℝ))
    (epsilon : Fin n → Bool) :
    chargedCoefficients nu beta hbeta hh ha he theta eta hn hbal (Fin.append epsilon eta)=
      if beta*(CMS.signCount eta true:ℝ)=2*(CMS.signCount epsilon true:ℝ) then
        (CMS.twoScaleBranchConstant (beta:ℂ) (charges beta n m) (Fin.append epsilon eta))⁻¹ else 0 := by
  classical
  split_ifs with hepsilon
  · exact chargedCoefficients_balanced_eq nu beta hbeta hh ha he theta eta hn hbal epsilon hepsilon
  · exact chargedCoefficients_unbalanced_eq_zero nu beta hbeta hh ha he theta eta hn hbal epsilon hepsilon

end BourgadeHuang.RationalBulk
