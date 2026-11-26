import BourgadeHuang.OrthogonalRatioGrowth
import BourgadeHuang.OrthogonalBranchBalance
import BourgadeHuang.CMS.TwoScaleRays

/-! The actual orthogonal expectation is bounded on the equal-height
 two-scale rays used to remove unbalanced CMS phases. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace BourgadeHuang

theorem upperRepresentative_sub_of_abs_im_eq {u v : ℂ} (h : |u.im|=|v.im|) :
    upperRepresentative u-upperRepresentative v=Complex.ofReal (u.re-v.re) := by
  apply Complex.ext <;> simp [h]

/-- All numerator sign choices share a uniform genuine expectation bound on
linearly separated real coordinates and common quadratic imaginary heights. -/
theorem expectedOrthogonalRatioFunction_twoScale_bounded {q : ℕ}
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hh : ExactAnchoredHierarchy ν .one) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState=>Real.exp (a*‖s.val.2‖^2)) ν)
    (ξ : Fin (q+(q+q))→ℝ) (ε η : Fin q→CMS.Sign) :
    ∃C : ℝ,0≤C ∧ ∀r : ℝ,1≤r →
      ‖expectedOrthogonalRatioFunction ν
        (CMS.twoScaleRay ξ (fun _=>0) (OrthogonalCMS.branchSigns ε η) 0 r)‖≤C := by
  by_cases hq : q=0
  · subst q
    refine ⟨1,zero_le_one,?_⟩
    intro r _
    simp [expectedOrthogonalRatioFunction,OrthogonalCMS.blockFunction,CMS.blockFunction,
      expectedOrthogonalCharacteristicRatios,orthogonalCharacteristicRatios]
  have hqp := Nat.pos_of_ne_zero hq
  let D := 2*∑i,|ξ i|
  have hD : 0≤D := by dsimp [D]; positivity
  have hξ (i j : Fin (q+(q+q))) : |ξ i-ξ j|≤D := by
    have hi := Finset.single_le_sum (f:=fun i=>|ξ i|) (fun i _=>abs_nonneg (ξ i)) (Finset.mem_univ i)
    have hj := Finset.single_le_sum (f:=fun i=>|ξ i|) (fun i _=>abs_nonneg (ξ i)) (Finset.mem_univ j)
    calc
      |ξ i-ξ j|≤|ξ i|+|ξ j| := by simpa using abs_sub_le (ξ i) 0 (ξ j)
      _≤(∑i,|ξ i|)+(∑i,|ξ i|) := add_le_add hi hj
      _=D := by dsimp [D]; ring
  refine ⟨(q:ℝ)*(2*Real.exp (((q:ℝ)*D)^2/(4*orthogonalBulkExponentialScale))),by positivity,?_⟩
  intro r hr
  have hrp : 0<r := lt_of_lt_of_le zero_lt_one hr
  let z := CMS.twoScaleRay ξ (fun _=>0) (OrthogonalCMS.branchSigns ε η) 0 r
  have habs (i) : |(z i).im|=r^2 := by
    dsimp [z,CMS.twoScaleRay]
    cases hs : OrthogonalCMS.branchSigns ε η i <;> simp [hs,CMS.signValue,sq_nonneg r]
  have hoff i : (z i).im≠0 := abs_pos.mp (by rw [habs]; positivity)
  have hcost (i j) : ‖upperRepresentative (z i)-upperRepresentative (z j)‖≤
      D*min |(z i).im| |(z j).im| := by
    rw [upperRepresentative_sub_of_abs_im_eq ((habs i).trans (habs j).symm)]
    simp only [Complex.norm_real,Real.norm_eq_abs,z,CMS.twoScaleRay_re]
    rw [← mul_sub,abs_mul,abs_of_pos hrp,habs,habs,min_self]
    have hx := mul_le_mul_of_nonneg_left (hξ i j) hrp.le
    have hs := mul_nonneg hD (mul_nonneg hrp.le (sub_nonneg.mpr hr))
    nlinarith
  have hwv j : SameOpenHalfPlane (z (OrthogonalCMS.secondDenominatorIndex j))
      (z (OrthogonalCMS.firstDenominatorIndex j)) := by
    cases hs : η j <;>
      simp only [z,CMS.twoScaleRay,OrthogonalCMS.firstDenominatorIndex,OrthogonalCMS.secondDenominatorIndex,
        OrthogonalCMS.branchSigns,Fin.append_left,Fin.append_right,hs,CMS.signValue] <;>
      simp [SameOpenHalfPlane,←Complex.ofReal_pow,sq_pos_of_pos hrp]
  have h := expectedOrthogonalCharacteristicRatios_growth hqp ν hh ha he
    (fun j=>z (OrthogonalCMS.numeratorIndex j)) (fun j=>z (OrthogonalCMS.firstDenominatorIndex j))
    (fun j=>z (OrthogonalCMS.secondDenominatorIndex j))
    (fun j=>hoff _) hwv hD (fun j=>hcost _ _) (fun j=>hcost _ _)
  have heq : (∑j : Fin q, (|(z (OrthogonalCMS.numeratorIndex j)).im|-
      (|(z (OrthogonalCMS.firstDenominatorIndex j)).im|+
        |(z (OrthogonalCMS.secondDenominatorIndex j)).im|)/2))=0 := by
    simp only [habs]
    simp
  rw [heq,Real.exp_zero,mul_one] at h
  exact h

end BourgadeHuang
