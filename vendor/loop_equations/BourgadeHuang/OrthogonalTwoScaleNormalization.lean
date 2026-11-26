import BourgadeHuang.OrthogonalRatioMatching
import BourgadeHuang.OrthogonalTwoScaleGrowth
import BourgadeHuang.OrthogonalPhaseIdentity

/-! Concrete small-source normalization on the actual balanced comparison ray. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace BourgadeHuang
namespace OrthogonalCMS

def balancedRayOffset (q : ℕ) : Fin (q+(q+q))→ℝ :=
  Fin.append (fun _=>1) (Fin.append (fun _=> -1) (fun _=> -1))

end OrthogonalCMS

/-- Reflection along the chosen sign gives the actual positive ray height. -/
theorem reflect_twoScaleRay_im {d : ℕ} (ξ δ : Fin d→ℝ) (σ : Fin d→CMS.Sign)
    (k : ℕ) (r : ℝ) (i : Fin d) :
    (reflectComplex (σ i) (CMS.twoScaleRay ξ δ σ k r i)).im=r^(k+2)+r*δ i := by
  cases hs : σ i <;> simp [reflectComplex,CMS.twoScaleRay,hs,CMS.signValue,←Complex.ofReal_pow]

theorem norm_twoScaleRay_sub_same_sign {d : ℕ} (ξ δ : Fin d→ℝ) (σ : Fin d→CMS.Sign)
    (k : ℕ) (r : ℝ) (i j : Fin d) (hs : σ i=σ j) :
    ‖CMS.twoScaleRay ξ δ σ k r j-CMS.twoScaleRay ξ δ σ k r i‖≤
      |r| * (|ξ j-ξ i|+|δ j-δ i|) := by
  rw [CMS.twoScaleRay_gap_eq,← hs,sub_self,mul_zero,zero_mul,add_zero]
  rw [show CMS.signValue (σ i)*Complex.ofReal (δ j)-CMS.signValue (σ i)*Complex.ofReal (δ i)=
    CMS.signValue (σ i)*Complex.ofReal (δ j-δ i) by push_cast; ring]
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg r)
  calc
    _≤‖Complex.ofReal (ξ j-ξ i)‖+‖Complex.I*(CMS.signValue (σ i)*Complex.ofReal (δ j-δ i))‖ := norm_add_le _ _
    _=_ := by cases h : σ i <;> simp [h,CMS.signValue,norm_mul,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_sub_comm]

/-- The balanced comparison geometry gives the normalized actual expectation
one, with every denominator match and source error justified internally. -/
theorem expectedOrthogonalRatioFunction_twoScale_normalized {q : ℕ}
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hh : ExactAnchoredHierarchy ν .one) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState=>Real.exp (a*‖s.val.2‖^2)) ν)
    (ξ : Fin (q+(q+q))→ℝ) (ε η : Fin q→CMS.Sign)
    (hb : CMS.signCount ε true=CMS.signCount η true) :
    Tendsto (fun r : ℝ=>Complex.exp (-CMS.generalRayPhase (OrthogonalCMS.charges q)
        (OrthogonalCMS.branchSigns ε η)
        (CMS.twoScaleRay ξ (OrthogonalCMS.balancedRayOffset q) (OrthogonalCMS.branchSigns ε η) 2 r))*
      expectedOrthogonalRatioFunction ν
        (CMS.twoScaleRay ξ (OrthogonalCMS.balancedRayOffset q) (OrthogonalCMS.branchSigns ε η) 2 r))
      atTop (𝓝 1) := by
  obtain ⟨p,hp⟩ := OrthogonalCMS.exists_signMatching ε η hb
  let C := 2+2*∑i,|ξ i|
  have hC : 0<C := by dsimp [C]; positivity
  have hξ (i j : Fin (q+(q+q))) : |ξ i-ξ j|+2≤C := by
    have hi := Finset.single_le_sum (f:=fun i=>|ξ i|) (fun i _=>abs_nonneg (ξ i)) (Finset.mem_univ i)
    have hj := Finset.single_le_sum (f:=fun i=>|ξ i|) (fun i _=>abs_nonneg (ξ i)) (Finset.mem_univ j)
    have hab : |ξ i-ξ j|≤|ξ i|+|ξ j| := by simpa using abs_sub_le (ξ i) 0 (ξ j)
    dsimp [C]
    linarith
  let z := fun r=>CMS.twoScaleRay ξ (OrthogonalCMS.balancedRayOffset q) (OrthogonalCMS.branchSigns ε η) 2 r
  let u := fun r j=>z r (OrthogonalCMS.numeratorIndex j)
  let v := fun r j=>z r (OrthogonalCMS.firstDenominatorIndex j)
  let w := fun r j=>z r (OrthogonalCMS.secondDenominatorIndex j)
  have hδ : Tendsto (fun r : ℝ=>C/r) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using tendsto_inv_atTop_zero.const_mul C
  have hgeom : ∀ᶠr : ℝ in atTop,0<r^2 ∧ 0<C/r ∧
      (∀j,r^2≤(reflectComplex (ε j) (u r j)).im) ∧
      (∀j,r^2≤(reflectComplex (ε j) (v r (p j))).im) ∧
      (∀j,r^2≤(reflectComplex (ε j) (w r (p j))).im) ∧
      (∀j,‖u r j-v r (p j)‖≤(C/r)*r^2) ∧ ∀j,‖u r j-w r (p j)‖≤(C/r)*r^2 := by
    filter_upwards [eventually_ge_atTop (2:ℝ)] with r hr
    have hrp : 0<r := by linarith
    have hheight : r^2≤r^4-r := by
      have h2 : 0≤r^2-2 := by nlinarith
      have h4 := mul_nonneg h2 (sq_nonneg r)
      nlinarith
    have himU (j) : (reflectComplex (ε j) (u r j)).im=r^4+r := by
      have h := reflect_twoScaleRay_im ξ (OrthogonalCMS.balancedRayOffset q)
        (OrthogonalCMS.branchSigns ε η) 2 r (OrthogonalCMS.numeratorIndex j)
      simpa only [u,z,OrthogonalCMS.numeratorIndex,OrthogonalCMS.balancedRayOffset,
        OrthogonalCMS.branchSigns,Fin.append_left,Fin.append_right,mul_one] using h
    have himV (j) : (reflectComplex (ε j) (v r (p j))).im=r^4-r := by
      have h := reflect_twoScaleRay_im ξ (OrthogonalCMS.balancedRayOffset q)
        (OrthogonalCMS.branchSigns ε η) 2 r (OrthogonalCMS.firstDenominatorIndex (p j))
      simpa only [v,z,OrthogonalCMS.firstDenominatorIndex,OrthogonalCMS.balancedRayOffset,
        OrthogonalCMS.branchSigns,Fin.append_left,Fin.append_right,hp,mul_neg_one,sub_eq_add_neg] using h
    have himW (j) : (reflectComplex (ε j) (w r (p j))).im=r^4-r := by
      have h := reflect_twoScaleRay_im ξ (OrthogonalCMS.balancedRayOffset q)
        (OrthogonalCMS.branchSigns ε η) 2 r (OrthogonalCMS.secondDenominatorIndex (p j))
      simpa only [w,z,OrthogonalCMS.secondDenominatorIndex,OrthogonalCMS.balancedRayOffset,
        OrthogonalCMS.branchSigns,Fin.append_left,Fin.append_right,hp,mul_neg_one,sub_eq_add_neg] using h
    refine ⟨by positivity,div_pos hC hrp,?_,?_,?_,?_,?_⟩
    · intro j; rw [himU]; linarith
    · intro j; rw [himV]; exact hheight
    · intro j; rw [himW]; exact hheight
    · intro j
      have hs : OrthogonalCMS.branchSigns ε η (OrthogonalCMS.firstDenominatorIndex (p j))=
          OrthogonalCMS.branchSigns ε η (OrthogonalCMS.numeratorIndex j) := by
        simp only [OrthogonalCMS.branchSigns,OrthogonalCMS.firstDenominatorIndex,
          OrthogonalCMS.numeratorIndex,Fin.append_left,Fin.append_right,hp]
      have h := norm_twoScaleRay_sub_same_sign ξ (OrthogonalCMS.balancedRayOffset q)
        (OrthogonalCMS.branchSigns ε η) 2 r _ _ hs
      simp only [OrthogonalCMS.balancedRayOffset,OrthogonalCMS.firstDenominatorIndex,
        OrthogonalCMS.numeratorIndex,Fin.append_left,Fin.append_right,sub_neg_eq_add,one_add_one_eq_two,
        abs_of_pos (by norm_num : (0:ℝ)<2),abs_of_pos hrp] at h
      apply h.trans
      calc
        _≤r*C := mul_le_mul_of_nonneg_left (hξ _ _) hrp.le
        _=_ := by field_simp; ring
    · intro j
      have hs : OrthogonalCMS.branchSigns ε η (OrthogonalCMS.secondDenominatorIndex (p j))=
          OrthogonalCMS.branchSigns ε η (OrthogonalCMS.numeratorIndex j) := by
        simp only [OrthogonalCMS.branchSigns,OrthogonalCMS.secondDenominatorIndex,
          OrthogonalCMS.numeratorIndex,Fin.append_left,Fin.append_right,hp]
      have h := norm_twoScaleRay_sub_same_sign ξ (OrthogonalCMS.balancedRayOffset q)
        (OrthogonalCMS.branchSigns ε η) 2 r _ _ hs
      simp only [OrthogonalCMS.balancedRayOffset,OrthogonalCMS.secondDenominatorIndex,
        OrthogonalCMS.numeratorIndex,Fin.append_left,Fin.append_right,sub_neg_eq_add,one_add_one_eq_two,
        abs_of_pos (by norm_num : (0:ℝ)<2),abs_of_pos hrp] at h
      apply h.trans
      calc
        _≤r*C := mul_le_mul_of_nonneg_left (hξ _ _) hrp.le
        _=_ := by field_simp; ring
  have h := tendsto_expectedOrthogonalCharacteristicRatios_matched_normalized ν hh ha he ε u v w p
    (fun r=>r^2) (fun r=>C/r) hδ hgeom
  simpa only [u,v,w,OrthogonalCMS.signedOrthogonalRatioPhase_sum_eq ε η p hp,z] using h

end BourgadeHuang
