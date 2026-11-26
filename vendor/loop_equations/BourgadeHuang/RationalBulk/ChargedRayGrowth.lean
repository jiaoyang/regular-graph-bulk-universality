import BourgadeHuang.RationalBulk.ChargedGrowth
import BourgadeHuang.RationalCoefficientRays
import BourgadeHuang.OrthogonalTwoScaleNormalization

/-! Exact growth bounds on the coefficient-separating and two-scale rays. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalBulk

theorem coefficientDirection_abs_im (β : ℝ) (hβ : 0<β) {n m : ℕ}
    (eta : Fin m → CMS.Sign) :
    (-∑j,realCharges β n m j*|(coefficientDirection β n eta j).im|)=
      CMS.binaryObservableRate n m := by
  rw [Fin.sum_univ_add]
  simp only [realCharges,coefficientDirection,Fin.append_left,Fin.append_right,
    Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,Complex.I_im,
    zero_mul,one_mul,Complex.ofReal_re,zero_add, neg_one_mul, Complex.natCast_im,
    ←Complex.ofReal_pow, Complex.ofReal_re, add_zero]
  rw [Finset.sum_neg_distrib]
  have hden : (∑j : Fin m,β/2*|CMS.realSign (eta j)*2^(n+j.val+1)/β|)=
      ∑j : Fin m,(2:ℝ)^(n+j.val) := by
    apply Finset.sum_congr rfl
    intro j _
    have he : |CMS.realSign (eta j)|=1 := by cases eta j <;> norm_num [CMS.realSign]
    rw [abs_div,abs_mul,he,one_mul,abs_of_pos (pow_pos (by norm_num) _),abs_of_pos hβ]
    rw [pow_succ]
    field_simp
    <;> ring
  rw [hden]
  simp only [abs_of_pos (pow_pos (by norm_num : (0:ℝ)<2) _),CMS.binaryObservableRate]
  ring

theorem expectedChargedObservable_coefficient_growth {n m : ℕ}
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν] (β : ℝ) (hβ : 0<β)
    (hh : ExactHierarchy ν β) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (eta : Fin m → CMS.Sign) (b : Fin (n+m) → ℂ)
    (hz : ∀j,(coefficientDirection β n eta j).im≠0)
    (hd : ChargedDomain (charges β n m) b (coefficientDirection β n eta))
    (hn : (n:ℝ)=(m:ℝ)*β/2) {B : ℂ} (hB : 0<B.im)
    (hb : ∀j,upperRepresentative (b j)=B) :
    ∃C : ℝ,0≤C ∧ ∀r : ℝ,0<r →
      ‖expectedChargedObservable ν (charges β n m) b
        (fun j => (r:ℂ)*coefficientDirection β n eta j)‖ ≤
        C*Real.exp (r*CMS.binaryObservableRate n m) := by
  have hneutral : ∑j,realCharges β n m j=0 := by rw [sum_realCharges]; linarith
  simpa only [coefficientDirection_abs_im β hβ eta,charges] using
    expectedChargedObservable_homogeneous_growth ν β hh ha he (realCharges β n m) b
      (coefficientDirection β n eta) hz hd hneutral hB hb

theorem expectedChargedObservable_zeroOffset_twoScale_bounded {d : ℕ}
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν] (β : ℝ)
    (hh : ExactHierarchy ν β) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (c : Fin d → ℝ) (b : Fin d → ℂ) (xi : Fin d → ℝ) (sigma : Fin d → CMS.Sign)
    (hneutral : ∑j,c j=0) {B : ℂ} (hB : 0<B.im)
    (hb : ∀j,upperRepresentative (b j)=B)
    (hbase : ∀j,(c j:ℂ)≠-1 → 0<(reflectComplex (sigma j) (b j)).im) :
    ∃C : ℝ,∀ᶠr : ℝ in atTop,
      ‖expectedChargedObservable ν (fun j=>(c j:ℂ)) b
        (CMS.twoScaleRay xi (fun _=>0) sigma 0 r)‖≤C := by
  by_cases hd0 : d=0
  · subst d
    refine ⟨1,Eventually.of_forall (fun r => ?_)⟩
    simp [expectedChargedObservable,chargedObservable]
  have hdim := Nat.pos_of_ne_zero hd0
  let D := ∑j,|xi j|
  let K := ∑j,|c j|
  have hD : 0≤D := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hK : 0≤K := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hcoef j : |c j|≤K := Finset.single_le_sum (f:=fun j=>|c j|)
    (fun j _ => abs_nonneg _) (Finset.mem_univ j)
  have hxi j : |xi j|≤D := Finset.single_le_sum (f:=fun j=>|xi j|)
    (fun j _ => abs_nonneg _) (Finset.mem_univ j)
  refine ⟨(d:ℝ)*(2*Real.exp (((d:ℝ)*K*D)^2/(4*bulkExponentialScale β))),?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ)] with r hr
  have hrp : 0<r := zero_lt_one.trans_le hr
  let z := CMS.twoScaleRay xi (fun _=>0) sigma 0 r
  have hheight j : (reflectComplex (sigma j) (z j)).im=r^2 := by
    simpa only [z,Nat.zero_add,mul_zero,add_zero] using
      reflect_twoScaleRay_im xi (fun _=>0) sigma 0 r j
  have hpos j : 0<(reflectComplex (sigma j) (z j)).im := by rw [hheight]; positivity
  have hz j : (z j).im≠0 := by
    have hp := hpos j
    cases hs : sigma j <;> simp [reflectComplex,hs] at hp
    · exact ne_of_lt (by linarith)
    · exact hp.ne'
  have habs j : |(z j).im|=r^2 := by
    have hp := hpos j
    have ht := hheight j
    cases hs : sigma j <;> simp [reflectComplex,hs] at ht hp
    · rw [abs_of_neg (by linarith)]; exact ht
    · rw [abs_of_pos hp]; exact ht
  have hupper j : upperRepresentative (z j)=(r*xi j:ℝ)+(r^2:ℝ)*Complex.I := by
    apply Complex.ext
    · cases hs : sigma j <;> simp [z,CMS.twoScaleRay,upperRepresentative,CMS.signValue,hs,←Complex.ofReal_pow]
    · simp [upperRepresentative,habs,←Complex.ofReal_pow]
  have hdom : ChargedDomain (fun j=>(c j:ℂ)) b z := by
    refine ⟨?_,?_⟩
    · intro j hj
      have h := congrArg Complex.im (hb j)
      simp only [upperRepresentative_im,hj,abs_zero] at h
      linarith
    · intro j hj
      exact sameOpenHalfPlane_of_reflect_pos (sigma j) (hpos j) (hbase j hj)
  have hcost j : ‖upperRepresentative (z j)-(r^2:ℝ)*Complex.I‖≤D*min |(z j).im| (((r^2:ℝ):ℂ)*Complex.I).im := by
    rw [hupper,habs]
    simp only [add_sub_cancel_right,Complex.norm_real,Real.norm_eq_abs,
      abs_mul,abs_of_pos hrp,Complex.mul_im,Complex.ofReal_re,Complex.I_im,mul_one,
      Complex.ofReal_im,zero_mul,add_zero,min_self]
    nlinarith [mul_le_mul_of_nonneg_left (hxi j) hrp.le, mul_nonneg hD (show 0≤r^2-r by nlinarith)]
  have h := expectedChargedObservable_growth hdim ν β hh ha he c b z hz hdom hneutral hB
    (show 0<(((r^2:ℝ):ℂ)*Complex.I).im by simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_im,zero_mul,mul_one,add_zero] using sq_pos_of_pos hrp) hb hD hK hcoef hcost
  simp only [habs,←Finset.sum_mul,hneutral,zero_mul,neg_zero,Real.exp_zero,mul_one] at h
  exact h

end BourgadeHuang.RationalBulk
