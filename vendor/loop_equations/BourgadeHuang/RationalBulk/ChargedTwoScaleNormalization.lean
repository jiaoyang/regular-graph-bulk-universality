import BourgadeHuang.RationalBulk.ChargedNormalization
import BourgadeHuang.RationalBulk.ChargeReanchoring
import BourgadeHuang.OrthogonalTwoScaleNormalization

/-! Balanced general charges have the genuine deterministic phase limit on the
comparison ray. All reanchoring, moment estimates, and path errors are proved. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalBulk

theorem norm_twoScale_sub_signAnchor {d : ℕ} (xi delta : Fin d → ℝ)
    (sigma : Fin d → CMS.Sign) (r : ℝ) (i : Fin d) :
    ‖CMS.twoScaleRay xi delta sigma 2 r i-signAnchor (sigma i) (r^4)‖≤
      |r| * (|xi i|+|delta i|) := by
  have he : CMS.twoScaleRay xi delta sigma 2 r i-signAnchor (sigma i) (r^4)=
      (r:ℂ)*((xi i:ℂ)+Complex.I*CMS.signValue (sigma i)*(delta i:ℂ)) := by
    simp only [CMS.twoScaleRay,signAnchor,Complex.ofReal_pow]
    norm_num
    ring
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg r)
  calc
    _≤‖(xi i:ℂ)‖+‖Complex.I*CMS.signValue (sigma i)*(delta i:ℂ)‖ := norm_add_le _ _
    _=_ := by cases hs : sigma i <;>
      simp [hs,CMS.signValue,norm_mul,Complex.norm_real,Real.norm_eq_abs]

theorem expectedChargedObservable_twoScale_normalized {d : ℕ}
    (nu : Measure AnchoredCountingState) [IsProbabilityMeasure nu]
    (beta : ℝ) (hh : ExactHierarchy nu beta) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState=>Real.exp (a*‖s.val.2‖^2)) nu)
    (c xi delta : Fin d → ℝ) (sigma : Fin d → CMS.Sign)
    (hzero : ∑i,c i=0) (hsigned : ∑i,c i*CMS.realSign (sigma i)=0)
    (hdelta : ∀i,|delta i|≤1) :
    Tendsto (fun r : ℝ=>Complex.exp (-CMS.generalRayPhase (fun i=>(c i:ℂ)) sigma
        (CMS.twoScaleRay xi delta sigma 2 r))*
      expectedChargedObservable nu (fun i=>(c i:ℂ))
        (fun i=>signAnchor (sigma i) 1) (CMS.twoScaleRay xi delta sigma 2 r))
      atTop (𝓝 1) := by
  let C : ℝ := 1+∑i,|c i| *(|xi i|+1)
  have hC : 0<C := by dsimp [C]; positivity
  have hci (i : Fin d) : |c i| *(|xi i|+1)≤C := by
    have hi := Finset.single_le_sum
      (f:=fun j=>|c j| *(|xi j|+1)) (fun j _=>by positivity) (Finset.mem_univ i)
    dsimp at hi
    dsimp [C]
    linarith
  have hC0 : Tendsto (fun r : ℝ=>C/r) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using tendsto_inv_atTop_zero.const_mul C
  let z := fun r=>CMS.twoScaleRay xi delta sigma 2 r
  let v := fun r i=>signAnchor (sigma i) (r^4)
  have hgeom : ∀ᶠr : ℝ in atTop,0<r^2 ∧ 0<C/r ∧
      (∀i,r^2≤(reflectComplex (sigma i) (z r i)).im) ∧
      (∀i,r^2≤(reflectComplex (sigma i) (v r i)).im) ∧
      (∀i,|c i| * ‖z r i-v r i‖≤(C/r)*r^2) := by
    filter_upwards [eventually_ge_atTop (2:ℝ)] with r hr
    have hrp : 0<r := by linarith
    have hheight : r^2≤r^4-r := by
      have h2 : 0≤r^2-2 := by nlinarith
      have h4 := mul_nonneg h2 (sq_nonneg r)
      nlinarith
    refine ⟨by positivity,div_pos hC hrp,?_,?_,?_⟩
    · intro i
      dsimp [z]
      rw [reflect_twoScaleRay_im]
      norm_num
      have hi := (abs_le.mp (hdelta i)).1
      have := mul_le_mul_of_nonneg_left hi hrp.le
      nlinarith
    · intro i
      simp only [v,reflect_signAnchor_im]
      linarith
    · intro i
      have hb := norm_twoScale_sub_signAnchor xi delta sigma r i
      rw [abs_of_pos hrp] at hb
      calc
        |c i| * ‖z r i-v r i‖ ≤ |c i| * (r*(|xi i|+|delta i|)) :=
          mul_le_mul_of_nonneg_left hb (abs_nonneg _)
        _ ≤ r*(|c i| *(|xi i|+1)) := by
          nlinarith [mul_le_mul_of_nonneg_left (hdelta i) (mul_nonneg hrp.le (abs_nonneg (c i)))]
        _ ≤ r*C := mul_le_mul_of_nonneg_left (hci i) hrp.le
        _ = (C/r)*r^2 := by field_simp; ring
  have hlim := tendsto_expectedChargedObservable_normalized nu beta hh ha he c sigma
    z v (fun r=>r^2) (fun r=>C/r) hC0 hgeom
  have hzeroC : (∑i,(c i:ℂ))=0 := by exact_mod_cast hzero
  have hsignC : (∑i,(c i:ℂ)*CMS.signValue (sigma i))=0 := by
    simpa only [←CMS.ofReal_realSign,←Complex.ofReal_mul,←Complex.ofReal_sum,
      hsigned,Complex.ofReal_zero]
  apply hlim.congr'
  filter_upwards [hgeom] with r hr
  have hr2 : 0<r^4 := by nlinarith [sq_nonneg (r^2)]
  have hz i : 0<(reflectComplex (sigma i) (z r i)).im := hr.1.trans_le (hr.2.2.1 i)
  have hre : expectedChargedObservable nu (fun i=>(c i:ℂ))
        (fun i=>signAnchor (sigma i) 1) (z r) =
      expectedChargedObservable nu (fun i=>(c i:ℂ)) (v r) (z r) := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun s=>chargedObservable_reanchor_signs
      (fun i=>(c i:ℂ)) sigma (z r) hzeroC hsignC zero_lt_one hr2 hz s)
  rw [signedPhase_sum_eq_generalRayPhase _ _ _ hzeroC]
  exact congrArg (fun w=>Complex.exp (-CMS.generalRayPhase (fun i=>(c i:ℂ)) sigma (z r))*w) hre.symm

end BourgadeHuang.RationalBulk
