import BourgadeHuang.RationalBulk.GaussianBetaDensity
import BourgadeHuang.RationalBulk.RepulsionDerivative

/-! Integrability of collision singularities for every exponent greater than -1.
A volume-preserving shear separates the singular gap from the Gaussian tails. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalBulk

theorem integrable_abs_rpow_polynomial_gaussian {c s : ℝ}
    (hc : 0 < c) (hs : -1 < s) (m : ℕ) :
    Integrable (fun x : ℝ => |x|^s * (1+|x|)^m * Real.exp (-c*x^2)) := by
  have h1 := integrable_abs_rpow_mul_gaussian hc hs
  have h2 := integrable_abs_rpow_mul_gaussian hc
    (show -1 < s+(m:ℝ) by linarith [(Nat.cast_nonneg m : (0:ℝ)≤m)])
  apply ((h1.add h2).const_mul ((2:ℝ)^m)).mono'
  · exact ((measurable_id.abs.pow measurable_const).mul
      ((measurable_const.add measurable_id.abs).pow_const m)).mul
        (((measurable_id.pow_const 2).const_mul (-c)).exp) |>.aestronglyMeasurable
  · filter_upwards [] with x
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    have hp : |x|^s*(1+|x|)^m ≤ (2:ℝ)^m*(|x|^s+|x|^(s+(m:ℝ))) := by
      by_cases hx : |x| ≤ 1
      · have hm : (1+|x|)^m ≤ (2:ℝ)^m := pow_le_pow_left₀ (by positivity) (by linarith) _
        have hr := mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg (abs_nonneg x) s)
        nlinarith [Real.rpow_nonneg (abs_nonneg x) (s+(m:ℝ)), pow_nonneg (by norm_num : (0:ℝ)≤2) m]
      · have hxpos : 0 < |x| := lt_trans zero_lt_one (lt_of_not_ge hx)
        have hm : (1+|x|)^m ≤ (2*|x|)^m :=
          pow_le_pow_left₀ (by positivity) (by linarith) _
        have hr := mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg (abs_nonneg x) s)
        rw [mul_pow] at hr
        rw [Real.rpow_add hxpos,Real.rpow_natCast]
        nlinarith [Real.rpow_nonneg (abs_nonneg x) s, pow_nonneg (by norm_num : (0:ℝ)≤2) m]
    have hb := mul_le_mul_of_nonneg_right hp (Real.exp_pos (-c*x^2)).le
    convert hb using 1 <;> simp only [Pi.add_apply] <;> ring

/-- Shear coordinate `i` by subtracting coordinate `j`. -/
def gapShear {N : ℕ} (i j : Fin N) (x : Fin N → ℝ) : Fin N → ℝ :=
  Function.update x i (x i-x j)

@[simp] theorem gapShear_same {N : ℕ} (i j : Fin N) (x : Fin N → ℝ) :
    gapShear i j x i = x i-x j := by simp [gapShear]

theorem gapShear_other {N : ℕ} (i j k : Fin N) (hki : k ≠ i) (x : Fin N → ℝ) :
    gapShear i j x k = x k := by simp [gapShear,Function.update_of_ne hki]

theorem gapShear_measurePreserving {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    MeasurePreserving (gapShear i j) := by
  convert Real.volume_preserving_transvectionStruct
    (⟨i,j,hij,-1⟩ : Matrix.TransvectionStruct (Fin N) ℝ) using 1
  ext x k
  simp only [Matrix.TransvectionStruct.toMatrix,Matrix.transvection,Matrix.toLin'_apply,
    Matrix.add_mulVec,Matrix.one_mulVec,Matrix.mulVec_stdBasisMatrix,Pi.add_apply]
  by_cases hk : k=i
  · subst k; simp [gapShear]; ring
  · simp [gapShear,Function.update_of_ne hk]

theorem coordinateEnvelope_le_gapShear {N : ℕ} (i j : Fin N) (hij : i ≠ j)
    (x : Fin N → ℝ) : coordinateEnvelope x ≤ coordinateEnvelope (gapShear i j x)^(2*N) := by
  let y := gapShear i j x
  have hE := coordinateEnvelope_one_le y
  have hcoord (k : Fin N) : 1+|x k| ≤ coordinateEnvelope y^2 := by
    by_cases hk : k=i
    · subst k
      have he : x i = y i + y j := by simp [y,gapShear,Function.update_of_ne hij.symm]
      rw [he]
      have hab := abs_add (y i) (y j)
      have hprod : 1+|y i|+|y j| ≤ (1+|y i|)*(1+|y j|) := by
        nlinarith [mul_nonneg (abs_nonneg (y i)) (abs_nonneg (y j))]
      have hb := mul_le_mul (coordinateEnvelope_coordinate y i) (coordinateEnvelope_coordinate y j)
        (by positivity : 0 ≤ 1+|y j|) (by linarith : 0 ≤ coordinateEnvelope y)
      nlinarith
    · have he : x k = y k := (gapShear_other i j k hk x).symm
      rw [he]
      exact (coordinateEnvelope_coordinate y k).trans (by nlinarith)
  calc
    _ ≤ ∏ _k : Fin N, coordinateEnvelope y^2 :=
      Finset.prod_le_prod (fun _ _ => by positivity) (fun k _ => hcoord k)
    _ = _ := by simp [← pow_mul,y]

theorem sum_square_gapShear_le {N : ℕ} (i j : Fin N) (x : Fin N → ℝ) :
    (∑ k, (gapShear i j x k)^2) ≤ (4*(N:ℝ))*(∑ k,x k^2) := by
  let S := ∑ k,x k^2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hx (k : Fin N) : x k^2 ≤ S :=
    Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ k)
  calc
    _ ≤ ∑ _k : Fin N,4*S := by
      apply Finset.sum_le_sum
      intro k _
      by_cases hk : k=i
      · subst k; rw [gapShear_same]; nlinarith [hx i,hx j,sq_nonneg (x i+x j)]
      · rw [gapShear_other i j k hk]; linarith [hx k]
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

/-- A product Gaussian times any polynomial envelope and one singular coordinate. -/
theorem integrable_coordinate_singularity {N : ℕ} (i : Fin N) {c s : ℝ}
    (hc : 0<c) (hs : -1<s) (q : ℕ) :
    Integrable (fun x : Fin N → ℝ => |x i|^s * coordinateEnvelope x^q *
      Real.exp (-c*(∑ k,x k^2))) := by
  let f : Fin N → ℝ → ℝ := fun k t =>
    (if i=k then |t|^s else 1)*(1+|t|)^q*Real.exp (-c*t^2)
  have hi : ∀ k,Integrable (f k) := by
    intro k
    by_cases hk : i=k
    · simpa [f,hk] using integrable_abs_rpow_polynomial_gaussian hc hs q
    · simpa [f,hk] using gaussian_polynomial_integrable hc q
  convert Integrable.fintype_prod hi using 1
  ext x
  simp only [f, Finset.prod_mul_distrib]
  rw [Finset.prod_ite_eq,if_pos (Finset.mem_univ i),Finset.prod_pow,
    ← Real.exp_sum,← Finset.mul_sum]
  rfl

theorem integrable_gap_singularity {N : ℕ} (i j : Fin N) (hij : i≠j)
    {c s : ℝ} (hc : 0<c) (hs : -1<s) (q : ℕ) :
    Integrable (fun x : Fin N → ℝ => |x i-x j|^s * coordinateEnvelope x^q *
      Real.exp (-c*(∑ k,x k^2))) := by
  have hN : (0:ℝ)<N := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
  let c' := c/(4*(N:ℝ))
  have hc' : 0<c' := by dsimp [c']; positivity
  have hi := integrable_coordinate_singularity i hc' hs ((2*N)*q)
  have hi' := ((gapShear_measurePreserving i j hij).integrable_comp hi.aestronglyMeasurable).2 hi
  apply hi'.mono'
  · exact (((measurable_pi_apply i).sub (measurable_pi_apply j)).abs.pow measurable_const).mul
      ((by unfold coordinateEnvelope; fun_prop : Continuous (fun x : Fin N → ℝ => coordinateEnvelope x)).measurable.pow_const q)
        |>.mul ((by fun_prop : Continuous (fun x : Fin N → ℝ => Real.exp (-c*(∑ k,x k^2)))).measurable)
        |>.aestronglyMeasurable
  · filter_upwards [] with x
    have hE0 : 0 ≤ coordinateEnvelope x := zero_le_one.trans (coordinateEnvelope_one_le x)
    have hEy0 : 0 ≤ coordinateEnvelope (gapShear i j x) := zero_le_one.trans (coordinateEnvelope_one_le _)
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    dsimp only [Function.comp_def]
    rw [gapShear_same]
    have hp : coordinateEnvelope x^q ≤ coordinateEnvelope (gapShear i j x)^((2*N)*q) := by
      simpa only [pow_mul] using pow_le_pow_left₀
        (zero_le_one.trans (coordinateEnvelope_one_le x)) (coordinateEnvelope_le_gapShear i j hij x) q
    have he : Real.exp (-c*(∑ k,x k^2)) ≤
        Real.exp (-c'*(∑ k,(gapShear i j x k)^2)) := by
      apply Real.exp_le_exp.mpr
      have hb := mul_le_mul_of_nonneg_left (sum_square_gapShear_le i j x) hc'.le
      have heq : c'*(4*(N:ℝ))=c := by dsimp [c']; field_simp
      rw [← mul_assoc,heq] at hb
      linarith
    exact mul_le_mul (mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg (abs_nonneg _) _)) he
      (Real.exp_pos _).le (by positivity)

end BourgadeHuang.RationalBulk
