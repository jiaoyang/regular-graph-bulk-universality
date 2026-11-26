import GeneralizedBulk.Gaussian.CoordinateLaw
import GeneralizedBulk.Entropy.GaussianTail
import GeneralizedBulk.Entropy.IntegerClippingEntropy
import GeneralizedBulk.Entropy.GridCells

/-! Actual global clipping probabilities for arbitrary correlated Gaussian
vectors.  The union bound uses no independence of the coordinates. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical NNReal

namespace GeneralizedBulk.Entropy
open GeneralizedBulk.Gaussian

theorem gaussianReal_abs_tail_le_uniform_mean (m M : ℝ) (hm : |m| ≤ M)
    (v c : ℝ≥0) (hvar : v ≤ c) (hc : 0 < c) (R : ℝ) (hR : M ≤ R) :
    (gaussianReal m v).real {x | R ≤ |x|} ≤
      2*Real.exp (-(R-M)^2/(2*(c : ℝ))) := by
  apply (gaussianReal_abs_tail_le m v c hvar R (hm.trans hR)).trans
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by norm_num)
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith [sq_nonneg (R-M),sq_nonneg (R-|m|)]

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem correlated_coordinate_abs_tail_le (A : Matrix I J ℝ) (a : I → ℝ) (i : I)
    (M : ℝ) (hmean : |a i| ≤ M) (c : ℝ≥0) (hc : 0 < c)
    (hvar : coordinateVariance A i ≤ c) (R : ℝ) (hR : M ≤ R) :
    (linearImageGaussian A).real {x | R ≤ |a i+x i|} ≤
      2*Real.exp (-(R-M)^2/(2*(c : ℝ))) := by
  have hm : Measurable (fun x : I → ℝ => a i+x i) := by fun_prop
  have hs : MeasurableSet {x : ℝ | R ≤ |x|} := isClosed_le continuous_const continuous_abs |>.measurableSet
  change (linearImageGaussian A ((fun x : I → ℝ => a i+x i) ⁻¹' {x | R ≤ |x|})).toReal ≤ _
  rw [← Measure.map_apply hm hs,linearImageGaussian_shifted_coordinate]
  exact gaussianReal_abs_tail_le_uniform_mean _ M hmean _ c hvar hc R hR

theorem correlated_global_abs_tail_le (A : Matrix I J ℝ) (a : I → ℝ)
    (M : ℝ) (hmean : ∀ i,|a i| ≤ M) (c : ℝ≥0) (hc : 0 < c)
    (hvar : ∀ i,coordinateVariance A i ≤ c) (R : ℝ) (hR : M ≤ R) :
    (linearImageGaussian A).real {x | ∃ i,R ≤ |a i+x i|} ≤
      2*(Fintype.card I : ℝ)*Real.exp (-(R-M)^2/(2*(c : ℝ))) := by
  have he : {x : I → ℝ | ∃ i,R ≤ |a i+x i|} = ⋃ i,{x | R ≤ |a i+x i|} := by ext x; simp
  rw [he]
  apply (measureReal_iUnion_fintype_le _).trans
  calc
    _ ≤ ∑ _i : I,2*Real.exp (-(R-M)^2/(2*(c : ℝ))) :=
      Finset.sum_le_sum (fun i hi => correlated_coordinate_abs_tail_le A a i M (hmean i) c hc (hvar i) R hR)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

theorem integerClippingTail_grid_implies_abs {m : ℕ} (K : ℕ) (a : ℝ) (ha : 0 < a)
    (x : Fin m → ℝ) (hx : integerClippingTail K (gridLabel a x)) :
    ∃ i,(K : ℝ)*a ≤ |x i| := by
  obtain ⟨i,hi | hi⟩ := hx
  · refine ⟨i,?_⟩
    have hfloor : x i/a < -(K : ℝ) := by
      have h := (Int.floor_lt (z := -(K : ℤ)) (a := x i/a)).mp hi
      simpa only [Int.cast_neg,Int.cast_natCast] using h
    have hxneg : x i < -(K : ℝ)*a := (div_lt_iff₀ ha).mp hfloor
    exact le_trans (by linarith) (neg_le_abs (x i))
  · refine ⟨i,?_⟩
    have hfloor : (K : ℝ) ≤ x i/a := (Int.le_floor).mp hi
    exact ((le_div_iff₀ ha).mp hfloor).trans (le_abs_self _)

theorem correlated_grid_clipping_probability_le {m : ℕ} (A : Matrix (Fin m) J ℝ)
    (a : Fin m → ℝ) (M : ℝ) (hmean : ∀ i,|a i| ≤ M)
    (c : ℝ≥0) (hc : 0 < c) (hvar : ∀ i,coordinateVariance A i ≤ c)
    (δ : ℝ) (hδ : 0 < δ) (K : ℕ) (hR : M ≤ (K : ℝ)*δ) :
    (linearImageGaussian A).real {x | integerClippingTail K (gridLabel δ (a+x))} ≤
      2*(m : ℝ)*Real.exp (-((K : ℝ)*δ-M)^2/(2*(c : ℝ))) := by
  apply (measureReal_mono (fun x hx => integerClippingTail_grid_implies_abs K δ hδ (a+x) hx)).trans
  simpa only [Fintype.card_fin,Pi.add_apply] using
    correlated_global_abs_tail_le A a M hmean c hc hvar ((K : ℝ)*δ) hR

end GeneralizedBulk.Entropy
