import Mathlib

/-! Actual scalar Gaussian Chernoff tails, derived from the proved MGF. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

namespace GeneralizedBulk.Entropy

variable {Ω : Type*} [MeasurableSpace Ω]

theorem hasSubgaussian_of_gaussianLaw (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (v c : ℝ≥0) (hvar : v ≤ c) (hX : Measure.map X μ = gaussianReal 0 v) :
    HasSubgaussianMGF X c μ where
  integrable_exp_mul t := mgf_pos_iff.mp (by rw [mgf_gaussianReal hX t]; exact Real.exp_pos _)
  mgf_le t := by
    rw [mgf_gaussianReal hX t]
    apply Real.exp_le_exp.mpr
    have hv : (v : ℝ) ≤ c := by exact_mod_cast hvar
    nlinarith [mul_le_mul_of_nonneg_right hv (sq_nonneg t)]

theorem hasSubgaussian_neg (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (c : ℝ≥0) (hX : HasSubgaussianMGF X c μ) :
    HasSubgaussianMGF (fun x => -X x) c μ where
  integrable_exp_mul t := by
    convert hX.integrable_exp_mul (-t) using 1
    funext x
    congr 1
    ring
  mgf_le t := by
    change mgf (-X) μ t ≤ _
    rw [mgf_neg]
    simpa only [neg_sq] using hX.mgf_le (-t)

set_option maxHeartbeats 1000000 in
theorem gaussianReal_centered_abs_tail_le (m : ℝ) (v c : ℝ≥0) (hvar : v ≤ c)
    (R : ℝ) (hR : 0 ≤ R) :
    (gaussianReal m v).real {x | R ≤ |x-m|} ≤ 2*Real.exp (-R^2/(2*(c : ℝ))) := by
  let X : ℝ → ℝ := fun x => x-m
  have hmap : Measure.map X (gaussianReal m v) = gaussianReal 0 v := by
    simpa only [X,sub_eq_add_neg,add_neg_cancel] using (gaussianReal_map_add_const (μ := m) (v := v) (-m))
  have hX := hasSubgaussian_of_gaussianLaw (gaussianReal m v) X v c hvar hmap
  have hneg := hasSubgaussian_neg (gaussianReal m v) X c hX
  have hsub : {x : ℝ | R ≤ |x-m|} ⊆ {x | R ≤ X x} ∪ {x | R ≤ -X x} := by
    intro x hx
    change R ≤ |x-m| at hx
    rcases le_total 0 (x-m) with h | h
    · left
      change R ≤ X x
      simpa only [X,abs_of_nonneg h] using hx
    · right
      change R ≤ -X x
      simpa only [X,abs_of_nonpos h] using hx
  calc
    _ ≤ (gaussianReal m v).real ({x | R ≤ X x} ∪ {x | R ≤ -X x}) := measureReal_mono hsub
    _ ≤ (gaussianReal m v).real {x | R ≤ X x}+(gaussianReal m v).real {x | R ≤ -X x} := measureReal_union_le _ _
    _ ≤ Real.exp (-R^2/(2*(c : ℝ)))+Real.exp (-R^2/(2*(c : ℝ))) :=
      add_le_add (hX.measure_ge_le hR) (hneg.measure_ge_le hR)
    _ = _ := by ring

theorem gaussianReal_abs_tail_le (m : ℝ) (v c : ℝ≥0) (hvar : v ≤ c)
    (R : ℝ) (hR : |m| ≤ R) :
    (gaussianReal m v).real {x | R ≤ |x|} ≤ 2*Real.exp (-(R-|m|)^2/(2*(c : ℝ))) := by
  apply (measureReal_mono (μ := gaussianReal m v)
    (show {x : ℝ | R ≤ |x|} ⊆ {x | R-|m| ≤ |x-m|} from by
      intro x hx
      change R ≤ |x| at hx
      change R-|m| ≤ |x-m|
      have h := abs_sub_le x m 0
      simp only [sub_zero] at h
      linarith)).trans
  exact gaussianReal_centered_abs_tail_le m v c hvar (R-|m|) (sub_nonneg.mpr hR)

end GeneralizedBulk.Entropy
