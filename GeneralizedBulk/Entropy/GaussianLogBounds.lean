import GeneralizedBulk.Entropy.GaussianMixtureTranslation
import GeneralizedBulk.Entropy.GaussianEnvelope

/-! Quadratic logarithmic envelopes for genuine finite Gaussian mixtures. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace GeneralizedBulk.Entropy
open GeneralizedBulk.Gaussian GeneralizedBulk.Analysis Hermite Mehler
variable {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S]

theorem abs_log_weighted_sum_le (weight f : S → ℝ) (hw : ∀ s, 0 ≤ weight s)
    (hnorm : ∑ s, weight s = 1) (hf : ∀ s, 0 < f s) (R : ℝ) (hbound : ∀ s, |Real.log (f s)| ≤ R) :
    |Real.log (∑ s, weight s * f s)| ≤ R := by
  have hp := positive_weighted_sum weight f hw hnorm hf
  have hlow (s) : Real.exp (-R) ≤ f s := by
    rw [← Real.exp_log (hf s)]
    exact Real.exp_le_exp.mpr (abs_le.mp (hbound s)).1
  have hhigh (s) : f s ≤ Real.exp R := by
    rw [← Real.exp_log (hf s)]
    exact Real.exp_le_exp.mpr (abs_le.mp (hbound s)).2
  have hlo : Real.exp (-R) ≤ ∑ s, weight s * f s := by
    calc
      _ = ∑ s, weight s * Real.exp (-R) := by rw [← Finset.sum_mul, hnorm, one_mul]
      _ ≤ _ := Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hlow s) (hw s))
  have hhi : (∑ s, weight s * f s) ≤ Real.exp R := by
    calc
      _ ≤ ∑ s, weight s * Real.exp R := Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hhigh s) (hw s))
      _ = _ := by rw [← Finset.sum_mul, hnorm, one_mul]
  apply abs_le.mpr
  constructor
  · have hh := Real.log_le_log (Real.exp_pos (-R)) hlo
    rwa [Real.log_exp] at hh
  · have hh := Real.log_le_log hp hhi
    rwa [Real.log_exp] at hh

theorem coordinateL1_add_le (x y : I → ℝ) : coordinateL1 (x + y) ≤ coordinateL1 x + coordinateL1 y := by
  simpa only [coordinateL1, Pi.add_apply, Finset.sum_add_distrib] using
    Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => abs_add_le (x i) (y i))

theorem coordinateL1_sub_le (x y : I → ℝ) : coordinateL1 (x - y) ≤ coordinateL1 x + coordinateL1 y := by
  simpa only [coordinateL1, Pi.sub_apply, Finset.sum_add_distrib] using
    Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => abs_sub (x i) (y i))

def matrixEntryL1 (A : Matrix I I ℝ) : ℝ := ∑ i, ∑ j, |A i j|

theorem matrixEntryL1_nonneg (A : Matrix I I ℝ) : 0 ≤ matrixEntryL1 A :=
  Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _))

theorem coordinateL1_mulVec_le (A : Matrix I I ℝ) (x : I → ℝ) :
    coordinateL1 (A.mulVec x) ≤ matrixEntryL1 A * coordinateL1 x := by
  unfold coordinateL1 matrixEntryL1
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  calc
    |A.mulVec x i| ≤ ∑ j, |A i j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |A i j| * |x j| := by simp_rw [abs_mul]
    _ ≤ ∑ j, |A i j| * ∑ t, |x t| := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun t _ => abs_nonneg (x t)) hj) (abs_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

theorem standardGaussian_memLp_coordinateL1 : MemLp (coordinateL1 (I := I)) 2 (standardGaussian I) := by
  apply memLp_finset_sum
  intro i hi
  have hm : MemLp (fun x : I → ℝ => x i) 2 (standardGaussian I) :=
    (memLp_two_iff_integrable_sq (measurable_pi_apply i).aestronglyMeasurable).mpr
      (standardGaussian_integrable_coordinate_pow i 2)
  simpa only [Real.norm_eq_abs] using hm.norm

theorem standardGaussian_integrable_affine_coordinateL1_sq (mean : I → ℝ) (A : Matrix I I ℝ) :
    Integrable (fun z => coordinateL1 (mean + A.mulVec z) ^ 2) (standardGaussian I) := by
  have hmajor := ((memLp_const (coordinateL1 mean) (p := (2 : ENNReal)) (μ := standardGaussian I)).add
    (standardGaussian_memLp_coordinateL1.const_mul (matrixEntryL1 A))).integrable_sq
  have hc : Continuous (fun z : I → ℝ => coordinateL1 (mean + A.mulVec z) ^ 2) :=
    (continuous_coordinateL1.comp (continuous_const.add (Matrix.toLin' A).toContinuousLinearMap.continuous)).pow 2
  apply hmajor.mono' hc.aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (coordinateL1_nonneg _) ((coordinateL1_add_le _ _).trans
    (add_le_add_left (coordinateL1_mulVec_le A z) _)) 2

theorem abs_log_affineGaussianPDF_le (mean : I → ℝ) (M : Matrix I I ℝ) (hM : M.det ≠ 0) (x : I → ℝ) :
    |Real.log (affineGaussianPDF mean M x)| ≤
      |Real.log (|M.det|)| + (Fintype.card I : ℝ) / 2 * |Real.log (2 * Real.pi)| +
        matrixEntryL1 M⁻¹ ^ 2 * (coordinateL1 x ^ 2 + coordinateL1 mean ^ 2) := by
  rw [log_affineGaussianPDF mean M hM]
  have hquad : (∑ i, (M⁻¹.mulVec (x - mean) i) ^ 2) ≤
      2 * matrixEntryL1 M⁻¹ ^ 2 * (coordinateL1 x ^ 2 + coordinateL1 mean ^ 2) := by
    have hh := (sum_sq_le_coordinateL1_sq (M⁻¹.mulVec (x - mean))).trans
      (pow_le_pow_left₀ (coordinateL1_nonneg _) (coordinateL1_mulVec_le M⁻¹ (x - mean)) 2)
    have hsub := pow_le_pow_left₀ (coordinateL1_nonneg _) (coordinateL1_sub_le x mean) 2
    have hsq : (coordinateL1 x + coordinateL1 mean) ^ 2 ≤
        2 * (coordinateL1 x ^ 2 + coordinateL1 mean ^ 2) := by nlinarith [sq_nonneg (coordinateL1 x - coordinateL1 mean)]
    have hm := mul_le_mul_of_nonneg_left (hsub.trans hsq) (sq_nonneg (matrixEntryL1 M⁻¹))
    rw [mul_pow] at hh
    nlinarith
  calc
    _ ≤ |-Real.log (|M.det|)| + |(Fintype.card I : ℝ) / 2 * Real.log (2 * Real.pi)| +
        |(∑ i, (M⁻¹.mulVec (x - mean) i) ^ 2) / 2| := (abs_sub _ _).trans (add_le_add_right (abs_sub _ _) _)
    _ = |Real.log (|M.det|)| + (Fintype.card I : ℝ) / 2 * |Real.log (2 * Real.pi)| +
        (∑ i, (M⁻¹.mulVec (x - mean) i) ^ 2) / 2 := by
      rw [abs_neg, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (Fintype.card I : ℝ) / 2),
        abs_of_nonneg (by positivity : 0 ≤ (∑ i, (M⁻¹.mulVec (x - mean) i) ^ 2) / 2)]
    _ ≤ _ := by linarith

end GeneralizedBulk.Entropy
