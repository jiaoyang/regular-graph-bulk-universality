import GeneralizedBulk.Entropy.HermiteMultivariate
import GeneralizedBulk.Analysis.PiDensity
import GeneralizedBulk.Entropy.MehlerEnvelope

/-! Gaussian integrability of every polynomial times the linear exponential
used in the uniform high-noise Mehler bounds. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace GeneralizedBulk.Entropy.Mehler
open GeneralizedBulk.Gaussian GeneralizedBulk.Analysis GeneralizedBulk.Entropy.Hermite
variable {I : Type*} [Fintype I]

def coordinateL1 (z : I → ℝ) : ℝ := ∑ i, |z i|

theorem coordinateL1_nonneg (z : I → ℝ) : 0 ≤ coordinateL1 z :=
  Finset.sum_nonneg (fun i _ => abs_nonneg _)

theorem continuous_coordinateL1 : Continuous (coordinateL1 : (I → ℝ) → ℝ) := by
  unfold coordinateL1
  fun_prop

theorem abs_cross_le_coordinateL1 (y z : I → ℝ) :
    |∑ i, z i * y i| ≤ coordinateL1 y * coordinateL1 z := by
  calc
    _ ≤ ∑ i, |z i * y i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |y i| * |z i| := by
      simp_rw [abs_mul, mul_comm |z _|]
    _ ≤ (∑ i, |y i|) * (∑ i, |z i|) := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => abs_nonneg (z j)) hi)
        (abs_nonneg (y i))

theorem sum_sq_le_coordinateL1_sq (y : I → ℝ) :
    (∑ i, y i ^ 2) ≤ coordinateL1 y ^ 2 := by
  simpa only [sq_abs] using Finset.sum_sq_le_sq_sum_of_nonneg (fun i (_ : i ∈ Finset.univ) => abs_nonneg (y i))

theorem standardNormal_integrable_exp_abs (C : ℝ) :
    Integrable (fun x : ℝ => Real.exp (C * |x|)) standardNormal := by
  have hp : C ∈ integrableExpSet id standardNormal := by
    rw [standardNormal_integrableExpSet]
    trivial
  have hn : -C ∈ integrableExpSet id standardNormal := by
    rw [standardNormal_integrableExpSet]
    trivial
  exact integrable_exp_mul_abs hp hn

theorem integrable_exp_coordinateL1 (C : ℝ) :
    Integrable (fun z : I → ℝ => Real.exp (C * coordinateL1 z)) (standardGaussian I) := by
  have hi := integrable_pi_product (fun _ : I => standardNormal)
    (fun _ x => Real.exp (C * |x|)) (fun _ => standardNormal_integrable_exp_abs C)
  convert hi using 1
  funext z
  rw [coordinateL1, Finset.mul_sum, Real.exp_sum]

/-- An explicit exponential majorant absorbs any fixed polynomial degree. -/
theorem polynomial_envelope_le_exp (Z : ℝ) (hZ : 0 ≤ Z) (n : ℕ) :
    (1 + Z ^ 2) ^ n ≤ ((2 * n).factorial : ℝ) * Real.exp (1 + Z) := by
  have hbase : 1 + Z ^ 2 ≤ (1 + Z) ^ 2 := by nlinarith
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + Z ^ 2) hbase n
  have he := Real.pow_div_factorial_le_exp (1 + Z) (show 0 ≤ 1 + Z by positivity) (2 * n)
  have hfac : (0 : ℝ) < (2 * n).factorial := by positivity
  have hh := (div_le_iff₀ hfac).mp he
  rw [← pow_mul] at hp
  nlinarith [hp]

theorem integrable_polynomial_exp_coordinateL1 (C : ℝ) (n : ℕ) :
    Integrable (fun z : I → ℝ => Real.exp (C * coordinateL1 z) *
      (1 + coordinateL1 z ^ 2) ^ n) (standardGaussian I) := by
  let A : ℝ := ((2 * n).factorial : ℝ) * Real.exp 1
  have hi := (integrable_exp_coordinateL1 (I := I) (C + 1)).const_mul A
  apply hi.mono' (show Continuous (fun z : I → ℝ => Real.exp (C * coordinateL1 z) *
    (1 + coordinateL1 z ^ 2) ^ n) from by unfold coordinateL1; fun_prop).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h := mul_le_mul_of_nonneg_left
    (polynomial_envelope_le_exp (coordinateL1 z) (coordinateL1_nonneg z) n)
    (Real.exp_pos (C * coordinateL1 z)).le
  convert h using 1
  dsimp [A]
  have he : Real.exp 1 * Real.exp ((C + 1) * coordinateL1 z) =
      Real.exp (C * coordinateL1 z) * Real.exp (1 + coordinateL1 z) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1 <;> ring
  nlinarith [congrArg (fun t => ((2 * n).factorial : ℝ) * t) he]

end GeneralizedBulk.Entropy.Mehler
