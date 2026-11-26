import GeneralizedBulk.Entropy.FullChaosEvaluation

/-! Actual exponential integrability used to prove Hermite completeness. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace GeneralizedBulk.Entropy.Hermite
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem integrable_exp_linearForm (t : I → ℝ) (r : ℝ) :
    Integrable (fun x => Real.exp (r * linearForm t x)) (standardGaussian I) := by
  have hscalar (s : ℝ) : Integrable (fun x : ℝ => Real.exp (s * x)) GeneralizedBulk.Gaussian.standardNormal := by
    apply mgf_pos_iff.mp
    have hm := GeneralizedBulk.Gaussian.centeredGaussian_mgf (1 : ℝ≥0) s
    change 0 < mgf id (gaussianReal 0 1) s
    rw [hm]
    exact Real.exp_pos _
  letI : MeasureSpace ℝ := ⟨GeneralizedBulk.Gaussian.standardNormal⟩
  letI : IsProbabilityMeasure (volume : Measure ℝ) := inferInstanceAs (IsProbabilityMeasure GeneralizedBulk.Gaussian.standardNormal)
  have hp := Integrable.fintype_prod (fun i : I => hscalar (r * t i))
  have heq : (fun x : I → ℝ => Real.exp (r * linearForm t x)) =
      fun x => ∏ i : I, Real.exp ((r * t i) * x i) := by
    funext x
    rw [linearForm, Finset.mul_sum, Real.exp_sum]
    congr 1
    funext i
    ring
  rw [heq]
  simpa only [standardGaussian, volume_pi] using hp

theorem integrable_exp_abs_linearForm (t : I → ℝ) (r : ℝ) :
    Integrable (fun x => Real.exp (r * |linearForm t x|)) (standardGaussian I) :=
  integrable_exp_mul_abs (integrable_exp_linearForm t r) (integrable_exp_linearForm t (-r))

theorem memLp_exp_abs_linearForm_two (t : I → ℝ) :
    MemLp (fun x => Real.exp |linearForm t x|) 2 (standardGaussian I) := by
  have hc : Continuous (fun x : I → ℝ => Real.exp |linearForm t x|) := by
    unfold linearForm
    fun_prop
  apply (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).mpr
  have h := integrable_exp_abs_linearForm t 2
  convert h using 1
  funext x
  rw [← Real.exp_nat_mul]
  norm_num

/-- Cauchy--Schwarz supplies the true exponential majorant for every actual
Gaussian L² vector, not merely for polynomial functions. -/
theorem integrable_abs_Lp_mul_exp_abs_linearForm (f : Lp ℝ 2 (standardGaussian I)) (t : I → ℝ) :
    Integrable (fun x => |f x| * Real.exp |linearForm t x|) (standardGaussian I) :=
  (Lp.memLp f).norm.integrable_mul (memLp_exp_abs_linearForm_two t)

end GeneralizedBulk.Entropy.Hermite
