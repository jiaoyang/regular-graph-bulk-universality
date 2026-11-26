import Mathlib.Probability.Distributions.Gaussian
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Tactic

/-! Gaussian entry moments, derived from the actual Gaussian measure. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace BourgadeHuang

theorem gaussian_integrable_exp (m : ℝ) (v : ℝ≥0) (t : ℝ) :
    Integrable (fun x : ℝ => Real.exp (t*x)) (gaussianReal m v) := by
  classical
  by_contra h
  have hm := mgf_gaussianReal (X := id) (p := gaussianReal m v) (Measure.map_id) t
  simp only [mgf, id_eq] at hm
  rw [integral_undef h] at hm
  exact (Real.exp_ne_zero _ ) hm.symm

theorem gaussian_integrableExpSet (m : ℝ) (v : ℝ≥0) :
    integrableExpSet id (gaussianReal m v) = Set.univ := by
  ext t
  simp only [Set.mem_univ, iff_true]
  exact gaussian_integrable_exp m v t

theorem gaussian_integrable_abs_pow (m : ℝ) (v : ℝ≥0) (q : ℕ) :
    Integrable (fun x : ℝ => |x|^q) (gaussianReal m v) := by
  have h := integrable_pow_abs_mul_exp_of_integrable_exp_mul
    (X := id) (v := 0) (t := 1) (by norm_num)
    (gaussian_integrable_exp m v (0+1))
    (gaussian_integrable_exp m v (0-1)) q
  simpa using h

theorem gaussian_integrable_pow (m : ℝ) (v : ℝ≥0) (q : ℕ) :
    Integrable (fun x : ℝ => x^q) (gaussianReal m v) := by
  simpa using integrable_pow_mul_exp_of_mem_interior_integrableExpSet
    (X := id) (μ := gaussianReal m v) (v := 0)
    (by simp [gaussian_integrableExpSet]) q

theorem gaussian_integral_exp_first (m : ℝ) (v : ℝ≥0) (t : ℝ) :
    (∫ x : ℝ, x * Real.exp (t*x) ∂gaussianReal m v) =
      Real.exp (m*t+v*t^2/2) * (m+v*t) := by
  have h := hasDerivAt_mgf (X := id) (μ := gaussianReal m v) (t := t)
    (by simp [gaussian_integrableExpSet])
  have he : mgf id (gaussianReal m v) = fun t : ℝ => Real.exp (m*t+v*t^2/2) := by
    funext u
    exact mgf_gaussianReal (X := id) (p := gaussianReal m v) Measure.map_id u
  rw [he] at h
  have hd : HasDerivAt (fun u : ℝ => Real.exp (m*u+v*u^2/2))
      (Real.exp (m*t+v*t^2/2) * (m+v*t)) t := by
    convert (((hasDerivAt_id t).const_mul m).add
      ((((hasDerivAt_id t).pow 2).const_mul (v:ℝ)).div_const 2)).exp using 1 <;>
        simp only [id_eq] <;> ring
  exact h.unique hd

theorem gaussian_integral_id (m : ℝ) (v : ℝ≥0) :
    (∫ x : ℝ, x ∂gaussianReal m v) = m := by
  simpa using gaussian_integral_exp_first m v 0

theorem gaussian_integral_sq (m : ℝ) (v : ℝ≥0) :
    (∫ x : ℝ, x^2 ∂gaussianReal m v) = m^2+v := by
  have h := hasDerivAt_integral_pow_mul_exp_real (X := id)
    (μ := gaussianReal m v) (t := 0) (by simp [gaussian_integrableExpSet]) 1
  simp only [pow_one, id_eq] at h
  have he : (fun t : ℝ => ∫ x : ℝ, x * Real.exp (t*x) ∂gaussianReal m v) =
      fun t : ℝ => Real.exp (m*t+v*t^2/2) * (m+v*t) := by
    funext t
    exact gaussian_integral_exp_first m v t
  rw [he] at h
  have hd : HasDerivAt
      (fun t : ℝ => Real.exp (m*t+v*t^2/2) * (m+v*t)) (m^2+v) 0 := by
    have hbase := ((hasDerivAt_id (0:ℝ)).const_mul m).add
      ((((hasDerivAt_id (0:ℝ)).pow 2).const_mul (v:ℝ)).div_const 2)
    have hlin := ((hasDerivAt_id (0:ℝ)).const_mul (v:ℝ)).const_add m
    convert hbase.exp.mul hlin using 1 <;> simp <;> ring
  simpa using h.unique hd

end BourgadeHuang
