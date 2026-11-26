import Mathlib

/-! # Standard real Gaussian moments from its actual probability law -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Topology

namespace GeneralizedBulk.Gaussian

def standardNormal : Measure ℝ := gaussianReal 0 1

instance : IsProbabilityMeasure standardNormal := by
  unfold standardNormal
  infer_instance

theorem standardNormal_mgf (t : ℝ) :
    mgf id standardNormal t = Real.exp (t ^ 2 / 2) := by
  have hm : Measure.map id standardNormal = gaussianReal 0 1 := by
    simp [standardNormal]
  simpa using mgf_gaussianReal hm t

theorem standardNormal_integrableExpSet : integrableExpSet id standardNormal = Set.univ := by
  ext t
  simp only [integrableExpSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact mgf_pos_iff.mp (by rw [standardNormal_mgf]; exact Real.exp_pos _)

theorem standardNormal_zero_interior :
    (0 : ℝ) ∈ interior (integrableExpSet id standardNormal) := by
  rw [standardNormal_integrableExpSet, interior_univ]
  trivial

theorem standardNormal_integrable_pow (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) standardNormal := by
  exact integrable_pow_of_mem_interior_integrableExpSet standardNormal_zero_interior n

private def f0 (x : ℝ) : ℝ := Real.exp (x ^ 2 / 2)
private def f1 (x : ℝ) : ℝ := x * f0 x
private def f2 (x : ℝ) : ℝ := (x ^ 2 + 1) * f0 x
private def f3 (x : ℝ) : ℝ := (x ^ 3 + 3 * x) * f0 x
private def f4 (x : ℝ) : ℝ := (x ^ 4 + 6 * x ^ 2 + 3) * f0 x

private theorem df0 (x : ℝ) : HasDerivAt f0 (f1 x) x := by
  have hd := ((hasDerivAt_id x).pow 2).div_const 2
  convert hd.exp using 1 <;> simp [f0, f1] <;> ring

private theorem df1 (x : ℝ) : HasDerivAt f1 (f2 x) x := by
  convert (hasDerivAt_id x).mul (df0 x) using 1 <;> simp [f0, f1, f2] <;> ring

private theorem df2 (x : ℝ) : HasDerivAt f2 (f3 x) x := by
  convert (((hasDerivAt_id x).pow 2).add_const 1).mul (df0 x) using 1 <;>
    simp [f0, f1, f2, f3] <;> ring

private theorem df3 (x : ℝ) : HasDerivAt f3 (f4 x) x := by
  convert (((hasDerivAt_id x).pow 3).add ((hasDerivAt_id x).const_mul 3)).mul (df0 x)
    using 1 <;> simp [f0, f1, f3, f4] <;> ring

private theorem iterated_f1 : iteratedDeriv 1 f0 = f1 := by
  funext x
  simpa using (df0 x).deriv

private theorem iterated_f2 : iteratedDeriv 2 f0 = f2 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iterated_f1]
  funext x
  exact (df1 x).deriv

private theorem iterated_f3 : iteratedDeriv 3 f0 = f3 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ, iterated_f2]
  funext x
  exact (df2 x).deriv

private theorem iterated_f4 : iteratedDeriv 4 f0 = f4 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, iteratedDeriv_succ, iterated_f3]
  funext x
  exact (df3 x).deriv

theorem standardNormal_moment_zero : (∫ x : ℝ, x ^ 0 ∂standardNormal) = 1 := by simp

theorem standardNormal_moment_one : (∫ x : ℝ, x ∂standardNormal) = 0 := by
  have h := iteratedDeriv_mgf_zero standardNormal_zero_interior 1
  rw [show mgf id standardNormal = f0 from funext standardNormal_mgf, iterated_f1] at h
  simpa [f1, f0] using h.symm

theorem standardNormal_moment_two : (∫ x : ℝ, x ^ 2 ∂standardNormal) = 1 := by
  have h := iteratedDeriv_mgf_zero standardNormal_zero_interior 2
  rw [show mgf id standardNormal = f0 from funext standardNormal_mgf, iterated_f2] at h
  simpa [f2, f0] using h.symm

theorem standardNormal_moment_three : (∫ x : ℝ, x ^ 3 ∂standardNormal) = 0 := by
  have h := iteratedDeriv_mgf_zero standardNormal_zero_interior 3
  rw [show mgf id standardNormal = f0 from funext standardNormal_mgf, iterated_f3] at h
  simpa [f3, f0] using h.symm

theorem standardNormal_moment_four : (∫ x : ℝ, x ^ 4 ∂standardNormal) = 3 := by
  have h := iteratedDeriv_mgf_zero standardNormal_zero_interior 4
  rw [show mgf id standardNormal = f0 from funext standardNormal_mgf, iterated_f4] at h
  simpa [f4, f0] using h.symm

end GeneralizedBulk.Gaussian
