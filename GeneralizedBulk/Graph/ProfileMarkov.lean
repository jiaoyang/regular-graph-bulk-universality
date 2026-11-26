import Mathlib

/-! Uniform over all finite empirical profiles by Markov's inequality and
one union bound. The expectation estimate is supplied by the actual
configuration count, rather than an external entropy hypothesis. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace GeneralizedBulk.Graph

variable {Ω A : Type*} [MeasurableSpace Ω] [Fintype A]

set_option maxHeartbeats 1000000 in
theorem uniform_profile_markov (μ : Measure Ω) [IsFiniteMeasure μ]
    (Z : A → Ω → ℝ) (hZ : ∀ a, Integrable (Z a) μ)
    (hZnonneg : ∀ a ω, 0 ≤ Z a ω) (F : A → ℝ)
    (hE : ∀ a, (∫ ω, Z a ω ∂μ) ≤ Real.exp (F a)) (b t : ℝ)
    (hb : Real.log (Fintype.card A) ≤ b) :
    μ.real {ω | ∃ a, Real.exp (F a + b + t) ≤ Z a ω} ≤ Real.exp (-t) := by
  rcases isEmpty_or_nonempty A with hA | hA
  · letI := hA
    simp
    exact le_of_lt (Real.exp_pos _)
  · letI := hA
    have hcard : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
    have ht (a : A) : μ.real {ω | Real.exp (F a + b + t) ≤ Z a ω} ≤ Real.exp (-b-t) := by
      have hm := mul_meas_ge_le_integral_of_nonneg
        (Filter.Eventually.of_forall (hZnonneg a)) (hZ a) (Real.exp (F a+b+t))
      have he := hm.trans (hE a)
      have hx : Real.exp (F a+b+t) * Real.exp (-b-t) = Real.exp (F a) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [← hx] at he
      exact (mul_le_mul_left (Real.exp_pos _)).mp he
    have heq : {ω | ∃ a, Real.exp (F a+b+t) ≤ Z a ω} =
        ⋃ a, {ω | Real.exp (F a+b+t) ≤ Z a ω} := by ext ω; simp
    rw [heq]
    calc
      _ ≤ ∑ a : A, μ.real {ω | Real.exp (F a+b+t) ≤ Z a ω} := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _a : A, Real.exp (-b-t) := Finset.sum_le_sum (fun a ha => ht a)
      _ = (Fintype.card A : ℝ) * Real.exp (-b-t) := by simp
      _ ≤ Real.exp b * Real.exp (-b-t) := by
        apply mul_le_mul_of_nonneg_right ((Real.log_le_iff_le_exp hcard).mp hb)
          (le_of_lt (Real.exp_pos _))
      _ = Real.exp (-t) := by rw [← Real.exp_add]; congr 1; ring

end GeneralizedBulk.Graph
