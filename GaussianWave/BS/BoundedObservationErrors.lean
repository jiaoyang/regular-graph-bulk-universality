import Mathlib

/-! A bounded observation's mean-square error vanishes when its variance
and bias vanish, even on changing source probability spaces. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace GaussianWave.BS

/-- No integrability or second-error conclusion is assumed: both are derived
from the actual [0,1] bound. -/
theorem boundedObservation_second_error_tendsto
    (Ω : ℕ → Type*) [∀ n,MeasurableSpace (Ω n)]
    (P : ∀ n,Measure (Ω n)) [∀ n,IsProbabilityMeasure (P n)]
    (X : ∀ n,Ω n → ℝ) (hXm : ∀ n,Measurable (X n))
    (hX : ∀ n ω,0 ≤ X n ω ∧ X n ω ≤ 1)
    (c : ℝ) (hmean : Tendsto (fun n => ∫ ω,X n ω ∂P n) atTop (𝓝 c))
    (v : ℕ → ℝ)
    (hvariance : ∀ n,(∫ ω,(X n ω-∫ z,X n z ∂P n)^2 ∂P n) ≤ v n)
    (hv : Tendsto v atTop (𝓝 0)) :
    (∀ n,Integrable (fun ω => (X n ω-c)^2) (P n)) ∧
      Tendsto (fun n => ∫ ω,(X n ω-c)^2 ∂P n) atTop (𝓝 0) := by
  have hLp (n : ℕ) : MemLp (X n) 2 (P n) := MemLp.of_bound (hXm n).aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs,abs_of_nonneg (hX n ω).1]; exact (hX n ω).2))
  have hi (n : ℕ) (a : ℝ) : Integrable (fun ω => (X n ω-a)^2) (P n) :=
    (memLp_two_iff_integrable_sq ((hXm n).sub_const a).aestronglyMeasurable).1
      ((hLp n).sub (memLp_const a))
  refine ⟨fun n => hi n c,?_⟩
  have hb (n : ℕ) : (∫ ω,(X n ω-c)^2 ∂P n) ≤
      2*v n+2*((∫ ω,X n ω ∂P n)-c)^2 := by
    let a := ∫ ω,X n ω ∂P n
    have h := integral_mono (hi n c)
      (((hi n a).const_mul 2).add (integrable_const (2*(a-c)^2)))
      (fun ω => by
        change (X n ω-c)^2 ≤ 2*(X n ω-a)^2+2*(a-c)^2
        nlinarith [sq_nonneg (X n ω-(2*a-c))])
    simp only [Pi.add_apply] at h
    rw [integral_add ((hi n a).const_mul 2) (integrable_const _),integral_const_mul,integral_const] at h
    simp only [measureReal_univ_eq_one,one_smul] at h
    exact h.trans (add_le_add_right (mul_le_mul_of_nonneg_left (hvariance n) (by norm_num)) _)
  apply squeeze_zero (fun n => integral_nonneg (fun ω => sq_nonneg _)) hb
  have hc : Tendsto (fun _ : ℕ => c) atTop (𝓝 c) := tendsto_const_nhds
  simpa only [sub_self,zero_pow (by omega : 2 ≠ 0),mul_zero,add_zero] using
    (hv.const_mul 2).add (((hmean.sub hc).pow 2).const_mul 2)

end GaussianWave.BS
