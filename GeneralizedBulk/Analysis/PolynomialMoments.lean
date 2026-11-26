import Mathlib

/-! Polynomial observables are genuinely integrable under coordinate moment bounds. -/
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace GeneralizedBulk.Analysis

structure AllMoments {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℂ) : Prop where
  measurable : AEStronglyMeasurable f μ
  norm_pow : ∀ n : ℕ, Integrable (fun ω => ‖f ω‖ ^ n) μ

namespace AllMoments
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f g : Ω → ℂ}

theorem integrable (hf : AllMoments μ f) : Integrable f μ :=
  (integrable_norm_iff hf.measurable).1 (by simpa using hf.norm_pow 1)

theorem const [IsFiniteMeasure μ] (c : ℂ) : AllMoments μ (fun _ : Ω => c) :=
  ⟨aestronglyMeasurable_const, fun _ => integrable_const _⟩

theorem add (hf : AllMoments μ f) (hg : AllMoments μ g) :
    AllMoments μ (fun ω => f ω + g ω) := by
  refine ⟨hf.measurable.add hg.measurable, fun n => ?_⟩
  apply (((hf.norm_pow n).add (hg.norm_pow n)).const_mul ((2 : ℝ) ^ (n - 1))).mono'
    (((hf.measurable.add hg.measurable).norm).pow n)
  filter_upwards [] with ω
  simp only [Pi.pow_apply, Pi.add_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) _).trans
    (add_pow_le (norm_nonneg _) (norm_nonneg _) _)

theorem mul (hf : AllMoments μ f) (hg : AllMoments μ g) :
    AllMoments μ (fun ω => f ω * g ω) := by
  refine ⟨hf.measurable.mul hg.measurable, fun n => ?_⟩
  have hfn : MemLp (fun ω => ‖f ω‖ ^ n) 2 μ :=
    (memLp_two_iff_integrable_sq (hf.measurable.norm.pow n)).2
      (by simpa only [Pi.pow_apply, ← pow_mul] using hf.norm_pow (n * 2))
  have hgn : MemLp (fun ω => ‖g ω‖ ^ n) 2 μ :=
    (memLp_two_iff_integrable_sq (hg.measurable.norm.pow n)).2
      (by simpa only [Pi.pow_apply, ← pow_mul] using hg.norm_pow (n * 2))
  simpa only [norm_mul, mul_pow, Pi.mul_apply] using hfn.integrable_mul hgn

theorem pow [IsFiniteMeasure μ] (hf : AllMoments μ f) (n : ℕ) :
    AllMoments μ (fun ω => f ω ^ n) := by
  induction n with
  | zero => simpa using (const (μ := μ) 1)
  | succ n ih => simpa only [pow_succ] using ih.mul hf

theorem const_mul [IsFiniteMeasure μ] (hf : AllMoments μ f) (c : ℂ) :
    AllMoments μ (fun ω => c * f ω) := (const c).mul hf

theorem neg [IsFiniteMeasure μ] (hf : AllMoments μ f) :
    AllMoments μ (fun ω => -f ω) := by simpa using hf.const_mul (-1)

theorem sub [IsFiniteMeasure μ] (hf : AllMoments μ f) (hg : AllMoments μ g) :
    AllMoments μ (fun ω => f ω - g ω) := by simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem finset_sum [IsFiniteMeasure μ] {ι : Type*} (s : Finset ι) (F : ι → Ω → ℂ)
    (hF : ∀ i ∈ s, AllMoments μ (F i)) :
    AllMoments μ (fun ω => ∑ i ∈ s, F i ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (const (μ := μ) 0)
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (hF i (by simp)).add (ih (fun j hj => hF j (by simp [hj])))

theorem finset_prod [IsFiniteMeasure μ] {ι : Type*} (s : Finset ι) (F : ι → Ω → ℂ)
    (hF : ∀ i ∈ s, AllMoments μ (F i)) :
    AllMoments μ (fun ω => ∏ i ∈ s, F i ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (const (μ := μ) 1)
  | @insert i s hi ih =>
      simp only [Finset.prod_insert hi]
      exact (hF i (by simp)).mul (ih (fun j hj => hF j (by simp [hj])))

/-- This is uniform in polynomial degree: all moments of a polynomial follow
from all coordinate moments, with no assumption that its integral exists. -/
theorem eval_polynomial [IsFiniteMeasure μ] {ι : Type*}
    (X : ι → Ω → ℂ) (hX : ∀ i, AllMoments μ (X i)) (p : MvPolynomial ι ℂ) :
    AllMoments μ (fun ω => MvPolynomial.eval (fun i => X i ω) p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial e c =>
      simp only [MvPolynomial.eval_monomial]
      exact (finset_prod e.support (fun i ω => X i ω ^ e i)
        (fun i _ => (hX i).pow _)).const_mul c
  | add p q hp hq => simpa only [MvPolynomial.eval_add] using hp.add hq

end AllMoments
end GeneralizedBulk.Analysis
