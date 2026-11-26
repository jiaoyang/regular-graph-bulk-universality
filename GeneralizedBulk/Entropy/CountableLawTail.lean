import GeneralizedBulk.Entropy.CountableLaw
import GeneralizedBulk.Entropy.TailEnergy

/-! Tail masses and tail moments of a countable fiber law are the actual
probability and integral of the corresponding measurable event. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical

namespace GeneralizedBulk.Entropy

variable {Ω A : Type*} [MeasurableSpace Ω] [Countable A]
  [MeasurableSpace A] [MeasurableSingletonClass A]

theorem measurableSet_countable_event (X : Ω → A) (hX : Measurable X) (s : A → Prop) :
    MeasurableSet {x | s (X x)} := hX (Set.to_countable {a | s a}).measurableSet

theorem tailMass_lawMass (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → A) (hX : Measurable X) (s : A → Prop) :
    tailMass (lawMass μ X) s = μ.real {x | s (X x)} := by
  have hm := measurableSet_countable_event X hX s
  have hi : Integrable (fun x => if s (X x) then (1 : ℝ) else 0) μ := by
    simpa only [Set.indicator_apply] using (integrable_const (1 : ℝ) (μ := μ)).indicator hm
  have h := lawMass_weighted_hasSum μ X hX (fun a => if s a then 1 else 0) hi
  have he : (fun a => lawMass μ X a*(if s a then 1 else 0)) = restrictedMass (lawMass μ X) s := by
    funext a
    by_cases ha : s a <;> simp [restrictedMass,ha]
  rw [he] at h
  calc
    _ = _ := h.tsum_eq
    _ = _ := by simpa only [Set.indicator_apply,Set.mem_setOf_eq,smul_eq_mul,mul_one] using integral_indicator_const (μ := μ) (1 : ℝ) hm

theorem restricted_lawMass_moment (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → A) (hX : Measurable X) (s : A → Prop) (g : A → ℝ)
    (hg : Integrable (fun x => g (X x)) μ) :
    (∑' a,restrictedMass (lawMass μ X) s a*g a) =
      ∫ x,if s (X x) then g (X x) else 0 ∂μ := by
  have hm := measurableSet_countable_event X hX s
  have hi : Integrable (fun x => if s (X x) then g (X x) else 0) μ := by
    simpa only [Set.indicator_apply] using hg.indicator hm
  have h := lawMass_weighted_hasSum μ X hX (fun a => if s a then g a else 0) hi
  have he : (fun a => lawMass μ X a*(if s a then g a else 0)) =
      (fun a => restrictedMass (lawMass μ X) s a*g a) := by
    funext a
    by_cases ha : s a <;> simp [restrictedMass,ha]
  rw [he] at h
  exact h.tsum_eq

theorem restricted_lawMass_moment_le_sqrt (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → A) (hX : Measurable X) (s : A → Prop) (g : A → ℝ)
    (hg : MemLp (fun x => g (X x)) 2 μ) (hgnn : ∀ a,0 ≤ g a) :
    (∑' a,restrictedMass (lawMass μ X) s a*g a) ≤
      Real.sqrt (∫ x,g (X x)^2 ∂μ)*Real.sqrt (μ.real {x | s (X x)}) := by
  rw [restricted_lawMass_moment μ X hX s g (hg.integrable (by norm_num))]
  have h := integral_abs_tail_le_sqrt μ (fun x => g (X x)) hg {x | s (X x)}
    (measurableSet_countable_event X hX s)
  simpa only [Set.mem_setOf_eq,abs_of_nonneg (hgnn _)] using h

end GeneralizedBulk.Entropy
