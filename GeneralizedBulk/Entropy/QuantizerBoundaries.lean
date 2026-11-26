import GeneralizedBulk.Entropy.SoftQuantizerAgreement
import GeneralizedBulk.Entropy.GaussianTransition

/-! A finite boundary description turns double-box transition occurrences
into an explicit finite union of intervals of total length at most 4ℓ·#F. -/
noncomputable section
open scoped BigOperators Classical

namespace GeneralizedBulk.Entropy

variable {B : Type*} [Fintype B] [DecidableEq B] [MeasurableSpace B] [MeasurableSingletonClass B]

def HasQuantizerBoundaries (J : ℝ → B) (F : Finset ℝ) : Prop :=
  ∀ x y,J x ≠ J y → ∃ b ∈ F,min x y ≤ b ∧ b ≤ max x y

theorem quantizerTransition_subset_intervals (J : ℝ → B) (F : Finset ℝ)
    (hF : HasQuantizerBoundaries J F) (ℓ : ℝ) :
    {x | quantizerTransition J ℓ x} ⊆ transitionIntervals F ℓ := by
  rintro x ⟨z,hz,hneq⟩
  obtain ⟨b,hb,hlo,hhi⟩ := hF x z hneq.symm
  apply Set.mem_iUnion.mpr
  refine ⟨b,Set.mem_iUnion.mpr ⟨hb,?_⟩⟩
  rcases le_total x z with hxz | hzx
  · simp only [min_eq_left hxz,max_eq_right hxz] at hlo hhi
    constructor <;> linarith [hz.1,hz.2]
  · simp only [min_eq_right hzx,max_eq_left hzx] at hlo hhi
    constructor <;> linarith [hz.1,hz.2]

theorem transition_indicator_le_boundary_indicator (J : ℝ → B) (F : Finset ℝ)
    (hF : HasQuantizerBoundaries J F) (ℓ x : ℝ) :
    (if quantizerTransition J ℓ x then (1 : ℝ) else 0) ≤
      if x ∈ transitionIntervals F ℓ then (1 : ℝ) else 0 := by
  by_cases ht : quantizerTransition J ℓ x
  · rw [if_pos ht,if_pos (quantizerTransition_subset_intervals J F hF ℓ ht)]
  · rw [if_neg ht]
    split_ifs <;> norm_num

end GeneralizedBulk.Entropy
