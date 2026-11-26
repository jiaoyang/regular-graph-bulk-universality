import GeneralizedBulk.Entropy.SoftQuantizerAgreement
import GeneralizedBulk.Entropy.UnitProducts

/-! Actual hard and C¹ soft finite word laws and their transition error. -/
noncomputable section
open scoped BigOperators Classical

namespace GeneralizedBulk.Entropy

variable {I B : Type*} [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B]
  [MeasurableSpace B] [MeasurableSingletonClass B]

def softWordProbability (J : ℝ → B) (ℓ : ℝ) (z : I → ℝ) (word : I → B) : ℝ :=
  ∏ i,softLabel J ℓ (word i) (z i)

def hardWordProbability (J : ℝ → B) (z : I → ℝ) (word : I → B) : ℝ :=
  ∏ i,hardLabel J (word i) (z i)

theorem product_probability_sum (p : I → B → ℝ) (hsum : ∀ i,∑ b,p i b = 1) :
    (∑ word : I → B,∏ i,p i (word i)) = 1 := by
  have h := Finset.prod_univ_sum (fun _i : I => (Finset.univ : Finset B)) p
  simpa only [hsum,Finset.prod_const_one,Fintype.piFinset_univ] using h.symm

theorem softWordProbability_nonneg (J : ℝ → B) (ℓ : ℝ) (hℓ : 0 < ℓ) (z : I → ℝ) (word : I → B) :
    0 ≤ softWordProbability J ℓ z word := Finset.prod_nonneg (fun i hi => softLabel_nonneg J ℓ hℓ _ _)

theorem softWordProbability_sum (J : ℝ → B) (hJ : Measurable J) (ℓ : ℝ) (hℓ : 0 < ℓ) (z : I → ℝ) :
    (∑ word : I → B,softWordProbability J ℓ z word) = 1 :=
  product_probability_sum _ (fun i => softLabel_sum J hJ ℓ hℓ (z i))

theorem hardWordProbability_eq_dirac (J : ℝ → B) (z : I → ℝ) (word : I → B) :
    hardWordProbability J z word = if word = (fun i => J (z i)) then 1 else 0 := by
  by_cases he : word = (fun i => J (z i))
  · subst word
    simp [hardWordProbability,hardLabel]
  · rw [if_neg he]
    have hi : ∃ i,word i ≠ J (z i) := by
      by_contra hn
      push_neg at hn
      exact he (funext hn)
    obtain ⟨i,hi⟩ := hi
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hardLabel,Ne.symm hi]

theorem dirac_l1_distance (p : (I → B) → ℝ) (hp : ∀ w,0 ≤ p w) (hsum : ∑ w,p w = 1) (w₀ : I → B) :
    (∑ w : I → B,|(if w = w₀ then (1 : ℝ) else 0)-p w|) = 2*(1-p w₀) := by
  have hp1 : p w₀ ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun w hw => hp w) (Finset.mem_univ w₀)
  have hs : p w₀+(∑ w ∈ Finset.univ.erase w₀,p w) = 1 := by
    rw [Finset.add_sum_erase Finset.univ p (Finset.mem_univ w₀),hsum]
  rw [← Finset.add_sum_erase Finset.univ (fun w => |(if w = w₀ then (1 : ℝ) else 0)-p w|) (Finset.mem_univ w₀)]
  simp only [ite_true,abs_of_nonneg (sub_nonneg.mpr hp1)]
  have he : (∑ w ∈ Finset.univ.erase w₀,|(if w = w₀ then (1 : ℝ) else 0)-p w|) =
      ∑ w ∈ Finset.univ.erase w₀,p w := by
    apply Finset.sum_congr rfl
    intro w hw
    rw [if_neg (Finset.mem_erase.mp hw).1,zero_sub,abs_neg,abs_of_nonneg (hp w)]
  rw [he]
  linarith

set_option maxHeartbeats 1000000 in
theorem hard_soft_word_l1_le_transitions (J : ℝ → B) (hJ : Measurable J) (ℓ : ℝ) (hℓ : 0 < ℓ) (z : I → ℝ) :
    (∑ word : I → B,|hardWordProbability J z word-softWordProbability J ℓ z word|) ≤
      2*∑ i : I,(if quantizerTransition J ℓ (z i) then (1 : ℝ) else 0) := by
  simp_rw [hardWordProbability_eq_dirac]
  rw [dirac_l1_distance _ (softWordProbability_nonneg J ℓ hℓ z) (softWordProbability_sum J hJ ℓ hℓ z)]
  let g : I → ℝ := fun i => softLabel J ℓ (J (z i)) (z i)
  have hg0 : ∀ i,0 ≤ g i := fun i => softLabel_nonneg J ℓ hℓ _ _
  have hg1 : ∀ i,g i ≤ 1 := fun i => softLabel_le_one J hJ ℓ hℓ _ _
  have hp : (∏ i,g i) ≤ 1 := Finset.prod_le_one (fun i hi => hg0 i) (fun i hi => hg1 i)
  have h := abs_prod_sub_prod_le_sum (fun _ : I => (1 : ℝ)) g (by intro; norm_num) (by intro; norm_num) hg0 hg1
  simp only [Finset.prod_const_one,abs_of_nonneg (sub_nonneg.mpr hp)] at h
  have hlocal (i : I) : |1-g i| ≤ if quantizerTransition J ℓ (z i) then (1 : ℝ) else 0 := by
    by_cases ht : quantizerTransition J ℓ (z i)
    · rw [if_pos ht,abs_of_nonneg (sub_nonneg.mpr (hg1 i))]
      linarith [hg0 i]
    · rw [if_neg ht]
      dsimp only [g]
      rw [softLabel_eq_hard_of_no_transition J ℓ hℓ _ _ ht]
      simp [hardLabel]
  have hsum : (∑ i,|1-g i|) ≤ ∑ i : I,if quantizerTransition J ℓ (z i) then (1 : ℝ) else 0 :=
    Finset.sum_le_sum (fun i hi => hlocal i)
  change 2*(1-∏ i,g i) ≤ _
  nlinarith [h.trans hsum]

end GeneralizedBulk.Entropy
