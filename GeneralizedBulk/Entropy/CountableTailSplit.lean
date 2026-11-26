import GeneralizedBulk.Entropy.CountableSubprobability

/-! A genuine countable entropy clipping loss bound by the global tail.
No conditional independence or coordinate entropy factorization is used. -/
noncomputable section
open scoped BigOperators Classical

namespace GeneralizedBulk.Entropy

variable {A : Type*}

def restrictedMass (p : A → ℝ) (s : A → Prop) (a : A) : ℝ := if s a then p a else 0

def tailMass (p : A → ℝ) (s : A → Prop) : ℝ := ∑' a,restrictedMass p s a

theorem restrictedMass_nonneg (p : A → ℝ) (hp : ∀ a,0 ≤ p a) (s : A → Prop) (a : A) :
    0 ≤ restrictedMass p s a := by unfold restrictedMass; split_ifs <;> simp [hp]

theorem summable_restrictedMass (p : A → ℝ) (hp : ∀ a,0 ≤ p a) (hs : Summable p) (s : A → Prop) :
    Summable (restrictedMass p s) := by
  apply Summable.of_nonneg_of_le (restrictedMass_nonneg p hp s) _ hs
  intro a
  unfold restrictedMass
  split_ifs <;> simp [hp]

theorem tailMass_nonneg (p : A → ℝ) (hp : ∀ a,0 ≤ p a) (s : A → Prop) : 0 ≤ tailMass p s :=
  tsum_nonneg (restrictedMass_nonneg p hp s)

theorem tailMass_le_one (p : A → ℝ) (hp : ∀ a,0 ≤ p a) (hs : HasSum p 1) (s : A → Prop) : tailMass p s ≤ 1 := by
  have h := Summable.tsum_le_tsum (fun a => show restrictedMass p s a ≤ p a by
    unfold restrictedMass; split_ifs <;> simp [hp]) (summable_restrictedMass p hp hs.summable s) hs.summable
  simpa only [hs.tsum_eq,tailMass] using h

theorem summable_restricted_entropy (p : A → ℝ) (hp : ∀ a,0 ≤ p a) (hs : HasSum p 1)
    (hH : Summable (fun a => Real.negMulLog (p a))) (s : A → Prop) :
    Summable (fun a => Real.negMulLog (restrictedMass p s a)) := by
  apply Summable.of_nonneg_of_le _ _ hH
  · intro a
    by_cases ha : s a
    · simpa only [restrictedMass,if_pos ha] using
        Real.negMulLog_nonneg (hp a) (mass_le_one_of_hasSum p hp hs a)
    · simp only [restrictedMass,if_neg ha,Real.negMulLog_zero,le_refl]
  · intro a
    unfold restrictedMass
    split_ifs
    · rfl
    · simpa only [Real.negMulLog_zero] using Real.negMulLog_nonneg (hp a) (mass_le_one_of_hasSum p hp hs a)

theorem restrictedMass_add_compl (p : A → ℝ) (s : A → Prop) :
    (fun a => restrictedMass p (fun a => ¬ s a) a+restrictedMass p s a) = p := by
  funext a
  by_cases ha : s a <;> simp only [restrictedMass,ha,not_true_eq_false,not_false_eq_true,if_false,if_true,zero_add,add_zero]

theorem restrictedMass_compl_hasSum (p : A → ℝ) (hp : ∀ a,0 ≤ p a) (hs : HasSum p 1) (s : A → Prop) :
    HasSum (restrictedMass p (fun a => ¬ s a)) (1-tailMass p s) := by
  have hg := summable_restrictedMass p hp hs.summable (fun a => ¬ s a)
  have hb := summable_restrictedMass p hp hs.summable s
  have hmass : (∑' a,restrictedMass p (fun a => ¬ s a) a)+tailMass p s = 1 := by
    rw [tailMass,← hg.tsum_add hb,restrictedMass_add_compl,hs.tsum_eq]
  convert hg.hasSum using 1
  linarith

theorem countableEntropy_split (p : A → ℝ) (hp : ∀ a,0 ≤ p a) (hs : HasSum p 1)
    (hH : Summable (fun a => Real.negMulLog (p a))) (s : A → Prop) :
    countableEntropy p = countableEntropy (restrictedMass p (fun a => ¬ s a))+countableEntropy (restrictedMass p s) := by
  unfold countableEntropy
  rw [← (summable_restricted_entropy p hp hs hH (fun a => ¬ s a)).tsum_add
    (summable_restricted_entropy p hp hs hH s)]
  apply tsum_congr
  intro a
  by_cases ha : s a <;> simp [restrictedMass,ha]

set_option maxHeartbeats 1000000 in
theorem countable_clipping_loss_le_tail (p : A → ℝ) (hp : ∀ a,0 ≤ p a) (hs : HasSum p 1)
    (hH : Summable (fun a => Real.negMulLog (p a))) (bad : A → Prop) (T : A → A)
    (hT : ∀ a,¬ bad a → T a = a) :
    countableEntropy p-countableEntropy (countablePush p T) ≤
      Real.binEntropy (tailMass p bad)+countableEntropy (restrictedMass p bad)-Real.negMulLog (tailMass p bad) := by
  let good := restrictedMass p (fun a => ¬ bad a)
  let tail := restrictedMass p bad
  have hgnn : ∀ a,0 ≤ good a := restrictedMass_nonneg p hp _
  have htnn : ∀ a,0 ≤ tail a := restrictedMass_nonneg p hp _
  have hgs := summable_restrictedMass p hp hs.summable (fun a => ¬ bad a)
  have hts := summable_restrictedMass p hp hs.summable bad
  have hgH := summable_restricted_entropy p hp hs hH (fun a => ¬ bad a)
  have htH := summable_restricted_entropy p hp hs hH bad
  have hgoodMass : HasSum good (1-tailMass p bad) := restrictedMass_compl_hasSum p hp hs bad
  have htailMass : HasSum tail (tailMass p bad) := hts.hasSum
  have hδ := tailMass_nonneg p hp bad
  have hδ1 := tailMass_le_one p hp hs bad
  have hpushGood : countablePush good T = good := by
    calc
      _ = countablePush good id := countablePush_congr_support good T id (by
        intro a ha
        apply hT
        intro hb
        apply ha
        simp [good,restrictedMass,hb])
      _ = _ := countablePush_id good
  have hsplit : (fun a => good a+tail a) = p := restrictedMass_add_compl p bad
  have hpush : (fun a => good a+countablePush tail T a) = countablePush p T := by
    rw [← hpushGood,← countablePush_add good tail hgs hts T,hsplit]
  have hlower := countableEntropy_add_lower_mass good (countablePush tail T) hgnn
    (countablePush_nonneg tail htnn T) (1-tailMass p bad) (tailMass p bad) (by linarith) hδ (by ring)
    hgoodMass (countablePush_hasSum_general tail htailMass T) hgH
    (summable_entropy_subprob_push tail htnn htailMass hδ1 htH T)
  rw [hpush] at hlower
  have htailLower := subprob_push_entropy_lower_total tail htnn htailMass hδ1 htH T
  have hEntropySplit := countableEntropy_split p hp hs hH bad
  change countableEntropy p = countableEntropy good+countableEntropy tail at hEntropySplit
  linarith

end GeneralizedBulk.Entropy
