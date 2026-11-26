import GaussianWave.BS.Reused.Entropy.CountablePushforward

/-! Exact scaling and mixture inequalities for summable countable entropy. -/
noncomputable section
open scoped BigOperators Classical

namespace GaussianWave.BS.Reused.Entropy

variable {A : Type*}

theorem summable_entropy_scale (c : ℝ) (p : A → ℝ) (hp : Summable p)
    (hH : Summable (fun a => Real.negMulLog (p a))) :
    Summable (fun a => Real.negMulLog (c*p a)) := by
  simp_rw [Real.negMulLog_mul]
  exact (hp.mul_right (Real.negMulLog c)).add (hH.mul_left c)

theorem countableEntropy_scale (c : ℝ) (p : A → ℝ) (hsum : HasSum p 1)
    (hH : Summable (fun a => Real.negMulLog (p a))) :
    countableEntropy (fun a => c*p a) = c*countableEntropy p+Real.negMulLog c := by
  unfold countableEntropy
  simp_rw [Real.negMulLog_mul]
  rw [(hsum.summable.mul_right (Real.negMulLog c)).tsum_add (hH.mul_left c),
    tsum_mul_right,tsum_mul_left,hsum.tsum_eq,one_mul]
  ring

theorem countable_mixture_hasSum (p q : A → ℝ) (hp : HasSum p 1) (hq : HasSum q 1)
    (a b : ℝ) (hab : a+b = 1) : HasSum (fun x => a*p x+b*q x) 1 := by
  have h := (hp.mul_left a).add (hq.mul_left b)
  simpa only [mul_one,hab] using h

theorem summable_entropy_mixture (p q : A → ℝ)
    (hp : ∀ x,0 ≤ p x) (hq : ∀ x,0 ≤ q x) (hpsum : HasSum p 1) (hqsum : HasSum q 1)
    (hHp : Summable (fun x => Real.negMulLog (p x))) (hHq : Summable (fun x => Real.negMulLog (q x)))
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b = 1) :
    Summable (fun x => Real.negMulLog (a*p x+b*q x)) := by
  have hnonneg : ∀ x,0 ≤ a*p x+b*q x := fun x => add_nonneg (mul_nonneg ha (hp x)) (mul_nonneg hb (hq x))
  have hsum := countable_mixture_hasSum p q hpsum hqsum a b hab
  apply Summable.of_nonneg_of_le
    (fun x => Real.negMulLog_nonneg (hnonneg x) (mass_le_one_of_hasSum _ hnonneg hsum x))
    (fun x => Finite.negMulLog_add_le (mul_nonneg ha (hp x)) (mul_nonneg hb (hq x)))
    ((summable_entropy_scale a p hpsum.summable hHp).add (summable_entropy_scale b q hqsum.summable hHq))

set_option maxHeartbeats 1000000 in
theorem countableEntropy_mixture_lower (p q : A → ℝ)
    (hp : ∀ x,0 ≤ p x) (hq : ∀ x,0 ≤ q x) (hpsum : HasSum p 1) (hqsum : HasSum q 1)
    (hHp : Summable (fun x => Real.negMulLog (p x))) (hHq : Summable (fun x => Real.negMulLog (q x)))
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b = 1) :
    a*countableEntropy p+b*countableEntropy q ≤ countableEntropy (fun x => a*p x+b*q x) := by
  have hpoint (x : A) : a*Real.negMulLog (p x)+b*Real.negMulLog (q x) ≤ Real.negMulLog (a*p x+b*q x) :=
    Real.concaveOn_negMulLog.2 (hp x) (hq x) ha hb hab
  have h := Summable.tsum_le_tsum hpoint ((hHp.mul_left a).add (hHq.mul_left b))
    (summable_entropy_mixture p q hp hq hpsum hqsum hHp hHq a b ha hb hab)
  rw [(hHp.mul_left a).tsum_add (hHq.mul_left b),tsum_mul_left,tsum_mul_left] at h
  exact h

set_option maxHeartbeats 1000000 in
theorem countableEntropy_mixture_upper (p q : A → ℝ)
    (hp : ∀ x,0 ≤ p x) (hq : ∀ x,0 ≤ q x) (hpsum : HasSum p 1) (hqsum : HasSum q 1)
    (hHp : Summable (fun x => Real.negMulLog (p x))) (hHq : Summable (fun x => Real.negMulLog (q x)))
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b = 1) :
    countableEntropy (fun x => a*p x+b*q x) ≤
      a*countableEntropy p+b*countableEntropy q+Real.negMulLog a+Real.negMulLog b := by
  have h := Summable.tsum_le_tsum
    (fun x => Finite.negMulLog_add_le (mul_nonneg ha (hp x)) (mul_nonneg hb (hq x)))
    (summable_entropy_mixture p q hp hq hpsum hqsum hHp hHq a b ha hb hab)
    ((summable_entropy_scale a p hpsum.summable hHp).add (summable_entropy_scale b q hqsum.summable hHq))
  rw [(summable_entropy_scale a p hpsum.summable hHp).tsum_add
    (summable_entropy_scale b q hqsum.summable hHq)] at h
  change countableEntropy (fun x => a*p x+b*q x) ≤
    countableEntropy (fun x => a*p x)+countableEntropy (fun x => b*q x) at h
  rw [countableEntropy_scale a p hpsum hHp,countableEntropy_scale b q hqsum hHq] at h
  linarith

theorem vector_eq_zero_of_hasSum_zero (p : A → ℝ) (hp : ∀ x,0 ≤ p x) (hs : HasSum p 0) : p = 0 := by
  funext x
  have h := hs.summable.le_tsum x (fun y hy => hp y)
  rw [hs.tsum_eq] at h
  exact le_antisymm h (hp x)

set_option maxHeartbeats 1000000 in
theorem countableEntropy_add_lower_mass (p q : A → ℝ)
    (hp : ∀ x,0 ≤ p x) (hq : ∀ x,0 ≤ q x)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b = 1)
    (hpsum : HasSum p a) (hqsum : HasSum q b)
    (hHp : Summable (fun x => Real.negMulLog (p x))) (hHq : Summable (fun x => Real.negMulLog (q x))) :
    countableEntropy p+countableEntropy q-Real.binEntropy b ≤ countableEntropy (fun x => p x+q x) := by
  by_cases ha0 : a = 0
  · have hp0 := vector_eq_zero_of_hasSum_zero p hp (by simpa only [ha0] using hpsum)
    have hb1 : b = 1 := by linarith
    simp [hp0,hb1,countableEntropy]
  by_cases hb0 : b = 0
  · have hq0 := vector_eq_zero_of_hasSum_zero q hq (by simpa only [hb0] using hqsum)
    simp [hq0,hb0,countableEntropy]
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  let P : A → ℝ := fun x => p x/a
  let Q : A → ℝ := fun x => q x/b
  have hP : ∀ x,0 ≤ P x := fun x => div_nonneg (hp x) ha
  have hQ : ∀ x,0 ≤ Q x := fun x => div_nonneg (hq x) hb
  have hPsum : HasSum P 1 := by simpa only [P,div_self ha0] using hpsum.div_const a
  have hQsum : HasSum Q 1 := by simpa only [Q,div_self hb0] using hqsum.div_const b
  have hHP : Summable (fun x => Real.negMulLog (P x)) := by
    simpa only [P,div_eq_mul_inv,mul_comm] using summable_entropy_scale a⁻¹ p hpsum.summable hHp
  have hHQ : Summable (fun x => Real.negMulLog (Q x)) := by
    simpa only [Q,div_eq_mul_inv,mul_comm] using summable_entropy_scale b⁻¹ q hqsum.summable hHq
  have hep : (fun x => a*P x) = p := by funext x; dsimp [P]; field_simp
  have heq : (fun x => b*Q x) = q := by funext x; dsimp [Q]; field_simp
  have hsP := countableEntropy_scale a P hPsum hHP
  have hsQ := countableEntropy_scale b Q hQsum hHQ
  rw [hep] at hsP
  rw [heq] at hsQ
  have hl := countableEntropy_mixture_lower P Q hP hQ hPsum hQsum hHP hHQ a b ha hb hab
  have hef : (fun x => a*P x+b*Q x) = (fun x => p x+q x) := by simp only [← hep,← heq]
  rw [hef] at hl
  have haeq : a = 1-b := by linarith
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,← haeq]
  linarith

end GaussianWave.BS.Reused.Entropy
