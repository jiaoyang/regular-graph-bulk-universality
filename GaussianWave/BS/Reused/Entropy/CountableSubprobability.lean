import GaussianWave.BS.Reused.Entropy.CountableMixture
import GaussianWave.BS.Reused.Entropy.IntegerReferenceProduct

/-! Pushforward and reference-energy bounds for actual subprobability masses. -/
noncomputable section
open scoped BigOperators Classical

namespace GaussianWave.BS.Reused.Entropy

variable {A B : Type*}

theorem mass_le_total_of_hasSum (p : A → ℝ) (hp : ∀ a,0 ≤ p a) {δ : ℝ} (hsum : HasSum p δ) (a : A) :
    p a ≤ δ := by
  rw [← hsum.tsum_eq]
  exact hsum.summable.le_tsum a (fun b hb => hp b)

theorem countablePush_hasSum_general (p : A → ℝ) {δ : ℝ} (hsum : HasSum p δ) (f : A → B) :
    HasSum (countablePush p f) δ := hsum.tsum_fiberwise f

theorem countablePush_eq_tsum_indicator (p : A → ℝ) (f : A → B) (b : B) :
    countablePush p f b = ∑' a,if f a = b then p a else 0 := by
  simpa only [Set.indicator,Set.mem_setOf_eq] using tsum_subtype {a : A | f a = b} p

theorem countablePush_congr_support (p : A → ℝ) (f g : A → B)
    (hfg : ∀ a,p a ≠ 0 → f a = g a) : countablePush p f = countablePush p g := by
  funext b
  rw [countablePush_eq_tsum_indicator,countablePush_eq_tsum_indicator]
  apply tsum_congr
  intro a
  by_cases ha : p a = 0
  · simp only [ha,ite_self]
  · rw [hfg a ha]

theorem countablePush_add (p q : A → ℝ) (hp : Summable p) (hq : Summable q) (f : A → B) :
    countablePush (fun a => p a+q a) f = fun b => countablePush p f b+countablePush q f b := by
  funext b
  exact (hp.subtype (fun a => f a = b)).tsum_add (hq.subtype (fun a => f a = b))

theorem summable_entropy_subprob_push (p : A → ℝ) (hp : ∀ a,0 ≤ p a)
    {δ : ℝ} (hsum : HasSum p δ) (hδ1 : δ ≤ 1)
    (hH : Summable (fun a => Real.negMulLog (p a))) (f : A → B) :
    Summable (fun b => Real.negMulLog (countablePush p f b)) := by
  have hps : ∀ a,p a ≤ 1 := fun a => (mass_le_total_of_hasSum p hp hsum a).trans hδ1
  have hpush := countablePush_hasSum_general p hsum f
  have hpnn := countablePush_nonneg p hp f
  have hpoint (b : B) : Real.negMulLog (countablePush p f b) ≤
      ∑' a : {a : A // f a = b},Real.negMulLog (p a.val) :=
    negMulLog_tsum_le_tsum _ (fun a => hp a.val) (fun a => hps a.val)
      (hsum.summable.subtype _) (hH.subtype _)
  apply Summable.of_nonneg_of_le
    (fun b => Real.negMulLog_nonneg (hpnn b) ((mass_le_total_of_hasSum _ hpnn hpush b).trans hδ1))
    hpoint (hH.hasSum.tsum_fiberwise f).summable

theorem subprob_push_entropy_lower_total (p : A → ℝ) (hp : ∀ a,0 ≤ p a)
    {δ : ℝ} (hsum : HasSum p δ) (hδ1 : δ ≤ 1)
    (hH : Summable (fun a => Real.negMulLog (p a))) (f : A → B) :
    Real.negMulLog δ ≤ countableEntropy (countablePush p f) := by
  have hpush := countablePush_hasSum_general p hsum f
  have hpnn := countablePush_nonneg p hp f
  have h := negMulLog_tsum_le_tsum _ hpnn
    (fun b => (mass_le_total_of_hasSum _ hpnn hpush b).trans hδ1) hpush.summable
    (summable_entropy_subprob_push p hp hsum hδ1 hH f)
  rwa [hpush.tsum_eq] at h

set_option maxHeartbeats 1000000 in
theorem subprob_integer_entropy_energy_bound {m : ℕ} (p : (Fin m → ℤ) → ℝ)
    (hp : ∀ j,0 ≤ p j) (δ : ℝ) (hδ : 0 ≤ δ) (hsum : HasSum p δ)
    (hmoment : Summable (fun j => p j*integerEnergy j)) :
    countableEntropy p-Real.negMulLog δ ≤
      δ*linearIntegerEntropyConstant m+(∑' j,p j*integerEnergy j) := by
  by_cases hδ0 : δ = 0
  · have hp0 := vector_eq_zero_of_hasSum_zero p hp (by simpa only [hδ0] using hsum)
    simp [hp0,hδ0,countableEntropy]
  have hδp : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hδ0)
  let P : (Fin m → ℤ) → ℝ := fun j => p j/δ
  have hP : ∀ j,0 ≤ P j := fun j => div_nonneg (hp j) hδ
  have hPsum : HasSum P 1 := by simpa only [P,div_self hδ0] using hsum.div_const δ
  have hPm : Summable (fun j => P j*integerEnergy j) := by
    simpa only [P,div_mul_eq_mul_div] using hmoment.div_const δ
  have hPH := summable_integer_entropy P hP hPsum hPm
  have hbound := integer_entropy_le_linear_first_moment P hP hPsum hPm
  have hscaled := countableEntropy_scale δ P hPsum hPH
  have hep : (fun j => δ*P j) = p := by funext j; dsimp [P]; field_simp
  rw [hep] at hscaled
  have hm : δ*(∑' j,P j*integerEnergy j) = ∑' j,p j*integerEnergy j := by
    simp only [P,div_mul_eq_mul_div,tsum_div_const]
    field_simp
  have hmul := mul_le_mul_of_nonneg_left hbound hδ
  rw [mul_add,hm] at hmul
  linarith

end GaussianWave.BS.Reused.Entropy
