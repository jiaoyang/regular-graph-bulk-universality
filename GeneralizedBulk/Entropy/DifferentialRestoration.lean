import GeneralizedBulk.Entropy.DifferentialMixtureBounds

/-! Restoring an arbitrary bad component of a density changes differential
entropy by its actual mixture mass times the two absolute entropies, plus
the binary mixing entropy. -/
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace GeneralizedBulk.Entropy

set_option maxHeartbeats 1500000 in
theorem differentialEntropy_restoration {I : Type*} [Fintype I]
    (full good bad : (I → ℝ) → ℝ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hsplit : ∀ x,full x = (1-p)*good x+p*bad x)
    (hgp : ∀ x,0 ≤ good x) (hbp : ∀ x,0 ≤ bad x)
    (hgi : Integrable good) (hbi : Integrable bad) (hgnorm : ∫ x,good x = 1) (hbnorm : ∫ x,bad x = 1)
    (hglog : Integrable (fun x => good x*Real.log (good x)))
    (hblog : Integrable (fun x => bad x*Real.log (bad x)))
    (hflog : Integrable (fun x => full x*Real.log (full x))) :
    |differentialEntropy full-differentialEntropy good| ≤
      p*(|differentialEntropy bad|+|differentialEntropy good|)+Real.binEntropy p := by
  let w : Fin 2 → ℝ := ![1-p,p]
  let f : Fin 2 → (I → ℝ) → ℝ := ![good,bad]
  have hw (i : Fin 2) : 0 ≤ w i := by fin_cases i <;> simp [w,hp,sub_nonneg.mpr hp1]
  have hsum : (∑ i,w i) = 1 := by simp [w,Fin.sum_univ_two]
  have hfp (i : Fin 2) (x) : 0 ≤ f i x := by fin_cases i; exact hgp x; exact hbp x
  have hfi (i : Fin 2) : Integrable (f i) := by fin_cases i; exact hgi; exact hbi
  have hfn (i : Fin 2) : (∫ x,f i x) = 1 := by fin_cases i; exact hgnorm; exact hbnorm
  have hfl (i : Fin 2) : Integrable (fun x => f i x*Real.log (f i x)) := by fin_cases i; exact hglog; exact hblog
  have he : (fun x => ∑ i,w i*f i x) = full := by
    funext x
    simp only [Fin.sum_univ_two,w,f,Matrix.cons_val_zero,Matrix.cons_val_one]
    exact (hsplit x).symm
  have hm : Integrable (fun x => (∑ i,w i*f i x)*Real.log (∑ i,w i*f i x)) := by
    simpa only [show (fun x => (∑ i,w i*f i x)*Real.log (∑ i,w i*f i x)) =
      (fun x => full x*Real.log (full x)) from by funext x; rw [congrFun he x]] using hflog
  have h := differentialEntropy_finite_mixture_bounds w f hw hsum hfp hfi hfn hfl hm
  rw [he] at h
  have hmix : (∑ i,w i*differentialEntropy (f i)) =
      (1-p)*differentialEntropy good+p*differentialEntropy bad := by
    simp only [Fin.sum_univ_two,w,f,Matrix.cons_val_zero,Matrix.cons_val_one]
  have hwH : Finite.entropy w = Real.binEntropy p := by
    simp only [Finite.entropy,Fin.sum_univ_two,w,Matrix.cons_val_zero,Matrix.cons_val_one,
      Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    ring
  rw [hmix,hwH] at h
  have hbin := Real.binEntropy_nonneg hp hp1
  have hbad0 := mul_le_mul_of_nonneg_left (neg_le_abs (differentialEntropy bad)) hp
  have hbad1 := mul_le_mul_of_nonneg_left (le_abs_self (differentialEntropy bad)) hp
  have hgood0 := mul_le_mul_of_nonneg_left (neg_le_abs (differentialEntropy good)) hp
  have hgood1 := mul_le_mul_of_nonneg_left (le_abs_self (differentialEntropy good)) hp
  exact abs_le.mpr ⟨by nlinarith [h.1],by nlinarith [h.2]⟩

end GeneralizedBulk.Entropy
