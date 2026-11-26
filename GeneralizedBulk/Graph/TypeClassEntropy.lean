import GeneralizedBulk.Entropy.FiniteShannon

/-! The empirical-type counting bound derived directly from normalized
finite product probabilities, without a multinomial counting assumption. -/
noncomputable section
open scoped BigOperators Classical

namespace GeneralizedBulk.Graph
open Entropy.Finite

variable {A : Type*} [Fintype A] [DecidableEq A]

def wordCount {N : ℕ} (w : Fin N → A) (a : A) : ℕ :=
  (Finset.univ.filter (fun v => w v = a)).card

def empiricalWordMass {N : ℕ} (w : Fin N → A) (a : A) : ℝ := wordCount w a / N

def typeClass {N : ℕ} (w : Fin N → A) : Finset (Fin N → A) :=
  Finset.univ.filter (fun z => ∀ a, wordCount z a = wordCount w a)

theorem wordCount_sum {N : ℕ} (w : Fin N → A) : ∑ a, wordCount w a = N := by
  have h := Finset.card_eq_sum_card_fiberwise (f := w)
    (s := (Finset.univ : Finset (Fin N))) (t := (Finset.univ : Finset A))
    (fun v hv => Finset.mem_univ _)
  simpa only [wordCount, Finset.card_univ, Fintype.card_fin] using h.symm

theorem empiricalWordMass_nonneg {N : ℕ} (w : Fin N → A) (a : A) :
    0 ≤ empiricalWordMass w a := by unfold empiricalWordMass; positivity

theorem empiricalWordMass_sum {N : ℕ} (hN : 0 < N) (w : Fin N → A) :
    ∑ a, empiricalWordMass w a = 1 := by
  simp only [empiricalWordMass, ← Finset.sum_div, ← Nat.cast_sum, wordCount_sum]
  exact div_self (by positivity)

theorem empiricalWordMass_at_pos {N : ℕ} (hN : 0 < N) (w : Fin N → A) (v : Fin N) :
    0 < empiricalWordMass w (w v) := by
  apply div_pos _ (by positivity)
  exact_mod_cast Finset.card_pos.mpr ⟨v, by simp⟩

theorem word_probability_fiberwise {N : ℕ} (p : A → ℝ) (w : Fin N → A) :
    ∏ v, p (w v) = ∏ a, p a ^ wordCount w a := by
  rw [← Finset.prod_fiberwise' (Finset.univ : Finset (Fin N)) w p]
  simp only [wordCount, Finset.prod_const]

theorem word_probability_sum {N : ℕ} (p : A → ℝ) (hp : ∑ a, p a = 1) :
    ∑ w : Fin N → A, ∏ v, p (w v) = 1 := by
  have h := Finset.sum_pow' (Finset.univ : Finset A) p N
  simpa only [hp, one_pow, Fintype.piFinset_univ] using h.symm

theorem log_word_probability {N : ℕ} (hN : 0 < N) (w : Fin N → A) :
    Real.log (∏ v, empiricalWordMass w (w v)) = -(N : ℝ) * entropy (empiricalWordMass w) := by
  rw [Real.log_prod _ _ (fun v hv => ne_of_gt (empiricalWordMass_at_pos hN w v))]
  rw [← Finset.sum_fiberwise' (Finset.univ : Finset (Fin N)) w
    (fun a => Real.log (empiricalWordMass w a))]
  simp only [Finset.sum_const, nsmul_eq_mul, wordCount]
  unfold entropy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Real.negMulLog]
  have hn : (N : ℝ) ≠ 0 := by positivity
  dsimp only [empiricalWordMass, wordCount]
  field_simp

set_option maxHeartbeats 1000000 in
theorem log_typeClass_card_le_entropy {N : ℕ} (hN : 0 < N) (w : Fin N → A) :
    Real.log (typeClass w).card ≤ (N : ℝ) * entropy (empiricalWordMass w) := by
  let p := empiricalWordMass w
  let W := ∏ v, p (w v)
  have hW : 0 < W := Finset.prod_pos (fun v hv => empiricalWordMass_at_pos hN w v)
  have hC : 0 < (typeClass w).card := Finset.card_pos.mpr ⟨w, by simp [typeClass]⟩
  have hs : ∑ z ∈ typeClass w, ∏ v, p (z v) = (typeClass w).card * W := by
    calc
      _ = ∑ z ∈ typeClass w, W := by
        apply Finset.sum_congr rfl
        intro z hz
        have hc : ∀ a, wordCount z a = wordCount w a := (Finset.mem_filter.mp hz).2
        dsimp [W]
        rw [word_probability_fiberwise, word_probability_fiberwise]
        simp_rw [hc]
      _ = _ := by simp
  have hb : ((typeClass w).card : ℝ) * W ≤ 1 := by
    rw [← hs, ← word_probability_sum p (empiricalWordMass_sum hN w)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun z hz hnot => Finset.prod_nonneg (fun v hv => empiricalWordMass_nonneg w _))
  have hl := Real.log_le_log (mul_pos (by exact_mod_cast hC) hW) hb
  rw [Real.log_one, Real.log_mul (by positivity) (ne_of_gt hW)] at hl
  have hwlog : Real.log W = -(N : ℝ) * entropy p := log_word_probability hN w
  rw [hwlog] at hl
  linarith

end GeneralizedBulk.Graph
