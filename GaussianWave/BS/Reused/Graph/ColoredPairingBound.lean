import GaussianWave.BS.Reused.Graph.ColoredPairings
import GaussianWave.BS.Reused.Graph.PairingBounds

/-! A square-factorial upper bound for color-compatible configurations.
This keeps the correct half-edge entropy coefficient without requiring that
all directed type cells have positive size. -/
noncomputable section
open scoped BigOperators Classical

namespace GaussianWave.BS.Reused.Graph.Configuration

abbrev UpperColorPair (q : ℕ) := {ab : Fin q × Fin q // ab.1 < ab.2}

abbrev ColorPairIndex (q : ℕ) := Fin q ⊕ (UpperColorPair q ⊕ UpperColorPair q)

def decodeColorPair {q : ℕ} : ColorPairIndex q → Fin q × Fin q
  | Sum.inl a => (a, a)
  | Sum.inr (Sum.inl ab) => ab.val
  | Sum.inr (Sum.inr ab) => (ab.val.2, ab.val.1)

theorem decodeColorPair_injective (q : ℕ) : Function.Injective (@decodeColorPair q) := by
  intro x y h
  cases x with
  | inl a =>
    cases y with
    | inl b => exact congrArg Sum.inl (congrArg Prod.fst h)
    | inr y =>
      cases y with
      | inl bc => have h0 := congrArg Prod.fst h; have h1 := congrArg Prod.snd h; dsimp [decodeColorPair] at h0 h1; exact False.elim (by have := bc.property; omega)
      | inr bc => have h0 := congrArg Prod.fst h; have h1 := congrArg Prod.snd h; dsimp [decodeColorPair] at h0 h1; exact False.elim (by have := bc.property; omega)
  | inr x =>
    cases x with
    | inl ab =>
      cases y with
      | inl c => have h0 := congrArg Prod.fst h; have h1 := congrArg Prod.snd h; dsimp [decodeColorPair] at h0 h1; exact False.elim (by have := ab.property; omega)
      | inr y =>
        cases y with
        | inl cd => exact congrArg (Sum.inr ∘ Sum.inl) (Subtype.ext h)
        | inr cd => have h0 := congrArg Prod.fst h; have h1 := congrArg Prod.snd h; dsimp [decodeColorPair] at h0 h1; exact False.elim (by have := ab.property; have := cd.property; omega)
    | inr ab =>
      cases y with
      | inl c => have h0 := congrArg Prod.fst h; have h1 := congrArg Prod.snd h; dsimp [decodeColorPair] at h0 h1; exact False.elim (by have := ab.property; omega)
      | inr y =>
        cases y with
        | inl cd => have h0 := congrArg Prod.fst h; have h1 := congrArg Prod.snd h; dsimp [decodeColorPair] at h0 h1; exact False.elim (by have := ab.property; have := cd.property; omega)
        | inr cd =>
          apply congrArg (Sum.inr ∘ Sum.inr)
          apply Subtype.ext
          exact (Prod.swap_injective h)

theorem decodeColorPair_surjective (q : ℕ) : Function.Surjective (@decodeColorPair q) := by
  rintro ⟨a, b⟩
  rcases lt_trichotomy a b with h | h | h
  · exact ⟨Sum.inr (Sum.inl ⟨(a,b),h⟩), rfl⟩
  · subst b; exact ⟨Sum.inl a, rfl⟩
  · exact ⟨Sum.inr (Sum.inr ⟨(b,a),h⟩), rfl⟩

def colorPairEquiv (q : ℕ) : ColorPairIndex q ≃ (Fin q × Fin q) :=
  Equiv.ofBijective decodeColorPair ⟨decodeColorPair_injective q, decodeColorPair_surjective q⟩

theorem colorPair_product {q : ℕ} (m : Fin q → Fin q → ℕ) :
    (∏ a, m a a) * (∏ ab : UpperColorPair q, m ab.val.1 ab.val.2 * m ab.val.2 ab.val.1) =
      ∏ a, ∏ b, m a b := by
  have h := Equiv.prod_comp (colorPairEquiv q) (fun ab : Fin q × Fin q => m ab.1 ab.2)
  simpa only [colorPairEquiv, Equiv.ofBijective_apply, Fintype.prod_sum_type,
    decodeColorPair, Finset.prod_mul_distrib, Fintype.prod_prod_type, mul_assoc] using h

set_option maxHeartbeats 2000000 in
theorem coloredPairing_card_sq_le {α : Type*} [Fintype α] [DecidableEq α]
    {f g : α → ℕ} (q : ℕ) (hf : ∀ x, f x < q) (hg : ∀ x, g x < q) :
    Fintype.card (ColoredPairing f g) ^ 2 ≤
      ∏ a : Fin q, ∏ b : Fin q, (Fintype.card (ColorBlock f g a b)).factorial := by
  let D := ∏ a : Fin q, Fintype.card (Pairing (ColorBlock f g a a))
  let B := ∏ ab : UpperColorPair q,
    Fintype.card (ColorBlock f g ab.val.1 ab.val.2 ≃ ColorBlock f g ab.val.2 ab.val.1)
  have hc : Fintype.card (ColoredPairing f g) ≤ D * B := coloredPairing_card_le q hf hg
  have hD : D ^ 2 ≤ ∏ a : Fin q, (Fintype.card (ColorBlock f g a a)).factorial := by
    dsimp [D]
    rw [← Finset.prod_pow]
    exact Finset.prod_le_prod' (fun a ha => pairing_card_sq_le_factorial _)
  have hB : B ^ 2 ≤ ∏ ab : UpperColorPair q,
      (Fintype.card (ColorBlock f g ab.val.1 ab.val.2)).factorial *
        (Fintype.card (ColorBlock f g ab.val.2 ab.val.1)).factorial := by
    dsimp [B]
    rw [← Finset.prod_pow]
    apply Finset.prod_le_prod'
    intro ab hab
    rw [pow_two]
    exact Nat.mul_le_mul
      (equiv_card_le_factorial (ColorBlock f g ab.val.1 ab.val.2)
        (ColorBlock f g ab.val.2 ab.val.1))
      (equiv_card_le_factorial_right (ColorBlock f g ab.val.1 ab.val.2)
        (ColorBlock f g ab.val.2 ab.val.1))

  calc
    _ ≤ (D * B) ^ 2 := Nat.pow_le_pow_left hc 2
    _ = D ^ 2 * B ^ 2 := mul_pow _ _ _
    _ ≤ _ := Nat.mul_le_mul hD hB
    _ = _ := colorPair_product (fun a b => (Fintype.card (ColorBlock f g a b)).factorial)

end GaussianWave.BS.Reused.Graph.Configuration
