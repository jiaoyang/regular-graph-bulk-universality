import GaussianWave.BS.Reused.Graph.PairingFactorial

/-! Decomposition of actual color-compatible configurations. A configuration
is encoded injectively by diagonal within-color matchings and one bijection
for each unordered pair of distinct directed color types. -/
noncomputable section
open scoped BigOperators Classical

namespace GaussianWave.BS.Reused.Graph.Configuration

variable {α : Type*} [Fintype α] [DecidableEq α]

def Compatible (f g : α → ℕ) (p : Pairing α) : Prop :=
  ∀ x, f (p.val x) = g x

def ColoredPairing (f g : α → ℕ) := {p : Pairing α // Compatible f g p}

instance (f g : α → ℕ) : Fintype (ColoredPairing f g) := by
  unfold ColoredPairing
  infer_instance

abbrev ColorBlock (f g : α → ℕ) (a b : ℕ) := {x : α // f x = a ∧ g x = b}

instance (f g : α → ℕ) (a b : ℕ) : Fintype (ColorBlock f g a b) := by
  unfold ColorBlock
  infer_instance

instance (f g : α → ℕ) (a b : ℕ) : DecidableEq (ColorBlock f g a b) :=
  inferInstanceAs (DecidableEq {x : α // f x = a ∧ g x = b})

theorem compatible_reverse {f g : α → ℕ} (p : ColoredPairing f g) (x : α) :
    g (p.val.val x) = f x := by
  have h := p.property (p.val.val x)
  rw [p.val.property.1 x] at h
  exact h.symm

def blockEquiv {f g : α → ℕ} (p : ColoredPairing f g) (a b : ℕ) :
    ColorBlock f g a b ≃ ColorBlock f g b a where
  toFun x := ⟨p.val.val x, by
    constructor
    · rw [p.property]; exact x.property.2
    · rw [compatible_reverse p x.val]; exact x.property.1⟩
  invFun x := ⟨p.val.val x, by
    constructor
    · rw [p.property]; exact x.property.2
    · rw [compatible_reverse p x.val]; exact x.property.1⟩
  left_inv x := Subtype.ext (p.val.property.1 x)
  right_inv x := Subtype.ext (p.val.property.1 x)

@[simp] theorem blockEquiv_val {f g : α → ℕ} (p : ColoredPairing f g)
    (a b : ℕ) (x : ColorBlock f g a b) :
    (blockEquiv p a b x).val = p.val.val x := rfl

def diagonalPairing {f g : α → ℕ} (p : ColoredPairing f g) (a : ℕ) :
    Pairing (ColorBlock f g a a) :=
  ⟨blockEquiv p a a, ⟨fun x => Subtype.ext (p.val.property.1 x),
    fun x h => p.val.property.2 x (congrArg Subtype.val h)⟩⟩

def ColorCode (f g : α → ℕ) (q : ℕ) :=
  (∀ a : Fin q, Pairing (ColorBlock f g a a)) ×
    (∀ ab : {ab : Fin q × Fin q // ab.1 < ab.2},
      ColorBlock f g ab.val.1 ab.val.2 ≃ ColorBlock f g ab.val.2 ab.val.1)

instance (f g : α → ℕ) (q : ℕ) : Fintype (ColorCode f g q) := by
  unfold ColorCode
  infer_instance

def colorCode {f g : α → ℕ} (q : ℕ) (p : ColoredPairing f g) : ColorCode f g q :=
  ⟨fun a => diagonalPairing p a, fun ab => blockEquiv p ab.val.1 ab.val.2⟩

set_option maxHeartbeats 1000000 in
theorem colorCode_injective {f g : α → ℕ} (q : ℕ)
    (hf : ∀ x, f x < q) (hg : ∀ x, g x < q) :
    Function.Injective (colorCode (f := f) (g := g) q) := by
  intro p r h
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro x
  let a : Fin q := ⟨f x, hf x⟩
  let b : Fin q := ⟨g x, hg x⟩
  let y : ColorBlock f g a b := ⟨x, rfl, rfl⟩
  rcases lt_trichotomy a b with hab | hab | hba
  · have he := congrArg (fun code : ColorCode f g q => (code.2 ⟨(a, b), hab⟩ y).val) h
    exact he
  · have hb : f x = g x := congrArg Fin.val hab
    let z : ColorBlock f g a a := ⟨x, rfl, hb.symm⟩
    have he := congrArg (fun code : ColorCode f g q => ((code.1 a).val z).val) h
    exact he
  · have he := congrArg (fun code : ColorCode f g q => (code.2 ⟨(b, a), hba⟩).symm y) h
    exact congrArg Subtype.val he

theorem coloredPairing_card_le {f g : α → ℕ} (q : ℕ)
    (hf : ∀ x, f x < q) (hg : ∀ x, g x < q) :
    Fintype.card (ColoredPairing f g) ≤
      (∏ a : Fin q, Fintype.card (Pairing (ColorBlock f g a a))) *
      ∏ ab : {ab : Fin q × Fin q // ab.1 < ab.2},
        Fintype.card (ColorBlock f g ab.val.1 ab.val.2 ≃ ColorBlock f g ab.val.2 ab.val.1) := by
  have h := Fintype.card_le_of_injective _ (colorCode_injective q hf hg)
  simpa only [ColorCode, Fintype.card_prod, Fintype.card_pi] using h

end GaussianWave.BS.Reused.Graph.Configuration
