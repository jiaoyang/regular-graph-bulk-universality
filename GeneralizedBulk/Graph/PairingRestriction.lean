import GeneralizedBulk.Graph.Pairings

/-! A prescribed matched pair removes exactly two half-edges. -/
noncomputable section
open scoped BigOperators Classical

namespace GeneralizedBulk.Graph.Configuration

abbrev Remainder {α : Type*} (a b : α) := {x : α // x ≠ a ∧ x ≠ b}

theorem partner_reverse {α : Type*} (p : Pairing α) {a b : α} (hab : p.val a = b) : p.val b = a := by
  rw [← hab, p.property.1]

def restrictMate {α : Type*} (p : Pairing α) {a b : α} (hab : p.val a = b)
    (x : Remainder a b) : Remainder a b :=
  ⟨p.val x.val, by
    constructor
    · intro hx
      apply x.property.2
      apply p.val.injective
      exact hx.trans (partner_reverse p hab).symm
    · intro hx
      apply x.property.1
      apply p.val.injective
      exact hx.trans hab.symm⟩

theorem restrictMate_involutive {α : Type*} (p : Pairing α) {a b : α} (hab : p.val a = b) :
    Function.Involutive (restrictMate p hab) := by
  intro x
  apply Subtype.ext
  exact p.property.1 x.val

def restrictPairing {α : Type*} (p : Pairing α) {a b : α} (hab : p.val a = b) : Pairing (Remainder a b) :=
  ⟨Function.Involutive.toPerm (restrictMate p hab) (restrictMate_involutive p hab),
    restrictMate_involutive p hab, by
      intro x hx
      apply p.property.2 x.val
      exact congrArg Subtype.val hx⟩

def extendMate {α : Type*} (a b : α) (q : Pairing (Remainder a b)) (x : α) : α :=
  if hxa : x = a then b else if hxb : x = b then a else (q.val ⟨x, hxa, hxb⟩).val

theorem extendMate_involutive {α : Type*} (a b : α) (hab : a ≠ b)
    (q : Pairing (Remainder a b)) : Function.Involutive (extendMate a b q) := by
  intro x
  by_cases hxa : x = a
  · subst x
    simp [extendMate, hab, hab.symm]
  · by_cases hxb : x = b
    · subst x
      simp [extendMate, hab, hab.symm]
    · have hqa : (q.val ⟨x, hxa, hxb⟩).val ≠ a := (q.val ⟨x, hxa, hxb⟩).property.1
      have hqb : (q.val ⟨x, hxa, hxb⟩).val ≠ b := (q.val ⟨x, hxa, hxb⟩).property.2
      simp only [extendMate, dif_neg hxa, dif_neg hxb, dif_neg hqa, dif_neg hqb]
      exact congrArg Subtype.val (q.property.1 ⟨x, hxa, hxb⟩)

def extendPairing {α : Type*} (a b : α) (hab : a ≠ b) (q : Pairing (Remainder a b)) : Pairing α :=
  ⟨Function.Involutive.toPerm (extendMate a b q) (extendMate_involutive a b hab q),
    extendMate_involutive a b hab q, by
      intro x hx
      change extendMate a b q x = x at hx
      by_cases hxa : x = a
      · subst x
        exact hab (by simpa [extendMate] using hx.symm)
      · by_cases hxb : x = b
        · subst x
          exact hab (by simpa [extendMate, hab.symm] using hx)
        · apply q.property.2 ⟨x, hxa, hxb⟩
          apply Subtype.ext
          simpa only [extendMate, dif_neg hxa, dif_neg hxb] using hx⟩

theorem extendPairing_partner {α : Type*} (a b : α) (hab : a ≠ b) (q : Pairing (Remainder a b)) :
    (extendPairing a b hab q).val a = b := by
  change extendMate a b q a = b
  simp [extendMate]

def prescribedPairEquiv {α : Type*} (a b : α) (hab : a ≠ b) :
    {p : Pairing α // p.val a = b} ≃ Pairing (Remainder a b) where
  toFun p := restrictPairing p.val p.property
  invFun q := ⟨extendPairing a b hab q, extendPairing_partner a b hab q⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Equiv.ext
    intro x
    change extendMate a b (restrictPairing p.val p.property) x = p.val.val x
    by_cases hxa : x = a
    · subst x
      simpa [extendMate] using p.property.symm
    · by_cases hxb : x = b
      · subst x
        simpa [extendMate, hab.symm] using (partner_reverse p.val p.property).symm
      · change extendMate a b (restrictPairing p.val p.property) x = p.val.val x
        simp only [extendMate, dif_neg hxa, dif_neg hxb]
        rfl
  right_inv q := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change extendMate a b q x.val = (q.val x).val
    simp only [extendMate, dif_neg x.property.1, dif_neg x.property.2]

theorem remainder_card {α : Type*} [Fintype α] [DecidableEq α] (a b : α) (hab : a ≠ b) :
    Fintype.card (Remainder a b) = Fintype.card α - 2 := by
  rw [Fintype.card_subtype]
  have he : Finset.univ.filter (fun x : α => x ≠ a ∧ x ≠ b) = (Finset.univ.erase a).erase b := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    tauto
  rw [he, Finset.card_erase_of_mem (by simp [hab.symm]), Finset.card_erase_of_mem (Finset.mem_univ a),
    Finset.card_univ]
  omega

theorem pairing_card_recursion {α : Type*} [Fintype α] [DecidableEq α] (a b : α) (hab : a ≠ b) :
    Fintype.card (Pairing α) = (Fintype.card α - 1) * Fintype.card (Pairing (Remainder a b)) := by
  rw [pairing_card_eq_partner_fiber a b hab]
  have h := Fintype.card_congr (prescribedPairEquiv a b hab)
  rw [Fintype.card_subtype] at h
  rw [h]

def pairingCount : ℕ → ℕ
  | 0 => 1
  | m + 1 => (2 * m + 1) * pairingCount m

theorem pairing_fin_card (m : ℕ) : Fintype.card (Pairing (Fin (2 * m))) = pairingCount m := by
  induction m with
  | zero =>
    letI : Subsingleton (Pairing (Fin 0)) := ⟨fun p q =>
      Subtype.ext (Equiv.ext (fun x => Fin.elim0 x))⟩
    letI : Unique (Pairing (Fin 0)) :=
      ⟨⟨canonicalPairing 0⟩, fun p => Subsingleton.elim _ _⟩
    exact Fintype.card_unique
  | succ m ih =>
    let a : Fin (2 * (m + 1)) := ⟨0, by omega⟩
    let b : Fin (2 * (m + 1)) := ⟨1, by omega⟩
    have hab : a ≠ b := by
      intro h
      have hv := congrArg Fin.val h
      change (0 : ℕ) = 1 at hv
      omega
    have hrem : Fintype.card (Remainder a b) = 2 * m := by
      rw [remainder_card a b hab, Fintype.card_fin]
      omega
    have hcount := Fintype.card_congr (conjugateEquiv (Fintype.equivFinOfCardEq hrem))
    rw [pairing_card_recursion a b hab, hcount, ih, Fintype.card_fin]
    simp only [pairingCount]
    congr 1

end GeneralizedBulk.Graph.Configuration
