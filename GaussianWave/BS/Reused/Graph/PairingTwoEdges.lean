import GaussianWave.BS.Reused.Graph.PairingRestriction

/-! Exact two-edge probabilities for the actual finite configuration law. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace GaussianWave.BS.Reused.Graph.Configuration

variable {α : Type*} [Fintype α] [DecidableEq α]

def twoEdgeRestrictionEquiv (a b c d : α) (hab : a ≠ b)
    (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b) :
    {p : Pairing α // p.val a = b ∧ p.val c = d} ≃
      {p : Pairing (Remainder a b) // p.val ⟨c,hca,hcb⟩ = ⟨d,hda,hdb⟩} :=
  (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun p : Pairing α => p.val a = b) (fun p => p.val c = d)).symm.trans
    ((prescribedPairEquiv a b hab).subtypeEquiv (fun p => by
      change p.val.val c = d ↔ restrictMate p.val p.property ⟨c,hca,hcb⟩ = ⟨d,hda,hdb⟩
      constructor
      · intro he; exact Subtype.ext he
      · intro he; exact congrArg Subtype.val he))

theorem pairing_card_eq_two_edge_fiber (a b c d : α) (hab : a ≠ b)
    (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b) (hcd : c ≠ d) :
    Fintype.card (Pairing α) = (Fintype.card α - 1) * (Fintype.card α - 3) *
      (Finset.univ.filter (fun p : Pairing α => p.val a = b ∧ p.val c = d)).card := by
  have hcd' : (⟨c,hca,hcb⟩ : Remainder a b) ≠ ⟨d,hda,hdb⟩ := by
    intro he; exact hcd (congrArg Subtype.val he)
  have h2 := pairing_card_eq_partner_fiber (⟨c,hca,hcb⟩ : Remainder a b) ⟨d,hda,hdb⟩ hcd'
  have he := Fintype.card_congr (twoEdgeRestrictionEquiv a b c d hab hca hcb hda hdb)
  simp only [Fintype.card_subtype] at he
  rw [← he] at h2
  rw [pairing_card_recursion a b hab, h2, remainder_card a b hab]
  simp only [Nat.sub_sub, show 2 + 1 = (3 : ℕ) by rfl, mul_assoc]

theorem pairingLaw_two_partner_probability [Nonempty (Pairing α)]
    (a b c d : α) (hab : a ≠ b)
    (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b) (hcd : c ≠ d) :
    (pairingLaw α {p | p.val a = b ∧ p.val c = d}).toReal =
      (((Fintype.card α - 1) * (Fintype.card α - 3) : ℕ) : ℝ)⁻¹ := by
  have hs : ({p : Pairing α | p.val a = b ∧ p.val c = d} : Set (Pairing α)) =
      (Finset.univ.filter (fun p : Pairing α => p.val a = b ∧ p.val c = d) : Set _) := by ext p; simp
  rw [pairingLaw, hs, Graph.finiteUniform_finset_toReal,
    pairing_card_eq_two_edge_fiber a b c d hab hca hcb hda hdb hcd]
  have hF : (Finset.univ.filter (fun p : Pairing α => p.val a = b ∧ p.val c = d)).card ≠ 0 := by
    intro hz
    have hP := Fintype.card_ne_zero (α := Pairing α)
    rw [pairing_card_eq_two_edge_fiber a b c d hab hca hcb hda hdb hcd, hz, mul_zero] at hP
    exact hP rfl
  push_cast
  have hFR : ((Finset.univ.filter (fun p : Pairing α => p.val a = b ∧ p.val c = d)).card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hF
  rw [div_eq_mul_inv, mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ hFR, one_mul]

end GaussianWave.BS.Reused.Graph.Configuration
