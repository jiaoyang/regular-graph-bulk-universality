import GeneralizedBulk.Graph.UniformSwitching

/-! Actual finite half-edge pairings and their uniform relabeling symmetry. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace GeneralizedBulk.Graph.Configuration

def Pairing (α : Type*) :=
  {σ : Equiv.Perm α // Function.Involutive σ ∧ ∀ a, σ a ≠ a}

instance (α : Type*) [Fintype α] : Fintype (Pairing α) := by unfold Pairing; infer_instance
instance (α : Type*) : MeasurableSpace (Pairing α) := ⊤
instance (α : Type*) : MeasurableSingletonClass (Pairing α) := ⟨fun _ => trivial⟩

def conjugate {α β : Type*} (e : α ≃ β) (p : Pairing α) : Pairing β :=
  ⟨e.symm.trans (p.val.trans e), by
    constructor
    · intro b
      change e (p.val (e.symm (e (p.val (e.symm b))))) = b
      rw [e.symm_apply_apply, p.property.1]
      exact e.apply_symm_apply b
    · intro b hb
      apply p.property.2 (e.symm b)
      have h := congrArg e.symm hb
      simpa only [Equiv.trans_apply, e.symm_apply_apply] using h⟩

theorem conjugate_apply {α β : Type*} (e : α ≃ β) (p : Pairing α) (b : β) :
    (conjugate e p).val b = e (p.val (e.symm b)) := rfl

def conjugateEquiv {α β : Type*} (e : α ≃ β) : Pairing α ≃ Pairing β where
  toFun := conjugate e
  invFun := conjugate e.symm
  left_inv p := by
    apply Subtype.ext
    apply Equiv.ext
    intro a
    simp only [conjugate_apply, Equiv.symm_symm, e.apply_symm_apply, e.symm_apply_apply]
  right_inv p := by
    apply Subtype.ext
    apply Equiv.ext
    intro b
    simp only [conjugate_apply, Equiv.symm_symm, e.apply_symm_apply, e.symm_apply_apply]

def canonicalPairing (m : ℕ) : Pairing (Fin (2 * m)) :=
  ⟨Fin.revPerm, Fin.rev_involutive, by
    intro i hi
    have hv := congrArg Fin.val hi
    change 2 * m - (i.val + 1) = i.val at hv
    have hi' := i.isLt
    omega⟩

instance (m : ℕ) : Nonempty (Pairing (Fin (2 * m))) := ⟨canonicalPairing m⟩

def pairingLaw (α : Type*) [Fintype α] : Measure (Pairing α) := Graph.finiteUniform _

theorem pairingLaw_isProbability (α : Type*) [Fintype α] [Nonempty (Pairing α)] :
    IsProbabilityMeasure (pairingLaw α) := Graph.finiteUniform_isProbability _

theorem pairingLaw_relabel_invariant {α : Type*} [Fintype α] (e : Equiv.Perm α) :
    Measure.map (conjugate e) (pairingLaw α) = pairingLaw α :=
  Graph.finiteUniform_equiv_invariant (conjugateEquiv e)

theorem partner_fiber_card_eq {α : Type*} [Fintype α] [DecidableEq α]
    (a b c : α) (hab : a ≠ b) (hac : a ≠ c) :
    (Finset.univ.filter (fun p : Pairing α => p.val a = b)).card =
      (Finset.univ.filter (fun p : Pairing α => p.val a = c)).card := by
  let e := Equiv.swap b c
  have hfix : e.symm a = a := by
    simp only [e, Equiv.symm_swap]
    exact Equiv.swap_apply_of_ne_of_ne hab hac
  apply Finset.card_equiv (conjugateEquiv e)
  intro p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change p.val a = b ↔ e (p.val (e.symm a)) = c
  rw [hfix]
  constructor
  · intro hp
    rw [hp]
    exact Equiv.swap_apply_left _ _
  · intro hp
    apply e.injective
    rw [hp]
    exact (Equiv.swap_apply_left _ _).symm

theorem pairing_card_eq_partner_fiber {α : Type*} [Fintype α] [DecidableEq α]
    (a b : α) (hab : a ≠ b) :
    Fintype.card (Pairing α) = (Fintype.card α - 1) *
      (Finset.univ.filter (fun p : Pairing α => p.val a = b)).card := by
  have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Pairing α)))
    (t := Finset.univ.erase a) (f := fun p : Pairing α => p.val a) (fun p hp => by
      simp only [Finset.mem_coe, Finset.mem_erase, Finset.mem_univ, and_true]
      exact p.property.2 a)
  have hf (c : α) (hc : c ∈ Finset.univ.erase a) :
      (Finset.univ.filter (fun p : Pairing α => p.val a = c)).card =
        (Finset.univ.filter (fun p : Pairing α => p.val a = b)).card :=
    partner_fiber_card_eq a c b (Ne.symm (Finset.mem_erase.mp hc).1) hab
  rw [Finset.card_univ] at h
  rw [h, Finset.sum_congr rfl hf]
  simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ,
    nsmul_eq_mul, Nat.cast_id]

/-- Under the actual uniform pairing law, the partner of a fixed half-edge
is exactly uniform over all other half-edges. -/
theorem pairingLaw_partner_probability {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty (Pairing α)] (a b : α) (hab : a ≠ b) :
    (pairingLaw α {p | p.val a = b}).toReal = ((Fintype.card α - 1 : ℕ) : ℝ)⁻¹ := by
  have hs : ({p : Pairing α | p.val a = b} : Set (Pairing α)) =
      (Finset.univ.filter (fun p : Pairing α => p.val a = b) : Set _) := by ext p; simp
  rw [pairingLaw, hs, Graph.finiteUniform_finset_toReal, pairing_card_eq_partner_fiber a b hab, Nat.cast_mul]
  have hP : Fintype.card (Pairing α) ≠ 0 := Fintype.card_ne_zero
  have hF : (Finset.univ.filter (fun p : Pairing α => p.val a = b)).card ≠ 0 := by
    intro hz
    rw [pairing_card_eq_partner_fiber a b hab, hz, mul_zero] at hP
    exact hP rfl
  have hFR : ((Finset.univ.filter (fun p : Pairing α => p.val a = b)).card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hF
  rw [div_eq_mul_inv, mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ hFR, one_mul]

end GeneralizedBulk.Graph.Configuration
