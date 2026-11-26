import GeneralizedBulk.Graph.ConfigurationProfiles

/-! A concrete defect count and the monotonicity principle used to repair
configuration loops and repeated edges by finitely many local switches. -/
noncomputable section
open scoped BigOperators Classical

namespace GeneralizedBulk.Graph.Configuration

def Parallel {N d : ℕ} (p : Pairing (Stub N d)) (h k : Stub N d) : Prop :=
  h.1 = k.1 ∧ h ≠ k ∧ (p.val h).1 = (p.val k).1

def BadStub {N d : ℕ} (p : Pairing (Stub N d)) (h : Stub N d) : Prop :=
  (p.val h).1 = h.1 ∨ ∃ k, Parallel p h k

def badStubs {N d : ℕ} (p : Pairing (Stub N d)) : Finset (Stub N d) :=
  Finset.univ.filter (BadStub p)

def defect {N d : ℕ} (p : Pairing (Stub N d)) : ℕ := (badStubs p).card

theorem parallel_symm {N d : ℕ} {p : Pairing (Stub N d)} {h k : Stub N d}
    (hP : Parallel p h k) : Parallel p k h := ⟨hP.1.symm,hP.2.1.symm,hP.2.2.symm⟩

theorem parallel_partner {N d : ℕ} {p : Pairing (Stub N d)} {h k : Stub N d}
    (hP : Parallel p h k) : Parallel p (p.val h) (p.val k) := by
  refine ⟨hP.2.2,fun he => hP.2.1 (p.val.injective he),?_⟩
  rw [p.property.1, p.property.1]
  exact hP.1

theorem badStub_partner_iff {N d : ℕ} (p : Pairing (Stub N d)) (h : Stub N d) :
    BadStub p (p.val h) ↔ BadStub p h := by
  have hf : ∀ h, BadStub p h → BadStub p (p.val h) := by
    intro h hb
    rcases hb with hl | ⟨k,hk⟩
    · left; rw [p.property.1]; exact hl.symm
    · exact Or.inr ⟨p.val k,parallel_partner hk⟩
  constructor
  · intro hbad
    have hh := hf (p.val h) hbad
    rw [p.property.1 h] at hh
    exact hh
  · exact hf h

theorem defect_zero_iff {N d : ℕ} (p : Pairing (Stub N d)) :
    defect p = 0 ↔ (∀ h, (p.val h).1 ≠ h.1) ∧
      ∀ v, Function.Injective (fun j : Fin d => (p.val (v,j)).1) := by
  rw [defect, Finset.card_eq_zero, badStubs, Finset.filter_eq_empty_iff]
  simp only [Finset.mem_univ, true_implies]
  constructor
  · intro hb
    constructor
    · intro h hh; exact hb (x := h) (Or.inl hh)
    · intro v i j hij
      by_contra hne
      exact hb (x := (v,i)) (Or.inr ⟨(v,j),rfl,fun he => hne (congrArg Prod.snd he),hij⟩)
  · rintro ⟨hl,hinj⟩ h (hloop | ⟨k,hk⟩)
    · exact hl h hloop
    · rcases h with ⟨v,i⟩
      rcases k with ⟨w,j⟩
      rcases hk with ⟨hvw,hneq,hroot⟩
      dsimp at hvw
      subst w
      exact hneq (Prod.ext rfl (hinj v hroot))

theorem badStubs_subset_of_changed_good {N d : ℕ} (p r : Pairing (Stub N d))
    (T : Finset (Stub N d)) (houtside : ∀ h ∉ T, r.val h = p.val h)
    (hgood : ∀ h ∈ T, ¬ BadStub r h) : badStubs r ⊆ badStubs p := by
  intro h hh
  have hbad := (Finset.mem_filter.mp hh).2
  have hhT : h ∉ T := by intro ht; exact hgood h ht hbad
  have hhval := houtside h hhT
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  rcases hbad with hl | ⟨k,hk⟩
  · left; simpa only [hhval] using hl
  · have hkT : k ∉ T := by
      intro ht
      exact hgood k ht (Or.inr ⟨h,parallel_symm hk⟩)
    right
    refine ⟨k,hk.1,hk.2.1,?_⟩
    simpa only [hhval,houtside k hkT] using hk.2.2

theorem defect_strict_decrease_of_changed_good {N d : ℕ} (p r : Pairing (Stub N d))
    (T : Finset (Stub N d)) (houtside : ∀ h ∉ T, r.val h = p.val h)
    (hgood : ∀ h ∈ T, ¬ BadStub r h) (a : Stub N d) (haT : a ∈ T) (ha : BadStub p a) :
    defect r < defect p := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨badStubs_subset_of_changed_good p r T houtside hgood,?_⟩
  intro he
  have hmem : a ∈ badStubs p := Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩
  rw [← he] at hmem
  exact hgood a haT (Finset.mem_filter.mp hmem).2

end GeneralizedBulk.Graph.Configuration
