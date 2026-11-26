import GeneralizedBulk.Graph.ConfigurationDefects

/-! A concrete two-edge configuration repair switch. -/
noncomputable section
open scoped BigOperators Classical

namespace GeneralizedBulk.Graph.Configuration

variable {N d : ℕ}

def switchPairing (p : Pairing (Stub N d)) (b c : Stub N d) : Pairing (Stub N d) :=
  conjugate (Equiv.swap b c) p

theorem switchPairing_involutive (b c : Stub N d) : Function.Involutive (fun p => switchPairing p b c) := by
  intro p
  apply Subtype.ext
  apply Equiv.ext
  intro h
  simp only [switchPairing,conjugate_apply,Equiv.symm_swap,Equiv.swap_apply_self]

def FarFromPair (p : Pairing (Stub N d)) (a b c : Stub N d) : Prop :=
  c.1 ≠ a.1 ∧ c.1 ≠ b.1 ∧ ∀ h, h.1 = a.1 ∨ h.1 = b.1 → (p.val h).1 ≠ c.1

set_option maxHeartbeats 1000000 in
theorem switchPairing_values (p : Pairing (Stub N d)) (a b c e : Stub N d)
    (hab : p.val a = b) (hce : p.val c = e)
    (hca : c ≠ a) (hcb : c ≠ b) (hea : e ≠ a) (heb : e ≠ b) :
    let r := switchPairing p b c
    r.val a = c ∧ r.val b = e ∧ r.val c = a ∧ r.val e = b := by
  have hab' : a ≠ b := by intro he; exact p.property.2 a (hab.trans he.symm)
  have hce' : c ≠ e := by intro he; exact p.property.2 c (hce.trans he.symm)
  have hba := partner_reverse p hab
  have hec := partner_reverse p hce
  dsimp only
  simp only [switchPairing,conjugate_apply,Equiv.symm_swap]
  simp [Equiv.swap_apply_def,hab,hce,hba,hec,hab',hab'.symm,hca,hca.symm,hcb,hcb.symm,
    hea,hea.symm,heb,heb.symm,hce',hce'.symm]

theorem switchPairing_outside (p : Pairing (Stub N d)) (a b c e : Stub N d)
    (hab : p.val a = b) (hce : p.val c = e) (h : Stub N d)
    (hh : h ∉ ({a,b,c,e} : Finset (Stub N d))) : (switchPairing p b c).val h = p.val h := by
  have ha : h ≠ a := fun he => hh (by simp [he])
  have hb : h ≠ b := fun he => hh (by simp [he])
  have hc : h ≠ c := fun he => hh (by simp [he])
  have he : h ≠ e := fun he => hh (by simp [he])
  have hpb : p.val h ≠ b := by intro h0; exact ha (p.val.injective (h0.trans hab.symm))
  have hpc : p.val h ≠ c := by
    intro h0
    have h1 := congrArg p.val h0
    rw [p.property.1 h,hce] at h1
    exact he h1
  simp [switchPairing,conjugate_apply,Equiv.swap_apply_def,hb,hc,hpb,hpc]

set_option maxHeartbeats 1000000 in
theorem switchPairing_repair_good (p : Pairing (Stub N d)) (a b c e : Stub N d)
    (hab : p.val a = b) (hce : p.val c = e)
    (hc : FarFromPair p a b c) (he : FarFromPair p a b e) (hceRoot : c.1 ≠ e.1) :
    ∀ h ∈ ({a,b,c,e} : Finset (Stub N d)), ¬ BadStub (switchPairing p b c) h := by
  have hca : c ≠ a := fun h => hc.1 (congrArg Prod.fst h)
  have hcb : c ≠ b := fun h => hc.2.1 (congrArg Prod.fst h)
  have hea : e ≠ a := fun h => he.1 (congrArg Prod.fst h)
  have heb : e ≠ b := fun h => he.2.1 (congrArg Prod.fst h)
  have hv := switchPairing_values p a b c e hab hce hca hcb hea heb
  let r := switchPairing p b c
  have hra : r.val a = c := hv.1
  have hrb : r.val b = e := hv.2.1
  have hrc : r.val c = a := hv.2.2.1
  have hre : r.val e = b := hv.2.2.2
  have gooda : ¬ BadStub r a := by
    rintro (hl | ⟨k,hk⟩)
    · rw [hra] at hl; exact hc.1 hl
    · have hkval : (r.val k).1 = c.1 := by rw [← hra]; exact hk.2.2.symm
      by_cases hkb : k = b
      · subst k; rw [hrb] at hkval; exact hceRoot hkval.symm
      by_cases hkc : k = c
      · subst k; exact hc.1 hk.1.symm
      by_cases hke : k = e
      · subst k; exact he.1 hk.1.symm
      have hka : k ≠ a := hk.2.1.symm
      have hout : k ∉ ({a,b,c,e} : Finset (Stub N d)) := by simp [hka,hkb,hkc,hke]
      rw [switchPairing_outside p a b c e hab hce k hout] at hkval
      exact hc.2.2 k (Or.inl hk.1.symm) hkval
  have goodb : ¬ BadStub r b := by
    rintro (hl | ⟨k,hk⟩)
    · rw [hrb] at hl; exact he.2.1 hl
    · have hkval : (r.val k).1 = e.1 := by rw [← hrb]; exact hk.2.2.symm
      by_cases hka : k = a
      · subst k; rw [hra] at hkval; exact hceRoot hkval
      by_cases hkc : k = c
      · subst k; exact hc.2.1 hk.1.symm
      by_cases hke : k = e
      · subst k; exact he.2.1 hk.1.symm
      have hkb : k ≠ b := hk.2.1.symm
      have hout : k ∉ ({a,b,c,e} : Finset (Stub N d)) := by simp [hka,hkb,hkc,hke]
      rw [switchPairing_outside p a b c e hab hce k hout] at hkval
      exact he.2.2 k (Or.inr hk.1.symm) hkval
  have goodc : ¬ BadStub r c := by
    rw [← hra]
    exact gooda ∘ (badStub_partner_iff r a).mp
  have goode : ¬ BadStub r e := by
    rw [← hrb]
    exact goodb ∘ (badStub_partner_iff r b).mp
  intro h hh
  simp only [Finset.mem_insert,Finset.mem_singleton] at hh
  rcases hh with rfl | rfl | rfl | rfl
  · exact gooda
  · exact goodb
  · exact goodc
  · exact goode

theorem switchPairing_repairs_defect (p : Pairing (Stub N d)) (a c : Stub N d)
    (ha : BadStub p a) (hc : FarFromPair p a (p.val a) c)
    (he : FarFromPair p a (p.val a) (p.val c)) (hceRoot : c.1 ≠ (p.val c).1) :
    defect (switchPairing p (p.val a) c) < defect p := by
  apply defect_strict_decrease_of_changed_good p (switchPairing p (p.val a) c)
    {a,p.val a,c,p.val c} (fun h hh => switchPairing_outside p a (p.val a) c (p.val c) rfl rfl h hh)
    (switchPairing_repair_good p a (p.val a) c (p.val c) rfl rfl hc he hceRoot) a (by simp) ha

end GeneralizedBulk.Graph.Configuration
