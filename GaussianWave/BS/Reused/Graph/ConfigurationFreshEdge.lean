import GaussianWave.BS.Reused.Graph.ConfigurationSwitch

/-! A fresh distant non-loop edge exists once the number of half-edges
exceeds a degree-dependent constant plus the actual defect count. -/
noncomputable section
open scoped BigOperators Classical

namespace GaussianWave.BS.Reused.Graph.Configuration

variable {N d : ℕ}

def neighborRoots (p : Pairing (Stub N d)) (v : Fin N) : Finset (Fin N) :=
  Finset.univ.image (fun j : Fin d => (p.val (v,j)).1)

def forbiddenRoots (p : Pairing (Stub N d)) (a b : Stub N d) : Finset (Fin N) :=
  insert a.1 (insert b.1 (neighborRoots p a.1 ∪ neighborRoots p b.1))

theorem forbiddenRoots_card_le (p : Pairing (Stub N d)) (a b : Stub N d) :
    (forbiddenRoots p a b).card ≤ 2 + 2 * d := by
  have h1 : (neighborRoots p a.1).card ≤ d :=
    Finset.card_image_le.trans_eq (by simp)
  have h2 : (neighborRoots p b.1).card ≤ d :=
    Finset.card_image_le.trans_eq (by simp)
  have hu := Finset.card_union_le (neighborRoots p a.1) (neighborRoots p b.1)
  have hi := Finset.card_insert_le a.1 (insert b.1 (neighborRoots p a.1 ∪ neighborRoots p b.1))
  have hj := Finset.card_insert_le b.1 (neighborRoots p a.1 ∪ neighborRoots p b.1)
  dsimp only [forbiddenRoots]
  omega

theorem farFromPair_of_not_mem_forbidden (p : Pairing (Stub N d)) (a b c : Stub N d)
    (hc : c.1 ∉ forbiddenRoots p a b) : FarFromPair p a b c := by
  refine ⟨?_,?_,?_⟩
  · intro he; apply hc; simp [forbiddenRoots,he]
  · intro he; apply hc; simp [forbiddenRoots,he]
  · rintro ⟨v,j⟩ (hv | hv) he
    · dsimp at hv he
      apply hc
      rw [← he]
      apply Finset.mem_insert_of_mem
      apply Finset.mem_insert_of_mem
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      exact ⟨j,Finset.mem_univ _,by simpa only [hv]⟩
    · dsimp at hv he
      apply hc
      rw [← he]
      apply Finset.mem_insert_of_mem
      apply Finset.mem_insert_of_mem
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      exact ⟨j,Finset.mem_univ _,by simpa only [hv]⟩

def rootStubs (F : Finset (Fin N)) : Finset (Stub N d) := F ×ˢ Finset.univ

def loopStubs (p : Pairing (Stub N d)) : Finset (Stub N d) :=
  Finset.univ.filter (fun h => (p.val h).1 = h.1)

theorem loopStubs_card_le_defect (p : Pairing (Stub N d)) : (loopStubs p).card ≤ defect p := by
  apply Finset.card_le_card
  intro h hh
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl (Finset.mem_filter.mp hh).2⟩

def excludedStubs (p : Pairing (Stub N d)) (a b : Stub N d) : Finset (Stub N d) :=
  rootStubs (forbiddenRoots p a b) ∪
    (rootStubs (forbiddenRoots p a b)).image p.val ∪ loopStubs p

theorem excludedStubs_card_le (p : Pairing (Stub N d)) (a b : Stub N d) :
    (excludedStubs p a b).card ≤ 4 * d * (d + 1) + defect p := by
  let R : Finset (Stub N d) := rootStubs (forbiddenRoots p a b)
  have hR : R.card ≤ (2 + 2 * d) * d := by
    dsimp [R,rootStubs]
    rw [Finset.card_product,Finset.card_univ,Fintype.card_fin]
    exact Nat.mul_le_mul_right d (forbiddenRoots_card_le p a b)
  have hI : (R.image p.val).card ≤ R.card := Finset.card_image_le
  have hU := Finset.card_union_le R (R.image p.val)
  have hV := Finset.card_union_le (R ∪ R.image p.val) (loopStubs p)
  have hL := loopStubs_card_le_defect p
  change ((R ∪ R.image p.val) ∪ loopStubs p).card ≤ _
  nlinarith

theorem exists_fresh_edge (p : Pairing (Stub N d)) (a b : Stub N d)
    (hsize : 4 * d * (d + 1) + defect p < N * d) :
    ∃ c : Stub N d, FarFromPair p a b c ∧ FarFromPair p a b (p.val c) ∧ c.1 ≠ (p.val c).1 := by
  have hcard : (excludedStubs p a b).card < (Finset.univ : Finset (Stub N d)).card := by
    simpa only [Finset.card_univ,Fintype.card_prod,Fintype.card_fin] using
      (excludedStubs_card_le p a b).trans_lt hsize
  obtain ⟨c,hcu,hc⟩ := Finset.exists_mem_not_mem_of_card_lt_card hcard
  have hcr : c.1 ∉ forbiddenRoots p a b := by
    intro he
    exact hc (Finset.mem_union_left _ (Finset.mem_union_left _ (by simp [rootStubs,he])))
  have hpr : (p.val c).1 ∉ forbiddenRoots p a b := by
    intro he
    have hr : p.val c ∈ rootStubs (forbiddenRoots p a b) := by simp [rootStubs,he]
    have hi : c ∈ (rootStubs (forbiddenRoots p a b)).image p.val :=
      Finset.mem_image.mpr ⟨p.val c,hr,p.property.1 c⟩
    exact hc (Finset.mem_union_left _ (Finset.mem_union_right _ hi))
  have hnloop : c.1 ≠ (p.val c).1 := by
    intro he
    exact hc (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he.symm⟩))
  exact ⟨c,farFromPair_of_not_mem_forbidden p a b c hcr,
    farFromPair_of_not_mem_forbidden p a b (p.val c) hpr,hnloop⟩

theorem exists_defect_reducing_switch (p : Pairing (Stub N d)) (hp : 0 < defect p)
    (hsize : 4 * d * (d + 1) + defect p < N * d) :
    ∃ b c : Stub N d, defect (switchPairing p b c) < defect p := by
  obtain ⟨a,ha⟩ := Finset.card_pos.mp hp
  have hbad : BadStub p a := (Finset.mem_filter.mp ha).2
  obtain ⟨c,hc,he,hce⟩ := exists_fresh_edge p a (p.val a) hsize
  exact ⟨p.val a,c,switchPairing_repairs_defect p a c hbad hc he hce⟩

end GaussianWave.BS.Reused.Graph.Configuration
