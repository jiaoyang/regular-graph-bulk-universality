import GeneralizedBulk.Graph.AdmissibleSizeLimits
import Mathlib.Data.ZMod.Basic

/-! The labelled regular-graph ensemble is nonempty exactly at the article's
arithmetic sizes. The sufficiency proof constructs the usual cyclic graph:
paired short jumps, with an antipodal jump when the degree is odd. -/
noncomputable section
open scoped Classical
open Filter

namespace GeneralizedBulk.Graph

private def cyclicGraph (M : ℕ) [NeZero M] (S : Finset ℕ)
    (hzero : 0 ∉ S) (_hbound : ∀ a ∈ S, a < M)
    (hsymm : ∀ a ∈ S, M - a ∈ S) : SimpleGraph (ZMod M) where
  Adj x y := (y - x).val ∈ S
  symm := by
    intro x y hxy
    have hn : y - x ≠ 0 := by
      intro hz
      exact hzero (by simpa [hz] using hxy)
    have hneg : x - y = -(y - x) := by abel
    rw [hneg, ZMod.neg_val, if_neg hn]
    exact hsymm _ hxy
  loopless := by
    intro x
    simpa using hzero

private theorem cyclicGraph_regular (M : ℕ) [NeZero M] (S : Finset ℕ)
    (hzero : 0 ∉ S) (hbound : ∀ a ∈ S, a < M)
    (hsymm : ∀ a ∈ S, M - a ∈ S) :
    (cyclicGraph M S hzero hbound hsymm).IsRegularOfDegree S.card := by
  classical
  let G := cyclicGraph M S hzero hbound hsymm
  intro x
  let e : {a // a ∈ S} ≃ G.neighborSet x := {
    toFun := fun a => ⟨x + (a.val : ZMod M), by
      change (x + (a.val : ZMod M) - x).val ∈ S
      simpa only [add_sub_cancel_left, ZMod.val_natCast_of_lt (hbound a.val a.property)] using a.property⟩
    invFun := fun y => ⟨(y.val - x).val, y.property⟩
    left_inv := by
      intro a
      apply Subtype.ext
      change (x + (a.val : ZMod M) - x).val = a.val
      rw [add_sub_cancel_left, ZMod.val_natCast_of_lt (hbound a.val a.property)]
    right_inv := by
      intro y
      apply Subtype.ext
      change x + (((y.val - x).val : ℕ) : ZMod M) = y.val
      rw [ZMod.natCast_zmod_val]
      abel }
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  exact (Fintype.card_congr e.symm).trans (Fintype.card_coe S)

private theorem regularGraph_nonempty_of_jumps (M : ℕ) (hM : 0 < M)
    (S : Finset ℕ) (hzero : 0 ∉ S) (hbound : ∀ a ∈ S, a < M)
    (hsymm : ∀ a ∈ S, M - a ∈ S) : Nonempty (RegularGraph M S.card) := by
  classical
  letI : NeZero M := ⟨Nat.ne_of_gt hM⟩
  let G := cyclicGraph M S hzero hbound hsymm
  let e := ZMod.finEquiv M
  let H := G.comap e
  have hG := cyclicGraph_regular M S hzero hbound hsymm
  refine ⟨⟨H, ?_⟩⟩
  intro v
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  have hc := Fintype.card_congr ((SimpleGraph.Iso.comap e G).mapNeighborSet v)
  exact hc.trans ((SimpleGraph.card_neighborSet_eq_degree G (e v)).trans (hG (e v)))

private def pairedJumps (M r : ℕ) : Finset ℕ :=
  Finset.Icc 1 r ∪ Finset.Icc (M-r) (M-1)

private theorem mem_pairedJumps (M r a : ℕ) :
    a ∈ pairedJumps M r ↔ (1 ≤ a ∧ a ≤ r) ∨ (M-r ≤ a ∧ a ≤ M-1) := by
  simp only [pairedJumps, Finset.mem_union, Finset.mem_Icc]

private theorem pairedJumps_spec (M r : ℕ) (hr : 2*r < M) :
    0 ∉ pairedJumps M r ∧
      (∀ a ∈ pairedJumps M r, a < M) ∧
      (∀ a ∈ pairedJumps M r, M-a ∈ pairedJumps M r) ∧
      (pairedJumps M r).card = 2*r := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mem_pairedJumps]
    omega
  · intro a ha
    rw [mem_pairedJumps] at ha
    omega
  · intro a ha
    rw [mem_pairedJumps] at ha ⊢
    omega
  · have hdis : Disjoint (Finset.Icc 1 r) (Finset.Icc (M-r) (M-1)) := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      simp only [Finset.mem_Icc] at ha hb
      omega
    rw [pairedJumps, Finset.card_union_of_disjoint hdis, Nat.card_Icc, Nat.card_Icc]
    omega

/-- Paired cyclic jumps give every even degree below the vertex count. -/
theorem regularGraph_nonempty_even_degree (M r : ℕ) (hr : 2*r < M) :
    Nonempty (RegularGraph M (2*r)) := by
  obtain ⟨hzero, hbound, hsymm, hcard⟩ := pairedJumps_spec M r hr
  rw [← hcard]
  exact regularGraph_nonempty_of_jumps M (by omega) (pairedJumps M r) hzero hbound hsymm

/-- For an even vertex count, add the antipodal jump to obtain every odd
allowed degree. -/
theorem regularGraph_nonempty_odd_degree (t r : ℕ) (hr : 2*r+1 < 2*t) :
    Nonempty (RegularGraph (2*t) (2*r+1)) := by
  obtain ⟨hzero, hbound, hsymm, hcard⟩ := pairedJumps_spec (2*t) r (by omega)
  have ht : t ∉ pairedJumps (2*t) r := by
    rw [mem_pairedJumps]
    omega
  let S := insert t (pairedJumps (2*t) r)
  have hcardS : S.card = 2*r+1 := by
    simp only [S, Finset.card_insert_of_not_mem ht, hcard]
  rw [← hcardS]
  apply regularGraph_nonempty_of_jumps (2*t) (by omega) S
  · simp only [S, Finset.mem_insert, not_or]
    exact ⟨by omega, hzero⟩
  · intro a ha
    simp only [S, Finset.mem_insert] at ha
    rcases ha with rfl | ha
    · omega
    · exact hbound a ha
  · intro a ha
    simp only [S, Finset.mem_insert] at ha ⊢
    rcases ha with rfl | ha
    · left
      omega
    · exact Or.inr (hsymm a ha)

/-- Every size allowed by the article's arithmetic conditions supports an
actual labelled simple regular graph. -/
theorem regularGraph_nonempty_of_arithmetic (d M : ℕ)
    (hdegree : d < M) (hparity : Even (M*d)) :
    Nonempty (RegularGraph M d) := by
  by_cases hd : Even d
  · obtain ⟨r, rfl⟩ := even_iff_exists_two_mul.mp hd
    exact regularGraph_nonempty_even_degree M r hdegree
  · have hM : Even M := (Nat.even_mul.mp hparity).resolve_right hd
    obtain ⟨t, rfl⟩ := even_iff_exists_two_mul.mp hM
    obtain ⟨r, rfl⟩ := odd_iff_exists_bit1.mp (Nat.not_even_iff_odd.mp hd)
    exact regularGraph_nonempty_odd_degree t r hdegree

/-- A positive labelled graph ensemble is nonempty precisely when its degree
is smaller than the vertex count and its degree sum is even. -/
theorem regularGraph_nonempty_iff_arithmetic (d M : ℕ) (hM : 0 < M) :
    Nonempty (RegularGraph M d) ↔ d < M ∧ Even (M*d) := by
  constructor
  · rintro ⟨g⟩
    constructor
    · have h := g.val.degree_lt_card_verts ⟨0, hM⟩
      simpa only [g.property.degree_eq, Fintype.card_fin] using h
    · have h := g.val.sum_degrees_eq_twice_card_edges
      simp only [g.property.degree_eq, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul] at h
      have he : M*d = 2*g.val.edgeFinset.card := by simpa using h
      rw [he]
      exact even_two_mul _
  · rintro ⟨hdegree, hparity⟩
    exact regularGraph_nonempty_of_arithmetic d M hdegree hparity

/-- The existing ensemble-based admissibility condition equals exactly the
article's explicit conditions `M > d` and `M*d` even. This includes degree
zero and hence in particular every fixed degree at least three. -/
theorem admissibleSize_iff_arithmetic (d M : ℕ) :
    AdmissibleSize d M ↔ d < M ∧ Even (M*d) := by
  constructor
  · rintro ⟨hM, hgraphs⟩
    exact (regularGraph_nonempty_iff_arithmetic d M hM).mp hgraphs
  · rintro ⟨hdegree, hparity⟩
    exact ⟨by omega, regularGraph_nonempty_of_arithmetic d M hdegree hparity⟩

/-- The size filter appearing in the proved endpoints is exactly the
article's limit through integers `M > d` with even degree sum. -/
theorem admissibleSizeFilter_eq_arithmetic (d : ℕ) :
    admissibleSizeFilter d =
      atTop ⊓ principal {M : ℕ | d < M ∧ Even (M*d)} := by
  unfold admissibleSizeFilter
  congr 2
  ext M
  exact admissibleSize_iff_arithmetic d M

/-- There are arbitrarily large sizes satisfying the explicit arithmetic
conditions, so the article's size filter is nontrivial. -/
theorem frequently_arithmetic_admissible_sizes (d : ℕ) :
    ∃ᶠ M : ℕ in atTop, d < M ∧ Even (M*d) := by
  apply Filter.frequently_atTop.mpr
  intro k
  refine ⟨2*(k+1)*(d+1), ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · apply even_iff_exists_two_mul.mpr
    exact ⟨(k+1)*(d+1)*d, by ring⟩

theorem arithmeticSizeFilter_neBot (d : ℕ) :
    NeBot (atTop ⊓ principal {M : ℕ | d < M ∧ Even (M*d)}) :=
  Filter.frequently_iff_neBot.mp (frequently_arithmetic_admissible_sizes d)

end GeneralizedBulk.Graph
