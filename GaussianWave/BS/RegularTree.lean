import GaussianWave.BS.FiniteTreeGeometry

/-!
# A concrete countable regular word tree

The distinguished root has `d` child branches. Every other vertex has one
parent and `d-1` children. The vertices and adjacency are constructed, rather
than supplied through a geometric contract.
-/
noncomputable section
open scoped Classical
namespace GaussianWave.BS

abbrev RegularTreeVertex (d : ℕ) := Option (Fin d × List (Fin (d - 1)))

def regularTreeDepth {d : ℕ} : RegularTreeVertex d → ℕ
  | none => 0
  | some (_, w) => w.length + 1

def regularTreeParent {d : ℕ} : RegularTreeVertex d → RegularTreeVertex d
  | none => none
  | some (_, []) => none
  | some (a, _ :: w) => some (a, w)

theorem regularTreeDepth_parent {d : ℕ} (a : Fin d) (w : List (Fin (d - 1))) :
    regularTreeDepth (regularTreeParent (some (a, w))) + 1 = regularTreeDepth (some (a, w)) := by
  cases w <;> simp [regularTreeDepth, regularTreeParent]

def regularWordTree (d : ℕ) : SimpleGraph (RegularTreeVertex d) where
  Adj v w := (v ≠ none ∧ regularTreeParent v = w) ∨
    (w ≠ none ∧ regularTreeParent w = v)
  symm := by intro v w h; exact h.symm
  loopless := by
    intro v h
    rcases h with ⟨hv, hp⟩ | ⟨hv, hp⟩ <;>
      cases v with
      | none => exact hv rfl
      | some aw =>
          have hh : regularTreeDepth (regularTreeParent (some aw)) + 1 = regularTreeDepth (some aw) :=
            regularTreeDepth_parent aw.1 aw.2
          have he := congrArg regularTreeDepth hp
          omega

def RegularTreeNeighborIndex (d : ℕ) : RegularTreeVertex d → Type
  | none => Fin d
  | some _ => Option (Fin (d - 1))

instance regularTreeNeighborIndexFintype (d : ℕ) (v : RegularTreeVertex d) :
    Fintype (RegularTreeNeighborIndex d v) := by
  cases v with
  | none => exact inferInstanceAs (Fintype (Fin d))
  | some _ => exact inferInstanceAs (Fintype (Option (Fin (d - 1))))

def regularTreeNeighbor {d : ℕ} : (v : RegularTreeVertex d) → RegularTreeNeighborIndex d v → RegularTreeVertex d
  | none, j => some (j, [])
  | some aw, none => regularTreeParent (some aw)
  | some (a, w), some b => some (a, b :: w)

theorem regularTreeParent_ne_child {d : ℕ} (a : Fin d) (w : List (Fin (d - 1))) (b : Fin (d - 1)) :
    regularTreeParent (some (a, w)) ≠ some (a, b :: w) := by
  intro he
  have hp := regularTreeDepth_parent a w
  rw [he] at hp
  simp only [regularTreeDepth, List.length_cons] at hp
  omega

theorem regularTreeNeighbor_adj {d : ℕ} (v : RegularTreeVertex d) (i : RegularTreeNeighborIndex d v) :
    (regularWordTree d).Adj v (regularTreeNeighbor v i) := by
  cases v with
  | none => exact Or.inr ⟨Option.some_ne_none _, rfl⟩
  | some aw =>
      cases i with
      | none => exact Or.inl ⟨Option.some_ne_none _, rfl⟩
      | some b => exact Or.inr ⟨Option.some_ne_none _, rfl⟩

theorem regularTreeNeighbor_injective {d : ℕ} (v : RegularTreeVertex d) :
    Function.Injective (regularTreeNeighbor v) := by
  cases v with
  | none => intro i j h; exact congrArg Prod.fst (Option.some.inj h)
  | some aw =>
      intro i j h
      cases i with
      | none =>
          cases j with
          | none => rfl
          | some b => exact False.elim (regularTreeParent_ne_child aw.1 aw.2 b h)
      | some b =>
          cases j with
          | none => exact False.elim (regularTreeParent_ne_child aw.1 aw.2 b h.symm)
          | some c =>
              have hh := congrArg Prod.snd (Option.some.inj h)
              exact congrArg some (List.cons.inj hh).1

theorem exists_regularTreeNeighbor_of_adj {d : ℕ} (v w : RegularTreeVertex d)
    (h : (regularWordTree d).Adj v w) : ∃ i, regularTreeNeighbor v i = w := by
  cases v with
  | none =>
      rcases h with ⟨h, _⟩ | ⟨hw, hp⟩
      · exact False.elim (h rfl)
      cases w with
      | none => exact False.elim (hw rfl)
      | some aw =>
          rcases aw with ⟨a, l⟩
          cases l with
          | nil => exact ⟨a, rfl⟩
          | cons b l => exact False.elim (Option.some_ne_none _ hp)
  | some aw =>
      rcases h with ⟨_, hp⟩ | ⟨hw, hp⟩
      · exact ⟨none, hp⟩
      cases w with
      | none => exact False.elim (hw rfl)
      | some bw =>
          rcases aw with ⟨a, l⟩
          rcases bw with ⟨b, m⟩
          cases m with
          | nil => exact False.elim (Option.noConfusion hp)
          | cons c m =>
              have he : (b, m) = (a, l) := Option.some.inj hp
              cases he
              exact ⟨some c, rfl⟩

def regularTreeNeighborEquiv (d : ℕ) (v : RegularTreeVertex d) :
    RegularTreeNeighborIndex d v ≃ (regularWordTree d).neighborSet v :=
  Equiv.ofBijective (fun i => ⟨regularTreeNeighbor v i, regularTreeNeighbor_adj v i⟩)
    ⟨fun i j h => regularTreeNeighbor_injective v (congrArg Subtype.val h),
      fun w => by
        obtain ⟨i, hi⟩ := exists_regularTreeNeighbor_of_adj v w w.property
        exact ⟨i, Subtype.ext hi⟩⟩

instance regularWordTreeLocallyFinite (d : ℕ) : (regularWordTree d).LocallyFinite :=
  fun v => Fintype.ofEquiv (RegularTreeNeighborIndex d v) (regularTreeNeighborEquiv d v)

theorem regularWordTree_regular (d : ℕ) (hd : 1 ≤ d) : (regularWordTree d).IsRegularOfDegree d := by
  intro v
  rw [← SimpleGraph.card_neighborSet_eq_degree, ← Fintype.card_congr (regularTreeNeighborEquiv d v)]
  cases v <;> simp only [RegularTreeNeighborIndex, Fintype.card_fin, Fintype.card_option]
  omega

theorem regularWordTree_root_reachable (d : ℕ) (v : RegularTreeVertex d) :
    (regularWordTree d).Reachable none v := by
  cases v with
  | none => exact SimpleGraph.Reachable.refl _
  | some aw =>
      rcases aw with ⟨a, w⟩
      induction w with
      | nil => exact (regularTreeNeighbor_adj none a).reachable
      | cons b w ih => exact ih.trans (regularTreeNeighbor_adj (some (a, w)) (some b)).reachable

theorem regularWordTree_connected (d : ℕ) : (regularWordTree d).Connected := by
  exact (SimpleGraph.connected_iff_exists_forall_reachable _).mpr ⟨none, regularWordTree_root_reachable d⟩

theorem regularTree_adj_parent_of_depth_le {d : ℕ} {v w : RegularTreeVertex d}
    (h : (regularWordTree d).Adj v w) (hle : regularTreeDepth w ≤ regularTreeDepth v) :
    w = regularTreeParent v := by
  rcases h with ⟨_, hp⟩ | ⟨hw, hp⟩
  · exact hp.symm
  cases w with
  | none => exact False.elim (hw rfl)
  | some aw =>
      have hh : regularTreeDepth (regularTreeParent (some aw)) + 1 = regularTreeDepth (some aw) :=
        regularTreeDepth_parent aw.1 aw.2
      have he := congrArg regularTreeDepth hp
      omega

theorem regularWordTree_acyclic (d : ℕ) : (regularWordTree d).IsAcyclic := by
  intro v c hc
  obtain ⟨u, hu, hmax⟩ := Finset.exists_max_image c.support.toFinset regularTreeDepth
    ⟨v, by simpa only [List.mem_toFinset] using c.start_mem_support⟩
  have hu' : u ∈ c.support := List.mem_toFinset.mp hu
  let p := c.rotate hu'
  have hp : p.IsCycle := hc.rotate hu'
  have hlen : 3 ≤ p.length := hp.three_le_length
  have hmem (w) (hw : w ∈ p.support) : w ∈ c.support := by
    rw [p.support_eq_cons] at hw
    rcases List.mem_cons.mp hw with he | ht
    · simpa only [he] using hu'
    · exact List.mem_of_mem_tail ((c.support_rotate hu').perm.mem_iff.mp ht)
  have hmax' (i : ℕ) : regularTreeDepth (p.getVert i) ≤ regularTreeDepth u :=
    hmax _ (List.mem_toFinset.mpr (hmem _ (p.getVert_mem_support i)))
  have hfirst : (regularWordTree d).Adj u (p.getVert 1) := by
    simpa only [SimpleGraph.Walk.getVert_zero, zero_add] using p.adj_getVert_succ (i := 0) (by omega)
  have hlast : (regularWordTree d).Adj u (p.getVert (p.length - 1)) := by
    have hh := p.adj_getVert_succ (i := p.length - 1) (by omega)
    rw [show p.length - 1 + 1 = p.length by omega, p.getVert_length] at hh
    exact hh.symm
  have heq : p.getVert 1 = p.getVert (p.length - 1) :=
    (regularTree_adj_parent_of_depth_le hfirst (hmax' 1)).trans
      (regularTree_adj_parent_of_depth_le hlast (hmax' (p.length - 1))).symm
  have hi := hp.getVert_injOn' (by change 1 ≤ p.length - 1; omega)
    (by change p.length - 1 ≤ p.length - 1; rfl) heq
  omega

theorem regularWordTree_isTree (d : ℕ) : (regularWordTree d).IsTree :=
  ⟨regularWordTree_connected d, regularWordTree_acyclic d⟩

end GaussianWave.BS
