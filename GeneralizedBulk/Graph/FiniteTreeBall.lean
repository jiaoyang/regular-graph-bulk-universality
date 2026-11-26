import Mathlib

/-!
# An explicit finite regular-tree ball about a distinguished edge

Each half of the central edge is the rooted `(d-1)`-ary word tree up to depth
`R`. The central roots have labels `0` and `1`, and all other vertices are
finite words in `Fin (d-1)` on one of the two sides. No analytic information
is encoded by the rooted graph isomorphism below.
-/
noncomputable section
open scoped Classical
namespace GeneralizedBulk.Graph

abbrev EdgeTreeVertex (d R : ℕ) := Fin 2 × (Σ k : Fin (R + 1), Fin k.val → Fin (d - 1))

def edgeTreeWord {d R : ℕ} (v : EdgeTreeVertex d R) : List (Fin (d - 1)) := List.ofFn v.2.2

def edgeTreeRoot (d R : ℕ) (side : Fin 2) : EdgeTreeVertex d R :=
  (side, ⟨⟨0, Nat.zero_lt_succ R⟩, Fin.elim0⟩)

/-- Two rooted word trees joined at their roots. This is the literal finite
ball of radius `R` about an edge in the infinite `d`-regular tree. -/
def finiteEdgeTreeBall (d R : ℕ) : SimpleGraph (EdgeTreeVertex d R) where
  Adj v w :=
    (v.1 ≠ w.1 ∧ v.2.1.val = 0 ∧ w.2.1.val = 0) ∨
      (v.1 = w.1 ∧ ((∃ a, edgeTreeWord v = a :: edgeTreeWord w) ∨
        (∃ a, edgeTreeWord w = a :: edgeTreeWord v)))
  symm v w h := by
    rcases h with h | h
    · exact Or.inl ⟨h.1.symm,h.2.2,h.2.1⟩
    · exact Or.inr ⟨h.1.symm,h.2.symm⟩
  loopless v h := by
    rcases h with h | h
    · exact h.1 rfl
    · rcases h.2 with ⟨a,ha⟩ | ⟨a,ha⟩ <;>
        have hh := congrArg List.length ha <;>
        simp only [List.length_cons] at hh <;> omega

theorem edgeTreeRoot_adj (d R : ℕ) :
    (finiteEdgeTreeBall d R).Adj (edgeTreeRoot d R 0) (edgeTreeRoot d R 1) :=
  Or.inl ⟨by change (0 : Fin 2) ≠ 1; decide,rfl,rfl⟩

def graphEdgeBall {V : Type*} (G : SimpleGraph V) (a b : V) (R : ℕ) : Set V :=
  {v | G.edist a v ≤ (R : ℕ∞) ∨ G.edist b v ≤ (R : ℕ∞)}

theorem graphEdgeBall_left {V : Type*} (G : SimpleGraph V) (a b : V) (R : ℕ) :
    a ∈ graphEdgeBall G a b R := by simp [graphEdgeBall]

theorem graphEdgeBall_right {V : Type*} (G : SimpleGraph V) (a b : V) (R : ℕ) :
    b ∈ graphEdgeBall G a b R := by simp [graphEdgeBall]

/-- A literal graph isomorphism to the fixed finite edge-tree ball, preserving
both distinguished endpoints in their actual order. -/
structure RootedEdgeBallIso {V : Type*} (G : SimpleGraph V) (a b : V) (d R : ℕ) where
  toIso : G.induce (graphEdgeBall G a b R) ≃g finiteEdgeTreeBall d R
  left : toIso ⟨a,graphEdgeBall_left G a b R⟩ = edgeTreeRoot d R 0
  right : toIso ⟨b,graphEdgeBall_right G a b R⟩ = edgeTreeRoot d R 1

end GeneralizedBulk.Graph
