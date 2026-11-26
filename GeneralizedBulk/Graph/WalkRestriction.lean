import GeneralizedBulk.Graph.FiniteTreeBall

/-!
# Exact restriction of short walks to induced finite graph balls

Every vertex of a length-`k` walk is within distance `k` of its starting
point. Restriction is constructed recursively and is inverse to the literal
inclusion map, giving genuine bijections of fixed-length walk sets.
-/
noncomputable section
open scoped Classical
namespace GeneralizedBulk.Graph

variable {V : Type*} (G : SimpleGraph V) (s : Set V)

def restrictWalk : ∀ {u v : V} (p : G.Walk u v) (hp : ∀ x ∈ p.support, x ∈ s),
    (G.induce s).Walk ⟨u,hp u p.start_mem_support⟩ ⟨v,hp v p.end_mem_support⟩
  | _, _, .nil, _ => .nil
  | u, v, @SimpleGraph.Walk.cons _ _ _ w _ h q, hp =>
      let hq : ∀ x ∈ q.support, x ∈ s := fun x hx =>
        hp x (by simpa only [SimpleGraph.Walk.support_cons, List.mem_cons] using Or.inr hx)
      @SimpleGraph.Walk.cons s (G.induce s)
        ⟨u,hp u (SimpleGraph.Walk.cons h q).start_mem_support⟩
        ⟨w,hq w q.start_mem_support⟩
        ⟨v,hp v (SimpleGraph.Walk.cons h q).end_mem_support⟩ h (restrictWalk q hq)

theorem map_restrictWalk {u v : V} (p : G.Walk u v) (hp : ∀ x ∈ p.support, x ∈ s) :
    (restrictWalk G s p hp).map (SimpleGraph.Embedding.induce s).toHom = p := by
  induction p with
  | nil => rfl
  | cons h q ih =>
      simp only [restrictWalk, SimpleGraph.Walk.map_cons]
      congr 1
      exact ih _

theorem length_restrictWalk {u v : V} (p : G.Walk u v) (hp : ∀ x ∈ p.support, x ∈ s) :
    (restrictWalk G s p hp).length = p.length := by
  have h := congrArg SimpleGraph.Walk.length (map_restrictWalk G s p hp)
  simpa only [SimpleGraph.Walk.length_map] using h

/-- The length-`k` walks in an induced subgraph are exactly the original
walks whenever all original length-`k` walks stay in the selected set. -/
def inducedWalkLengthEquiv (u v : s) (k : ℕ)
    (hstay : ∀ p : G.Walk u.val v.val, p.length = k → ∀ x ∈ p.support, x ∈ s) :
    {p : G.Walk u.val v.val | p.length = k} ≃ {q : (G.induce s).Walk u v | q.length = k} where
  toFun p := ⟨restrictWalk G s p.val (hstay p.val p.property),
    (length_restrictWalk G s p.val _).trans p.property⟩
  invFun q := ⟨q.val.map (SimpleGraph.Embedding.induce s).toHom,
    (SimpleGraph.Walk.length_map _ q.val).trans q.property⟩
  left_inv p := Subtype.ext (map_restrictWalk G s p.val _)
  right_inv q := by
    apply Subtype.ext
    apply SimpleGraph.Walk.map_injective_of_injective
      (f := (SimpleGraph.Embedding.induce s).toHom) Subtype.val_injective u v
    exact map_restrictWalk G s (q.val.map (SimpleGraph.Embedding.induce s).toHom) _

/-- Every vertex visited by a walk lies within its length of the initial
vertex; this includes walks with arbitrary backtracking. -/
theorem walk_support_edist_le_length [DecidableEq V] {u v x : V} (p : G.Walk u v)
    (hx : x ∈ p.support) : G.edist u x ≤ (p.length : ℕ∞) := by
  exact (p.takeUntil x hx).edist_le.trans (by exact_mod_cast p.length_takeUntil_le hx)

/-- Walks starting at either distinguished endpoint stay in the literal
edge ball for all lengths at most the displayed radius. -/
theorem walk_stays_graphEdgeBall [DecidableEq V] (a b : V) (R : ℕ)
    {u v : V} (hu : u = a ∨ u = b) (p : G.Walk u v) (hk : p.length ≤ R) :
    ∀ x ∈ p.support, x ∈ graphEdgeBall G a b R := by
  intro x hx
  have hle : (p.length : ℕ∞) ≤ (R : ℕ∞) := by exact_mod_cast hk
  have hd := (walk_support_edist_le_length G p hx).trans hle
  rcases hu with rfl | rfl
  · exact Or.inl hd
  · exact Or.inr hd

end GeneralizedBulk.Graph
