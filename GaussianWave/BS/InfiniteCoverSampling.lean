import GaussianWave.BS.FiniteCoverSampling
import GaussianWave.BS.TreeBallEmbedding

/-! Every literal finite cover seed extends to a locally injective map of
the actual infinite regular tree.  Neighbor orders beyond the supplied
finite prefix are the identity. -/
noncomputable section
open scoped Classical
namespace GaussianWave.BS
open Reused.Graph Reused.Graph.Configuration

structure GraphCoverDart {N m : ℕ} (G : RegularGraph N (m+2)) where
  parent : Fin N
  root : Fin N
  adj : G.val.Adj parent root

def graphCoverDartStep {N m : ℕ} {G : RegularGraph N (m+2)}
    (e : GraphCoverDart G) (j : Fin (m+1)) : GraphCoverDart G :=
  ⟨e.root, graphForwardNeighbor G e.adj j, graphForwardNeighbor_adj G e.adj j⟩

def defaultBranchDart {N m : ℕ} {G : RegularGraph N (m+2)} :
    GraphCoverDart G → List (Fin (m+1)) → GraphCoverDart G
  | e, [] => e
  | e, a::w => defaultBranchDart (graphCoverDartStep e a) w

theorem defaultBranchDart_append {N m : ℕ} {G : RegularGraph N (m+2)}
    (e : GraphCoverDart G) (w : List (Fin (m+1))) (a : Fin (m+1)) :
    defaultBranchDart e (w ++ [a]) = graphCoverDartStep (defaultBranchDart e w) a := by
  induction w generalizing e with
  | nil => rfl
  | cons b w ih => exact ih (graphCoverDartStep e b)

def infiniteBranchDart {N m : ℕ} {G : RegularGraph N (m+2)} :
    (k : ℕ) → GraphCoverDart G → BranchCoverOrdering (m+1) k →
      List (Fin (m+1)) → GraphCoverDart G
  | 0, e, _, w => defaultBranchDart e w
  | k+1, e, g, [] => e
  | k+1, e, g, a::w => infiniteBranchDart k (graphCoverDartStep e (g.1 a)) (g.2 a) w

def branchNodePermutation (q : ℕ) : (k : ℕ) → BranchCoverOrdering q k →
    List (Fin q) → Equiv.Perm (Fin q)
  | 0, _, _ => 1
  | k+1, g, [] => g.1
  | k+1, g, a::w => branchNodePermutation q k (g.2 a) w

@[simp] theorem infiniteBranchDart_nil {N m : ℕ} {G : RegularGraph N (m+2)}
    (k : ℕ) (e : GraphCoverDart G) (g : BranchCoverOrdering (m+1) k) :
    infiniteBranchDart k e g [] = e := by cases k <;> rfl

theorem infiniteBranchDart_append {N m : ℕ} {G : RegularGraph N (m+2)}
    (k : ℕ) (e : GraphCoverDart G) (g : BranchCoverOrdering (m+1) k)
    (w : List (Fin (m+1))) (a : Fin (m+1)) :
    infiniteBranchDart k e g (w ++ [a]) = graphCoverDartStep (infiniteBranchDart k e g w)
      (branchNodePermutation (m+1) k g w a) := by
  induction k generalizing e w with
  | zero => exact defaultBranchDart_append e w a
  | succ k ih =>
    cases w with
    | nil => simp only [List.nil_append, infiniteBranchDart, infiniteBranchDart_nil,
        branchNodePermutation]
    | cons b w => exact ih (graphCoverDartStep e (g.1 b)) (g.2 b) w

theorem infiniteBranchDart_finite {N m : ℕ} {G : RegularGraph N (m+2)}
    (k : ℕ) (e : GraphCoverDart G) (g : BranchCoverOrdering (m+1) k)
    (v : BranchVertex (m+1) k) :
    (infiniteBranchDart k e g (branchPath (m+1) k v)).root =
      branchGraphCover G k e.adj g v := by
  induction k generalizing e with
  | zero => cases v; rfl
  | succ k ih =>
    cases v with
    | inl u => rfl
    | inr av => exact ih (graphCoverDartStep e (g.1 av.1)) (g.2 av.1) av.2

def seedRootDart {N m : ℕ} (G : RegularGraph N (m+2)) (k : ℕ)
    (seed : VertexCoverSeed N m k) (a : Fin (m+2)) : GraphCoverDart G :=
  ⟨seed.1, graphNeighbor G seed.1 (seed.2.1 a),
    (canonicalPortLabeling G seed.1 (seed.2.1 a)).property⟩

def infiniteVertexGraphCover {N m : ℕ} (G : RegularGraph N (m+2)) (k : ℕ)
    (seed : VertexCoverSeed N m k) : RegularTreeVertex (m+2) → Fin N
  | none => seed.1
  | some (a,w) => (infiniteBranchDart k (seedRootDart G k seed a) (seed.2.2 a) w.reverse).root

theorem infiniteVertexGraphCover_restrict {N m : ℕ} (G : RegularGraph N (m+2)) (k : ℕ)
    (seed : VertexCoverSeed N m k) (v : VertexBallVertex (m+2) k) :
    infiniteVertexGraphCover G k seed (vertexBallEmbedding (m+2) k v) = vertexGraphCover G k seed v := by
  cases v with
  | inl u => rfl
  | inr av =>
    change (infiniteBranchDart k (seedRootDart G k seed av.1) (seed.2.2 av.1)
      (branchPath (m+1) k av.2).reverse.reverse).root = _
    rw [List.reverse_reverse, infiniteBranchDart_finite]
    rfl

theorem infiniteVertexGraphCover_parent {N m : ℕ} (G : RegularGraph N (m+2)) (k : ℕ)
    (seed : VertexCoverSeed N m k) (a : Fin (m+2)) (w : List (Fin (m+1))) :
    infiniteVertexGraphCover G k seed (regularTreeParent (some (a,w))) =
      (infiniteBranchDart k (seedRootDart G k seed a) (seed.2.2 a) w.reverse).parent := by
  cases w with
  | nil => rw [List.reverse_nil, infiniteBranchDart_nil]; rfl
  | cons b w =>
    rw [List.reverse_cons, infiniteBranchDart_append]
    rfl

theorem infiniteVertexGraphCover_child {N m : ℕ} (G : RegularGraph N (m+2)) (k : ℕ)
    (seed : VertexCoverSeed N m k) (a : Fin (m+2)) (w : List (Fin (m+1))) (b : Fin (m+1)) :
    infiniteVertexGraphCover G k seed (some (a,b::w)) =
      graphForwardNeighbor G
        (infiniteBranchDart k (seedRootDart G k seed a) (seed.2.2 a) w.reverse).adj
        (branchNodePermutation (m+1) k (seed.2.2 a) w.reverse b) := by
  change (infiniteBranchDart k _ _ (b::w).reverse).root = _
  rw [List.reverse_cons, infiniteBranchDart_append]
  rfl

theorem infiniteVertexGraphCover_parent_adj {N m : ℕ} (G : RegularGraph N (m+2)) (k : ℕ)
    (seed : VertexCoverSeed N m k) (v : RegularTreeVertex (m+2)) (hv : v ≠ none) :
    G.val.Adj (infiniteVertexGraphCover G k seed v)
      (infiniteVertexGraphCover G k seed (regularTreeParent v)) := by
  cases v with
  | none => exact (hv rfl).elim
  | some aw =>
    rcases aw with ⟨a,w⟩
    rw [infiniteVertexGraphCover_parent]
    exact (infiniteBranchDart k (seedRootDart G k seed a) (seed.2.2 a) w.reverse).adj.symm

def infiniteVertexGraphHom {N m : ℕ} (G : RegularGraph N (m+2)) (k : ℕ)
    (seed : VertexCoverSeed N m k) : regularWordTree (m+2) →g G.val where
  toFun := infiniteVertexGraphCover G k seed
  map_rel' := by
    intro v w h
    rcases h with ⟨hv,hp⟩ | ⟨hw,hp⟩
    · rw [← hp]
      exact infiniteVertexGraphCover_parent_adj G k seed v hv
    · rw [← hp]
      exact (infiniteVertexGraphCover_parent_adj G k seed w hw).symm

theorem graphForwardNeighbor_injective {N m : ℕ} (G : RegularGraph N (m+2))
    {parent root : Fin N} (h : G.val.Adj parent root) :
    Function.Injective (graphForwardNeighbor G h) := by
  intro i j hij
  apply Fin.succAbove_right_injective
  exact (canonicalPortLabeling G root).injective (Subtype.ext hij)

theorem infiniteVertexGraphCover_neighbor_injective {N m : ℕ} (G : RegularGraph N (m+2)) (k : ℕ)
    (seed : VertexCoverSeed N m k) (v : RegularTreeVertex (m+2)) :
    Function.Injective (fun i : RegularTreeNeighborIndex (m+2) v =>
      infiniteVertexGraphCover G k seed (regularTreeNeighbor v i)) := by
  cases v with
  | none =>
    intro i j hij
    change (infiniteBranchDart k (seedRootDart G k seed i) (seed.2.2 i) []).root =
      (infiniteBranchDart k (seedRootDart G k seed j) (seed.2.2 j) []).root at hij
    simp only [infiniteBranchDart_nil] at hij
    apply seed.2.1.injective
    apply (canonicalPortLabeling G seed.1).injective
    exact Subtype.ext hij
  | some aw =>
    rcases aw with ⟨a,w⟩
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some b =>
        change infiniteVertexGraphCover G k seed (regularTreeParent (some (a,w))) =
          infiniteVertexGraphCover G k seed (some (a,b::w)) at hij
        rw [infiniteVertexGraphCover_parent, infiniteVertexGraphCover_child] at hij
        exact (graphForwardNeighbor_ne_parent G _ _ hij.symm).elim
    | some b =>
      cases j with
      | none =>
        change infiniteVertexGraphCover G k seed (some (a,b::w)) =
          infiniteVertexGraphCover G k seed (regularTreeParent (some (a,w))) at hij
        rw [infiniteVertexGraphCover_parent, infiniteVertexGraphCover_child] at hij
        exact (graphForwardNeighbor_ne_parent G _ _ hij).elim
      | some c =>
        change infiniteVertexGraphCover G k seed (some (a,b::w)) =
          infiniteVertexGraphCover G k seed (some (a,c::w)) at hij
        rw [infiniteVertexGraphCover_child, infiniteVertexGraphCover_child] at hij
        congr 1
        exact (branchNodePermutation (m+1) k (seed.2.2 a) w.reverse).injective
          (graphForwardNeighbor_injective G _ hij)

theorem infiniteVertexGraphCover_local_injective {N m : ℕ} (G : RegularGraph N (m+2)) (k : ℕ)
    (seed : VertexCoverSeed N m k) (v : RegularTreeVertex (m+2)) :
    Set.InjOn (infiniteVertexGraphCover G k seed) ((regularWordTree (m+2)).neighborSet v) := by
  intro x hx y hy hxy
  obtain ⟨i,hi⟩ := exists_regularTreeNeighbor_of_adj v x hx
  obtain ⟨j,hj⟩ := exists_regularTreeNeighbor_of_adj v y hy
  have h := infiniteVertexGraphCover_neighbor_injective G k seed v
  rw [← hi, ← hj] at hxy
  exact hi.symm.trans ((congrArg (regularTreeNeighbor v) (h hxy)).trans hj)

end GaussianWave.BS
