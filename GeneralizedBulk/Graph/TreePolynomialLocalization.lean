import GeneralizedBulk.Graph.WalkRestriction
import GeneralizedBulk.Graph.PolynomialCompression

/-!
# Literal tree-ball geometry determines finite polynomial compressions

Fixed-length walk bijections, followed by the exact adjacency walk-count
formula, transfer every polynomial of sufficiently small degree to the
explicit finite regular-tree edge ball.
-/
noncomputable section
open scoped BigOperators Classical
namespace GeneralizedBulk.Graph

/-- A graph isomorphism preserves the entries of every adjacency power. -/
theorem graphIso_adjacency_power
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    (k : ℕ) (u v : V) : (G.adjMatrix ℂ ^ k) u v = (H.adjMatrix ℂ ^ k) (e u) (e v) := by
  induction k generalizing u v with
  | zero => simp only [pow_zero, Matrix.one_apply, e.injective.eq_iff]
  | succ k ih =>
      simp only [pow_succ, Matrix.mul_apply]
      calc
        _ = ∑ w : V, (H.adjMatrix ℂ ^ k) (e u) (e w) * H.adjMatrix ℂ (e w) (e v) := by
          apply Finset.sum_congr rfl
          intro w hw
          rw [ih]
          congr 1
          simp only [SimpleGraph.adjMatrix_apply, e.map_adj_iff]
        _ = _ := Equiv.sum_comp e.toEquiv (fun w : W => (H.adjMatrix ℂ ^ k) (e u) w * H.adjMatrix ℂ w (e v))

/-- Restricting all relevant walks to an induced graph preserves the
literal adjacency power entry. -/
theorem adjacency_power_eq_induced
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (s : Set V)
    (u v : s) (k : ℕ)
    (hstay : ∀ p : G.Walk u.val v.val, p.length = k → ∀ x ∈ p.support, x ∈ s) :
    (G.adjMatrix ℂ ^ k) u.val v.val = ((G.induce s).adjMatrix ℂ ^ k) u v := by
  rw [SimpleGraph.adjMatrix_pow_apply_eq_card_walk, SimpleGraph.adjMatrix_pow_apply_eq_card_walk]
  exact congrArg (fun n : ℕ => (n : ℂ)) (Fintype.card_congr (inducedWalkLengthEquiv G s u v k hstay))

def edgeEndpoint {V : Type*} (a b : V) : Fin 2 → V := ![a,b]

def edgeBallEndpoint {V : Type*} (G : SimpleGraph V) (a b : V) (R : ℕ) :
    Fin 2 → graphEdgeBall G a b R :=
  ![⟨a,graphEdgeBall_left G a b R⟩,⟨b,graphEdgeBall_right G a b R⟩]

@[simp] theorem edgeBallEndpoint_val {V : Type*} (G : SimpleGraph V) (a b : V) (R : ℕ) (i : Fin 2) :
    (edgeBallEndpoint G a b R i).val = edgeEndpoint a b i := by fin_cases i <;> rfl

theorem rootedEdgeBallIso_endpoint {V : Type*} {G : SimpleGraph V} {a b : V} {d R : ℕ}
    (e : RootedEdgeBallIso G a b d R) (i : Fin 2) :
    e.toIso (edgeBallEndpoint G a b R i) = edgeTreeRoot d R i := by
  fin_cases i
  · exact e.left
  · exact e.right

/-- A rooted edge-ball isomorphism determines every short adjacency power
between the two physical edge endpoints. -/
theorem adjacency_power_edge_tree
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (a b : V) (d R : ℕ)
    (e : RootedEdgeBallIso G a b d R) (k : ℕ) (hk : k ≤ R) (i j : Fin 2) :
    (G.adjMatrix ℂ ^ k) (edgeEndpoint a b i) (edgeEndpoint a b j) =
      ((finiteEdgeTreeBall d R).adjMatrix ℂ ^ k) (edgeTreeRoot d R i) (edgeTreeRoot d R j) := by
  have hstay : ∀ p : G.Walk (edgeBallEndpoint G a b R i).val (edgeBallEndpoint G a b R j).val,
      p.length = k → ∀ x ∈ p.support, x ∈ graphEdgeBall G a b R := by
    intro p hp
    apply walk_stays_graphEdgeBall G a b R _ p (hp.trans_le hk)
    fin_cases i <;> simp only [edgeBallEndpoint, Matrix.cons_val_zero, Matrix.cons_val_one] <;> simp
  have hp := adjacency_power_eq_induced G (graphEdgeBall G a b R)
    (edgeBallEndpoint G a b R i) (edgeBallEndpoint G a b R j) k hstay
  simp only [edgeBallEndpoint_val] at hp
  rw [hp, graphIso_adjacency_power e.toIso, rootedEdgeBallIso_endpoint, rootedEdgeBallIso_endpoint]

def graphPolynomialMatrix {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (Q : Polynomial ℝ) :
    Matrix V V ℂ := ∑ k ∈ Q.support, (Q.coeff k : ℂ) • G.adjMatrix ℂ ^ k

def edgePolynomialProfile (d R : ℕ) (Q : Polynomial ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (graphPolynomialMatrix (finiteEdgeTreeBall d R) Q).submatrix (edgeTreeRoot d R) (edgeTreeRoot d R)

/-- The local polynomial compression is exactly the deterministic two-vertex
profile in the fixed finite word tree. -/
theorem polynomial_edge_tree
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (a b : V) (d R : ℕ)
    (e : RootedEdgeBallIso G a b d R) (Q : Polynomial ℝ) (hQ : Q.natDegree ≤ R) (i j : Fin 2) :
    graphPolynomialMatrix G Q (edgeEndpoint a b i) (edgeEndpoint a b j) = edgePolynomialProfile d R Q i j := by
  simp only [graphPolynomialMatrix, edgePolynomialProfile, Matrix.submatrix_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [adjacency_power_edge_tree G a b d R e k ((Polynomial.le_natDegree_of_ne_zero
    (Polynomial.mem_support_iff.mp hk)).trans hQ) i j]

/-- A spectral polynomial cannot connect vertices whose graph distance
exceeds its degree. -/
theorem graphPolynomialMatrix_eq_zero_of_far
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (Q : Polynomial ℝ)
    (u v : V) (hfar : (Q.natDegree : ℕ∞) < G.edist u v) : graphPolynomialMatrix G Q u v = 0 := by
  simp only [graphPolynomialMatrix, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro k hk
  have hzero : (G.adjMatrix ℂ ^ k) u v = 0 := by
    rw [SimpleGraph.adjMatrix_pow_apply_eq_card_walk]
    have hdegree : k ≤ Q.natDegree := Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hk)
    letI : IsEmpty {p : G.Walk u v // p.length = k} := ⟨fun p => by
      have hd := p.val.edist_le
      rw [p.property] at hd
      exact (not_le_of_gt hfar) (hd.trans (by exact_mod_cast hdegree))⟩
    simp
  rw [hzero, mul_zero]

def fourEndpoints {V : Type*} (a b c e : V) : Fin 4 → V := ![a,b,c,e]

def twoEdgePolynomialProfile (d R : ℕ) (Q : Polynomial ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  let P := edgePolynomialProfile d R Q
  !![P 0 0, P 0 1, 0, 0;
     P 1 0, P 1 1, 0, 0;
     0, 0, P 0 0, P 0 1;
     0, 0, P 1 0, P 1 1]

/-- Two canonical edge neighborhoods with no short connecting walk have a
single deterministic four-endpoint polynomial compression. -/
theorem polynomial_two_edge_tree
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (a b c e : V) (d R : ℕ) (left : RootedEdgeBallIso G a b d R)
    (right : RootedEdgeBallIso G c e d R) (Q : Polynomial ℝ) (hQ : Q.natDegree ≤ R)
    (hsep : ∀ i j : Fin 2, (Q.natDegree : ℕ∞) <
      G.edist (edgeEndpoint a b i) (edgeEndpoint c e j)) :
    (graphPolynomialMatrix G Q).submatrix (fourEndpoints a b c e) (fourEndpoints a b c e) =
      twoEdgePolynomialProfile d R Q := by
  have hleft := polynomial_edge_tree G a b d R left Q hQ
  have hright := polynomial_edge_tree G c e d R right Q hQ
  have hcross (i j : Fin 2) := graphPolynomialMatrix_eq_zero_of_far G Q
    (edgeEndpoint a b i) (edgeEndpoint c e j) (hsep i j)
  have hback (i j : Fin 2) : graphPolynomialMatrix G Q
      (edgeEndpoint c e i) (edgeEndpoint a b j) = 0 := by
    apply graphPolynomialMatrix_eq_zero_of_far
    rw [SimpleGraph.edist_comm]
    exact hsep j i
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.submatrix_apply, fourEndpoints, twoEdgePolynomialProfile,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.vecHead, Matrix.vecTail] <;>
    first | exact hleft 0 0 | exact hleft 0 1 | exact hleft 1 0 | exact hleft 1 1 |
      exact hright 0 0 | exact hright 0 1 | exact hright 1 0 | exact hright 1 1 |
      exact hcross 0 0 | exact hcross 0 1 | exact hcross 1 0 | exact hcross 1 1 |
      exact hback 0 0 | exact hback 0 1 | exact hback 1 0 | exact hback 1 1

end GeneralizedBulk.Graph
