import GeneralizedBulk.Graph.TreePolynomialLocalization

/-! Fixed-radius regular-graph ball sizes from exact finite walk counts. -/
noncomputable section
open scoped BigOperators Classical
namespace GeneralizedBulk.Graph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- Every row of a regular adjacency power counts exactly `d^k` walks. -/
theorem regular_adjacency_power_row_sum {d : ℕ} (hG : G.IsRegularOfDegree d)
    (k : ℕ) (v : V) : (∑ w, (G.adjMatrix ℕ ^ k) v w) = d ^ k := by
  have hrow (v : V) : (∑ w, G.adjMatrix ℕ v w) = d := by
    have h := G.adjMatrix_mulVec_const_apply_of_regular (α := ℕ) (a := 1) hG (v := v)
    simpa only [Matrix.mulVec, dotProduct, Function.const_apply, mul_one] using h
  induction k generalizing v with
  | zero => simp [Matrix.one_apply]
  | succ k ih =>
      simp only [pow_succ', Matrix.mul_apply]
      calc
        _ = ∑ x, ∑ w, G.adjMatrix ℕ v x * (G.adjMatrix ℕ ^ k) x w := Finset.sum_comm
        _ = ∑ x, G.adjMatrix ℕ v x * d ^ k := by simp_rw [← Finset.mul_sum, ih]
        _ = d * d ^ k := by rw [← Finset.sum_mul, hrow]
        _ = _ := rfl

def graphBallVertices (v : V) (R : ℕ) : Finset V :=
  Finset.univ.filter (fun w => G.edist v w ≤ (R : ℕ∞))

def regularBallBound (d R : ℕ) : ℕ := ∑ k ∈ Finset.range (R + 1), d ^ k

/-- A short-distance indicator is dominated by the sum of actual walk
counts of lengths at most the radius. -/
theorem graphBall_indicator_le_walk_sum (v w : V) (R : ℕ) :
    (if G.edist v w ≤ (R : ℕ∞) then 1 else 0) ≤
      ∑ k ∈ Finset.range (R + 1), (G.adjMatrix ℕ ^ k) v w := by
  split_ifs with hclose
  · have hne : G.edist v w ≠ ⊤ := ne_top_of_le_ne_top (by simp) hclose
    obtain ⟨p,hp⟩ := G.exists_walk_of_edist_ne_top hne
    have hlen : p.length ≤ R := by
      exact_mod_cast (show (p.length : ℕ∞) ≤ (R : ℕ∞) by rw [hp]; exact hclose)
    have hwalk : 1 ≤ (G.adjMatrix ℕ ^ p.length) v w := by
      rw [SimpleGraph.adjMatrix_pow_apply_eq_card_walk]
      exact Fintype.card_pos_iff.mpr ⟨⟨p,rfl⟩⟩
    exact hwalk.trans (Finset.single_le_sum (f := fun k : ℕ => (G.adjMatrix ℕ ^ k) v w)
      (fun k _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hlen)))
  · exact Nat.zero_le _

/-- The fixed-radius ball has a bound independent of the graph size. -/
theorem regular_graphBall_card_le {d : ℕ} (hG : G.IsRegularOfDegree d) (v : V) (R : ℕ) :
    (graphBallVertices G v R).card ≤ regularBallBound d R := by
  rw [graphBallVertices, Finset.card_eq_sum_ones, Finset.sum_filter]
  calc
    _ ≤ ∑ w, ∑ k ∈ Finset.range (R + 1), (G.adjMatrix ℕ ^ k) v w :=
      Finset.sum_le_sum (fun w _ => graphBall_indicator_le_walk_sum G v w R)
    _ = _ := by
      rw [Finset.sum_comm]
      simp_rw [regular_adjacency_power_row_sum G hG]
      rfl

end GeneralizedBulk.Graph
