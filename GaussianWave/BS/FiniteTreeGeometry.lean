import Mathlib

/-!
# Literal finite regular-tree balls

The recursion records a root and its ordered child subtrees.  A vertex ball
`C_k` has radius `k+1`, whereas an edge ball `E_k` has radius `k` about its
central edge.  These are finite combinatorial types, with no probabilistic
or entropy assumptions.
-/
noncomputable section
open scoped BigOperators
namespace GaussianWave.BS

/-- A rooted `q`-ary tree of depth `k`, including its root. -/
def BranchVertex (q : ℕ) : ℕ → Type
  | 0 => Unit
  | k + 1 => Unit ⊕ (Fin q × BranchVertex q k)

instance branchVertexFintype (q k : ℕ) : Fintype (BranchVertex q k) := by
  induction k with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ k ih =>
      letI := ih
      exact inferInstanceAs (Fintype (Unit ⊕ (Fin q × BranchVertex q k)))

instance branchVertexDecidableEq (q k : ℕ) : DecidableEq (BranchVertex q k) := Classical.decEq _

def branchRoot (q : ℕ) : (k : ℕ) → BranchVertex q k
  | 0 => ()
  | _ + 1 => Sum.inl ()

/-- The full vertex ball `C_k=B_k(B_1(o))`. -/
abbrev VertexBallVertex (d k : ℕ) := Unit ⊕ (Fin d × BranchVertex (d - 1) k)

/-- The full edge ball `E_k=B_k(e)`. -/
abbrev EdgeBallVertex (d k : ℕ) := Bool × BranchVertex (d - 1) k

def vertexBallRoot (d k : ℕ) : VertexBallVertex d k := Sum.inl ()

def vertexBallNeighbor (d k : ℕ) (a : Fin d) : VertexBallVertex d k :=
  Sum.inr (a, branchRoot (d - 1) k)

def edgeBallEndpoint (d k : ℕ) (b : Bool) : EdgeBallVertex d k :=
  (b, branchRoot (d - 1) k)

@[simp] theorem card_branchVertex_zero (q : ℕ) :
    Fintype.card (BranchVertex q 0) = 1 := by simp [BranchVertex]

@[simp] theorem card_branchVertex_succ (q k : ℕ) :
    Fintype.card (BranchVertex q (k + 1)) =
      1 + q * Fintype.card (BranchVertex q k) := by
  simp [BranchVertex, Fintype.card_sum, Fintype.card_prod]

theorem card_branchVertex (q k : ℕ) :
    Fintype.card (BranchVertex q k) = ∑ j ∈ Finset.range (k + 1), q ^ j := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [card_branchVertex_succ, ih]
      have hs : (∑ j ∈ Finset.range (k + 2), q ^ j) =
          1 + q * ∑ j ∈ Finset.range (k + 1), q ^ j := by
        rw [Finset.sum_range_succ']
        simp only [pow_zero, pow_succ', ← Finset.mul_sum]
        omega
      exact hs.symm

@[simp] theorem card_vertexBallVertex (d k : ℕ) :
    Fintype.card (VertexBallVertex d k) =
      1 + d * Fintype.card (BranchVertex (d - 1) k) := by
  simp [VertexBallVertex, Fintype.card_sum, Fintype.card_prod]

@[simp] theorem card_edgeBallVertex (d k : ℕ) :
    Fintype.card (EdgeBallVertex d k) =
      2 * Fintype.card (BranchVertex (d - 1) k) := by
  simp [EdgeBallVertex, Fintype.card_prod]

/-- The ambient cardinality cancellation retains exactly one root vertex. -/
theorem ball_ambient_card_balance (d k : ℕ) :
    2 * Fintype.card (VertexBallVertex d k) =
      d * Fintype.card (EdgeBallVertex d k) + 2 := by
  rw [card_vertexBallVertex, card_edgeBallVertex]
  ring

theorem ball_ambient_real_card_balance (d k : ℕ) :
    (Fintype.card (VertexBallVertex d k) : ℝ) -
      (d : ℝ) / 2 * Fintype.card (EdgeBallVertex d k) = 1 := by
  have h := ball_ambient_card_balance d k
  have hR : (2 : ℝ) * Fintype.card (VertexBallVertex d k) =
      d * Fintype.card (EdgeBallVertex d k) + 2 := by exact_mod_cast h
  linarith

/-- One block of `q-1` sibling differences at every non-leaf branch vertex. -/
def BranchInnovation (q : ℕ) : ℕ → Type
  | 0 => Empty
  | k + 1 => Fin (q - 1) ⊕ (Fin q × BranchInnovation q k)

instance branchInnovationFintype (q k : ℕ) : Fintype (BranchInnovation q k) := by
  induction k with
  | zero => exact inferInstanceAs (Fintype Empty)
  | succ k ih =>
      letI := ih
      exact inferInstanceAs (Fintype (Fin (q - 1) ⊕ (Fin q × BranchInnovation q k)))

instance branchInnovationDecidableEq (q k : ℕ) : DecidableEq (BranchInnovation q k) :=
  Classical.decEq _

@[simp] theorem card_branchInnovation_zero (q : ℕ) :
    Fintype.card (BranchInnovation q 0) = 0 := by simp [BranchInnovation]

@[simp] theorem card_branchInnovation_succ (q k : ℕ) :
    Fintype.card (BranchInnovation q (k + 1)) =
      q - 1 + q * Fintype.card (BranchInnovation q k) := by
  simp [BranchInnovation, Fintype.card_sum, Fintype.card_prod]

theorem card_branchInnovation_add_one (q k : ℕ) (hq : 1 ≤ q) :
    Fintype.card (BranchInnovation q k) + 1 = q ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [card_branchInnovation_succ, pow_succ]
      have hq' : q - 1 + 1 = q := by omega
      nlinarith

abbrev VertexBallInnovation (d k : ℕ) := Fin d ⊕ (Fin d × BranchInnovation (d - 1) k)
abbrev EdgeBallInnovation (d k : ℕ) := Bool ⊕ (Bool × BranchInnovation (d - 1) k)

/-- The innovation dimensions are the actual source dimensions in (4.1). -/
theorem card_vertexBallInnovation (d k : ℕ) (hd : 2 ≤ d) :
    Fintype.card (VertexBallInnovation d k) = d * (d - 1) ^ k := by
  have h := card_branchInnovation_add_one (d - 1) k (by omega)
  simp only [VertexBallInnovation, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  nlinarith

theorem card_edgeBallInnovation (d k : ℕ) (hd : 2 ≤ d) :
    Fintype.card (EdgeBallInnovation d k) = 2 * (d - 1) ^ k := by
  have h := card_branchInnovation_add_one (d - 1) k (by omega)
  simp only [EdgeBallInnovation, Fintype.card_sum, Fintype.card_prod, Fintype.card_bool]
  nlinarith

theorem ball_innovation_card_balance (d k : ℕ) (hd : 2 ≤ d) :
    2 * Fintype.card (VertexBallInnovation d k) =
      d * Fintype.card (EdgeBallInnovation d k) := by
  rw [card_vertexBallInnovation d k hd, card_edgeBallInnovation d k hd]
  ring

end GaussianWave.BS
