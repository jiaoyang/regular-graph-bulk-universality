import GaussianWave.BS.LeafInnovationSplit
import GaussianWave.BS.EigenBallCoordinates

/-!
# Literal edge-ball covers of a larger vertex ball

At level `k+1`, the edge ball about the root and its `a`-th neighbor consists
of the entire forward branch `a` and the earlier vertex ball.  All maps here
are actual vertex maps; the restriction preserves the written eigenrelations.
-/
noncomputable section
open scoped BigOperators
namespace GaussianWave.BS

theorem branchVertexInclusion_injective (q k : ℕ) : Function.Injective (branchVertexInclusion q k) := by
  induction k with
  | zero => intro i j _; cases i; cases j; rfl
  | succ k ih =>
      intro i j h
      cases i with
      | inl u =>
          cases j with
          | inl v => cases u; cases v; rfl
          | inr av => exact Sum.noConfusion h
      | inr au =>
          cases j with
          | inl v => exact Sum.noConfusion h
          | inr av =>
              have hp := Sum.inr.inj h
              have ha := congrArg (fun p : Fin q × BranchVertex q (k + 1) => p.1) hp
              have hv := ih (congrArg (fun p : Fin q × BranchVertex q (k + 1) => p.2) hp)
              cases au; cases av; simp_all

def neighborExceptEquiv {m : ℕ} (a : Fin (m + 2)) :
    Fin (m + 1) ≃ {b : Fin (m + 2) // b ≠ a} :=
  Equiv.ofBijective (fun j => ⟨a.succAbove j, Fin.succAbove_ne a j⟩)
    ⟨fun i j h => Fin.succAbove_right_injective (congrArg Subtype.val h),
      fun b => by
        obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq b.property
        exact ⟨j, Subtype.ext hj⟩⟩

theorem neighborExceptEquiv_symm {m : ℕ} (a b : Fin (m + 2)) (h : b ≠ a) :
    a.succAbove ((neighborExceptEquiv a).symm ⟨b, h⟩) = b :=
  congrArg Subtype.val ((neighborExceptEquiv a).apply_symm_apply ⟨b, h⟩)

def edgeInVertexCover (m k : ℕ) (a : Fin (m + 2)) :
    EdgeBallVertex (m + 2) (k + 1) → VertexBallVertex (m + 2) (k + 1) :=
  fun bv => if bv.1 then Sum.inr (a, bv.2) else
    Sum.elim (fun _ => Sum.inl ())
      (fun jv => Sum.inr (a.succAbove jv.1, branchVertexInclusion (m + 1) k jv.2)) bv.2

def vertexCoreInEdgeCover (m k : ℕ) (a : Fin (m + 2)) :
    VertexBallVertex (m + 2) k → EdgeBallVertex (m + 2) (k + 1) :=
  Sum.elim (fun _ => (false, Sum.inl ())) (fun bv =>
    if h : bv.1 = a then (true, branchVertexInclusion (m + 1) k bv.2) else
      (false, Sum.inr ((neighborExceptEquiv a).symm ⟨bv.1, h⟩, bv.2)))

theorem edgeInVertexCover_core (m k : ℕ) (a : Fin (m + 2)) (v : VertexBallVertex (m + 2) k) :
    edgeInVertexCover m k a (vertexCoreInEdgeCover m k a v) = vertexBallInclusion m k v := by
  cases v with
  | inl u => cases u; rfl
  | inr bv =>
      by_cases h : bv.1 = a
      · simp only [vertexCoreInEdgeCover, Sum.elim_inr, h, dite_true, edgeInVertexCover, if_true]
        cases bv
        simp_all [vertexBallInclusion]
      · simp only [vertexCoreInEdgeCover, Sum.elim_inr, h, dite_false, edgeInVertexCover,
          Bool.false_eq_true, if_false, neighborExceptEquiv_symm]
        rfl

theorem branchEigenrelation_restrict (m k : ℕ) (energy parent : ℝ)
    (x : BranchVertex (m + 1) (k + 1) → ℝ) (hx : BranchEigenrelation m (k + 1) energy parent x) :
    BranchEigenrelation m k energy parent (fun v => x (branchVertexInclusion (m + 1) k v)) := by
  induction k generalizing parent with
  | zero => trivial
  | succ k ih =>
      constructor
      · simpa only [branchVertexInclusion, Sum.elim_inr, Sum.elim_inl,
          branchVertexInclusion_root] using hx.1
      · intro a
        simpa only [branchVertexInclusion, Sum.elim_inr, Sum.elim_inl] using
          ih (x (Sum.inl ())) (fun v => x (Sum.inr (a, v))) (hx.2 a)

theorem edgeInVertexCover_eigenrelation (m k : ℕ) (energy : ℝ)
    (x : VertexBallVertex (m + 2) (k + 1) → ℝ) (hx : VertexBallEigenrelation m (k + 1) energy x)
    (a : Fin (m + 2)) : EdgeBallEigenrelation m (k + 1) energy (fun v => x (edgeInVertexCover m k a v)) := by
  intro b
  cases b
  · constructor
    · change (∑ j : Fin (m + 1), x (Sum.inr
          (a.succAbove j, branchVertexInclusion (m + 1) k (branchRoot (m + 1) k)))) =
        energy * x (Sum.inl ()) - x (Sum.inr (a, branchRoot (m + 1) (k + 1)))
      simp_rw [branchVertexInclusion_root]
      have hs := Fin.sum_univ_succAbove
        (fun b : Fin (m + 2) => x (vertexBallNeighbor (m + 2) (k + 1) b)) a
      have hroot := hx.1
      change (∑ b : Fin (m + 2), x (vertexBallNeighbor (m + 2) (k + 1) b)) =
        energy * x (Sum.inl ()) at hroot
      change (∑ j : Fin (m + 1), x (vertexBallNeighbor (m + 2) (k + 1) (a.succAbove j))) =
        energy * x (Sum.inl ()) - x (vertexBallNeighbor (m + 2) (k + 1) a)
      linarith
    · intro j
      exact branchEigenrelation_restrict m k energy (x (vertexBallRoot (m + 2) (k + 1)))
        (fun v => x (Sum.inr (a.succAbove j, v))) (hx.2 (a.succAbove j))
  · exact hx.2 a

/-- A vertex-centered radius-`k+1` ball around either endpoint of the central
edge.  Neighbor zero is the other endpoint, followed by the ordered children. -/
def vertexInEdgeCover (m k : ℕ) (b : Bool) :
    VertexBallVertex (m + 2) k → EdgeBallVertex (m + 2) (k + 1) :=
  Sum.elim (fun _ => (b, Sum.inl ())) (fun av => Fin.cases
    ((!b), branchVertexInclusion (m + 1) k av.2)
    (fun j => (b, Sum.inr (j, av.2))) av.1)

theorem vertexInEdgeCover_eigenrelation (m k : ℕ) (energy : ℝ)
    (x : EdgeBallVertex (m + 2) (k + 1) → ℝ) (hx : EdgeBallEigenrelation m (k + 1) energy x)
    (b : Bool) : VertexBallEigenrelation m k energy (fun v => x (vertexInEdgeCover m k b v)) := by
  constructor
  · rw [Fin.sum_univ_succ]
    change x ((!b), branchVertexInclusion (m + 1) k (branchRoot (m + 1) k)) +
      (∑ j : Fin (m + 1), x (b, Sum.inr (j, branchRoot (m + 1) k))) =
      energy * x (b, Sum.inl ())
    rw [branchVertexInclusion_root]
    have h := (hx b).1
    change (∑ j : Fin (m + 1), x (b, Sum.inr (j, branchRoot (m + 1) k))) =
      energy * x (b, Sum.inl ()) - x ((!b), branchRoot (m + 1) (k + 1)) at h
    linarith
  · intro a
    refine Fin.cases ?_ (fun j => ?_) a
    · have h := branchEigenrelation_restrict m k energy
        (x (edgeBallEndpoint (m + 2) (k + 1) b)) (fun v => x ((!b), v)) (by
          simpa only [Bool.not_not] using hx (!b))
      exact h
    · exact (hx b).2 j

end GaussianWave.BS
