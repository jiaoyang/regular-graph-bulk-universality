import GaussianWave.BS.UniformTreeCoverLaw
import GaussianWave.BS.TreeRerooting

/-! Actual symmetric edge-centered uniform cover sampling. Every side has
its own independent forward-neighbor ordering; reversing the directed graph
edge and swapping these orderings is a literal permutation of the seed set. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GaussianWave.BS
open Reused.Graph Reused.Graph.Configuration

/-- Uniform directed edge together with the two actual branch-order seeds. -/
abbrev EdgeCoverSeed {N m : ℕ} (G : RegularGraph N (m+2)) (k : ℕ) :=
  G.val.Dart × (Bool → BranchCoverOrdering (m+1) k)

def edgeGraphCover {N m : ℕ} (G : RegularGraph N (m+2)) (k : ℕ)
    (seed : EdgeCoverSeed G k) : EdgeBallVertex (m+2) k → Fin N
  | (false,v) => branchGraphCover G k seed.1.adj.symm (seed.2 false) v
  | (true,v) => branchGraphCover G k seed.1.adj (seed.2 true) v

@[simp] theorem edgeGraphCover_false_root {N m : ℕ} (G : RegularGraph N (m+2)) (k : ℕ)
    (seed : EdgeCoverSeed G k) :
    edgeGraphCover G k seed (false,branchRoot (m+1) k)=seed.1.fst :=
  branchGraphCover_root _ _ _ _
@[simp] theorem edgeGraphCover_true_root {N m : ℕ} (G : RegularGraph N (m+2)) (k : ℕ)
    (seed : EdgeCoverSeed G k) :
    edgeGraphCover G k seed (true,branchRoot (m+1) k)=seed.1.snd :=
  branchGraphCover_root _ _ _ _

def edgeCoverSeedReverse {N m : ℕ} (G : RegularGraph N (m+2)) (k : ℕ) :
    Equiv.Perm (EdgeCoverSeed G k) where
  toFun z := (z.1.symm,fun b => z.2 (!b))
  invFun z := (z.1.symm,fun b => z.2 (!b))
  left_inv z := by simp
  right_inv z := by simp

def edgeBallReverse (m k : ℕ) : Equiv.Perm (EdgeBallVertex (m+2) k) where
  toFun z := (!z.1,z.2)
  invFun z := (!z.1,z.2)
  left_inv z := by simp
  right_inv z := by simp

theorem edgeGraphCover_reverse {N m : ℕ} (G : RegularGraph N (m+2)) (k : ℕ)
    (seed : EdgeCoverSeed G k) (v : EdgeBallVertex (m+2) k) :
    edgeGraphCover G k (edgeCoverSeedReverse G k seed) v=
      edgeGraphCover G k seed (edgeBallReverse m k v) := by
  rcases v with ⟨b,v⟩
  cases b <;> rfl

/-- The actual finite law, without any invariance assumption. -/
def finiteEdgeCoverImageLaw {N m : ℕ} (G : RegularGraph N (m+2)) (k : ℕ) :
    Measure (EdgeBallVertex (m+2) k → Fin N) := uniformAtomicLaw (edgeGraphCover G k)

theorem finiteEdgeCoverImageLaw_probability {N m : ℕ} (G : RegularGraph N (m+2))
    (hN : 0<N) (k : ℕ) : IsProbabilityMeasure (finiteEdgeCoverImageLaw G k) := by
  let v : Fin N := ⟨0,hN⟩
  let a : G.val.Dart := ⟨(v,graphNeighbor G v 0),(canonicalPortLabeling G v 0).property⟩
  letI : Nonempty (EdgeCoverSeed G k) := ⟨(a,fun _ => default)⟩
  exact uniformAtomicLaw_isProbability _

/-- Exact reversal of the actual E-ball law. -/
theorem finiteEdgeCoverImageLaw_reverse {N m : ℕ} (G : RegularGraph N (m+2)) (k : ℕ) :
    Measure.map (fun x : EdgeBallVertex (m+2) k → Fin N => fun v => x (edgeBallReverse m k v))
      (finiteEdgeCoverImageLaw G k)=finiteEdgeCoverImageLaw G k := by
  rw [finiteEdgeCoverImageLaw,uniformAtomicLaw_map _ _
    (measurable_pi_lambda _ (fun _ => measurable_pi_apply _))]
  have he : (fun x : EdgeBallVertex (m+2) k → Fin N => fun v => x (edgeBallReverse m k v)) ∘
      edgeGraphCover G k=edgeGraphCover G k ∘ edgeCoverSeedReverse G k := by
    funext seed v
    exact (edgeGraphCover_reverse G k seed v).symm
  rw [he,uniformAtomicLaw_reindex]

/-- Independent boundary orderings establish actual E-ball consistency. -/
def edgeCoverSeedDepthEquiv {N m : ℕ} (G : RegularGraph N (m+2)) (k : ℕ) :
    EdgeCoverSeed G (k+1) ≃ EdgeCoverSeed G k ×
      (Bool → BranchLayer (m+1) k → Equiv.Perm (Fin (m+1))) where
  toFun z := ((z.1,fun b => branchCoverOrderingTruncate (m+1) k (z.2 b)),
    fun b => (branchCoverOrderingDepthEquiv (m+1) k (z.2 b)).2)
  invFun z := (z.1.1,fun b => (branchCoverOrderingDepthEquiv (m+1) k).symm (z.1.2 b,z.2 b))
  left_inv z := by
    dsimp only [branchCoverOrderingTruncate]
    apply Prod.ext
    · rfl
    · funext b
      exact (branchCoverOrderingDepthEquiv (m+1) k).symm_apply_apply (z.2 b)
  right_inv z := by
    dsimp only [branchCoverOrderingTruncate]
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext b
        exact congrArg Prod.fst ((branchCoverOrderingDepthEquiv (m+1) k).apply_symm_apply (z.1.2 b,z.2 b))
    · funext b
      exact congrArg Prod.snd ((branchCoverOrderingDepthEquiv (m+1) k).apply_symm_apply (z.1.2 b,z.2 b))

theorem finiteEdgeCoverImageLaw_consistent {N m : ℕ} (G : RegularGraph N (m+2)) (k : ℕ) :
    Measure.map (fun x : EdgeBallVertex (m+2) (k+1) → Fin N => fun v => x (edgeBallInclusion m k v))
      (finiteEdgeCoverImageLaw G (k+1))=finiteEdgeCoverImageLaw G k := by
  apply uniformAtomicLaw_projection (edgeCoverSeedDepthEquiv G k)
    (edgeGraphCover G (k+1)) (edgeGraphCover G k) _
    (measurable_pi_lambda _ (fun _ => measurable_pi_apply _))
  intro z
  funext v
  rcases v with ⟨b,v⟩
  cases b <;>
    simp only [edgeBallInclusion,edgeGraphCover,branchGraphCover_restrict]
  · have he := congrArg Prod.fst ((edgeCoverSeedDepthEquiv G k).apply_symm_apply z)
    exact congrFun (congrArg Prod.snd he) false ▸ rfl
  · have he := congrArg Prod.fst ((edgeCoverSeedDepthEquiv G k).apply_symm_apply z)
    exact congrFun (congrArg Prod.snd he) true ▸ rfl

end GaussianWave.BS
