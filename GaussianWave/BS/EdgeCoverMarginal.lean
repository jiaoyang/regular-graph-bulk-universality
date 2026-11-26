import GaussianWave.BS.EdgeBallEmbedding
import GaussianWave.BS.PermutationPortSplit

/-! The E-ball cover law is an actual marginal of the same uniform C-ball
sampler. An explicit finite seed bijection separates all unused last-layer
choices; no marginal identity is supplied as an assumption. -/
noncomputable section
open MeasureTheory
open scoped Classical
namespace GaussianWave.BS
open Reused.Graph Reused.Graph.Configuration

def EdgeCoverExtra (m : ℕ) : ℕ → Type
  | 0 => Equiv.Perm (Fin (m+1))
  | k+1 => Fin (m+1) → BranchLayer (m+1) k → Equiv.Perm (Fin (m+1))

instance edgeCoverExtraFintype (m k : ℕ) : Fintype (EdgeCoverExtra m k) := by
  cases k <;> dsimp only [EdgeCoverExtra] <;> infer_instance
instance edgeCoverExtraInhabited (m k : ℕ) : Inhabited (EdgeCoverExtra m k) := by
  cases k <;> dsimp only [EdgeCoverExtra] <;> infer_instance

/-- Retain an oriented root port, both E-branch orderings, and precisely the
unused last-layer choices from a C-ball seed. -/
def portEdgeCoverSeedEquiv (N m : ℕ) : (k : ℕ) →
    VertexCoverSeed N m k ≃
      (((Fin N × Fin (m+2)) × (Bool → BranchCoverOrdering (m+1) k)) × EdgeCoverExtra m k)
  | 0 =>
    { toFun := fun z => (((z.1,(portPermutationSplit (m+1) z.2.1).1),fun _ => ()),
        (portPermutationSplit (m+1) z.2.1).2)
      invFun := fun z => (z.1.1.1,portPermFromFirst z.1.1.2 z.2,fun _ => ())
      left_inv := by
        intro z
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · exact (portPermutationSplit (m+1)).symm_apply_apply z.2.1
          · funext j
            cases z.2.2 j
            rfl
      right_inv := by
        rintro ⟨⟨⟨v,p⟩,b⟩,ρ⟩
        dsimp only
        apply Prod.ext
        · apply Prod.ext
          · apply Prod.ext
            · rfl
            · exact portPermFromFirst_zero p ρ
          · funext j
            cases b j
            rfl
        · change (portPermutationSplit (m+1) (portPermFromFirst p ρ)).2=ρ
          exact congrArg (fun z : Fin (m+2) × Equiv.Perm (Fin (m+1)) => z.2)
            ((portPermutationSplit (m+1)).apply_symm_apply (p,ρ)) }
  | k+1 =>
    { toFun := fun z =>
        (((z.1,(portPermutationSplit (m+1) z.2.1).1),
          fun b => match b with
            | false => ((portPermutationSplit (m+1) z.2.1).2,
                fun j => branchCoverOrderingTruncate (m+1) k (z.2.2 j.succ))
            | true => z.2.2 0),
          fun j => (branchCoverOrderingDepthEquiv (m+1) k (z.2.2 j.succ)).2)
      invFun := fun z =>
        (z.1.1.1,portPermFromFirst z.1.1.2 (z.1.2 false).1,
          Fin.cases (z.1.2 true) (fun j =>
            (branchCoverOrderingDepthEquiv (m+1) k).symm ((z.1.2 false).2 j,z.2 j)))
      left_inv := by
        intro z
        dsimp only
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · exact (portPermutationSplit (m+1)).symm_apply_apply z.2.1
          · funext j
            induction j using Fin.cases with
            | zero => rfl
            | succ j =>
              exact (branchCoverOrderingDepthEquiv (m+1) k).symm_apply_apply (z.2.2 j.succ)
      right_inv := by
        intro z
        dsimp only
        have hp := (portPermutationSplit (m+1)).apply_symm_apply (z.1.1.2,(z.1.2 false).1)
        apply Prod.ext
        · apply Prod.ext
          · apply Prod.ext
            · rfl
            · exact congrArg Prod.fst hp
          · funext b
            cases b with
            | true => rfl
            | false =>
              apply Prod.ext
              · exact congrArg Prod.snd hp
              · funext j
                exact congrArg Prod.fst ((branchCoverOrderingDepthEquiv (m+1) k).apply_symm_apply
                  ((z.1.2 false).2 j,z.2 j))
        · funext j
          exact congrArg Prod.snd ((branchCoverOrderingDepthEquiv (m+1) k).apply_symm_apply
            ((z.1.2 false).2 j,z.2 j)) }

/-- Replace the retained root/port pair with its literal directed graph
edge, using the actual canonical neighbor labeling bijection. -/
def edgeCoverSeedRetainEquiv {N m : ℕ} (G : RegularGraph N (m+2)) (k : ℕ) :
    VertexCoverSeed N m k ≃ EdgeCoverSeed G k × EdgeCoverExtra m k :=
  (portEdgeCoverSeedEquiv N m k).trans
    { toFun := fun z => (((labelingDartEquiv G (canonicalPortLabeling G)) z.1.1,z.1.2),z.2)
      invFun := fun z => ((((labelingDartEquiv G (canonicalPortLabeling G)).symm z.1.1),z.1.2),z.2)
      left_inv := by intro z; simp
      right_inv := by intro z; simp }


/-- The excluded parent port is precisely the originally selected port. -/
theorem graphParentPort_reverse_neighbor {N m : ℕ} (G : RegularGraph N (m+2))
    (v : Fin N) (p : Fin (m+2)) :
    graphParentPort G (canonicalPortLabeling G v p).property.symm=p := by
  exact (canonicalPortLabeling G v).symm_apply_apply p

private theorem branchGraphCover_congr_root {N m : ℕ} (G : RegularGraph N (m+2))
    (k : ℕ) {parent root root' : Fin N} (h : G.val.Adj parent root) (h' : G.val.Adj parent root')
    (he : root=root') (orders : BranchCoverOrdering (m+1) k) (v : BranchVertex (m+1) k) :
    branchGraphCover G k h orders v=branchGraphCover G k h' orders v := by
  subst root'
  rfl

/-- Restricting a literal vertex sampler to the edge ball gives exactly the
retained literal edge sampler, pointwise for every finite seed. -/
theorem vertexGraphCover_edge_seed_restrict {N m : ℕ} (G : RegularGraph N (m+2))
    (k : ℕ) (seed : VertexCoverSeed N m k) (v : EdgeBallVertex (m+2) k) :
    vertexGraphCover G k seed (edgeToVertexBall m k v)=
      edgeGraphCover G k (edgeCoverSeedRetainEquiv G k seed).1 v := by
  cases k with
  | zero =>
    rcases v with ⟨b,v⟩
    cases b <;> cases v <;> rfl
  | succ k =>
    rcases v with ⟨b,v⟩
    cases b with
    | true => rfl
    | false =>
      cases v with
      | inl z => rfl
      | inr av =>
        change branchGraphCover G (k+1)
          (canonicalPortLabeling G seed.1 (seed.2.1 av.1.succ)).property
          (seed.2.2 av.1.succ) (branchVertexInclusion (m+1) k av.2)=_
        rw [branchGraphCover_restrict]
        change branchGraphCover G k
          (canonicalPortLabeling G seed.1 (seed.2.1 av.1.succ)).property
          (branchCoverOrderingTruncate (m+1) k (seed.2.2 av.1.succ)) av.2 =
          branchGraphCover G k
            (graphForwardNeighbor_adj G (canonicalPortLabeling G seed.1 (seed.2.1 0)).property.symm
              (portPermDeleteFirst seed.2.1 av.1))
            (branchCoverOrderingTruncate (m+1) k (seed.2.2 av.1.succ)) av.2
        apply branchGraphCover_congr_root
        unfold graphForwardNeighbor
        rw [graphParentPort_reverse_neighbor,portPermDeleteFirst_succAbove]
        rfl

/-- The actual E-ball uniform cover law is a proved marginal of the same
actual C-ball uniform cover law. -/
theorem finiteVertexCoverImageLaw_edge_marginal {N m : ℕ} (G : RegularGraph N (m+2)) (k : ℕ) :
    Measure.map (fun x : VertexBallVertex (m+2) k → Fin N => fun v => x (edgeToVertexBall m k v))
      (finiteVertexCoverImageLaw G k)=finiteEdgeCoverImageLaw G k := by
  apply uniformAtomicLaw_projection (edgeCoverSeedRetainEquiv G k)
    (vertexGraphCover G k) (edgeGraphCover G k) _
    (measurable_pi_lambda _ (fun _ => measurable_pi_apply _))
  intro z
  funext v
  rw [vertexGraphCover_edge_seed_restrict]
  have he := congrArg Prod.fst ((edgeCoverSeedRetainEquiv G k).apply_symm_apply z)
  rw [he]

/-- In particular, the constructed whole uniform cover process has exactly
the same actual E-ball sampler marginal. -/
theorem uniformTreeCoverLaw_edge_ball {N m : ℕ} (G : RegularGraph N (m+2)) (hN : 0<N) (k : ℕ) :
    Measure.map (fun z : RegularTreeVertex (m+2) → Fin N => fun v => z (edgeBallEmbedding m k v))
      (uniformTreeCoverLaw G hN : Measure _)=finiteEdgeCoverImageLaw G k := by
  let C := fun z : RegularTreeVertex (m+2) → Fin N => fun v => z (vertexBallEmbedding (m+2) k v)
  let T := fun z : VertexBallVertex (m+2) k → Fin N => fun v => z (edgeToVertexBall m k v)
  have he : (fun z : RegularTreeVertex (m+2) → Fin N => fun v => z (edgeBallEmbedding m k v))=T ∘ C := by
    funext z v
    exact congrArg z (edgeToVertexBall_embedding m k v).symm
  have hT : Measurable T := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have hC : Measurable C := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  rw [he,← Measure.map_map hT hC]
  have hb := uniformTreeCoverLaw_ball G hN k
  change Measure.map C (uniformTreeCoverLaw G hN : Measure _)=_ at hb
  rw [hb]
  exact finiteVertexCoverImageLaw_edge_marginal G k

end GaussianWave.BS
