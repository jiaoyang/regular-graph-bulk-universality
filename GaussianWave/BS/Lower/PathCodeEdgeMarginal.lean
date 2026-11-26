import GaussianWave.BS.Lower.PathRecoloringSampling
import GaussianWave.BS.Lower.PathCodeEntropy
import GaussianWave.BS.TreeRerooting
import GaussianWave.BS.RootedBallAutomorphismDecomposition

/-! The averaged directed-edge marginal of the concrete recoded star is
the distinguished-port pair law when the original finite window law has
the actual root-neighbor permutation symmetries. -/
noncomputable section
open scoped BigOperators Classical
set_option maxHeartbeats 1000000
namespace GaussianWave.BS.Lower
open GaussianWave.BS GaussianWave.BS.Reused.Entropy GaussianWave.BS.Reused.Entropy.Finite
open GaussianWave.BS.Reused.Graph.ColorProfiles GaussianWave.BS.Reused.Graph.Configuration

theorem edgeMassOfStar_pushMass {A : Type*} [Fintype A] {d q : ℕ}
    (code : A → StarWord d q) (p : A → ℝ) (ab : Fin q × Fin q) :
    edgeMassOfStar (pushMass code p) ab=
      (d : ℝ)⁻¹*∑ j : Fin d,pushMass (fun a => (code a 0,code a j.succ)) p ab := by
  unfold edgeMassOfStar
  rw [sum_pushMass_mul]
  apply congrArg (fun z : ℝ => (d : ℝ)⁻¹*z)
  simp only [wordPortCount,Finset.card_eq_sum_ones,Finset.sum_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [pushMass_as_sum]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [Prod.ext_iff]

def vertexBallRootPermutationIso (d k : ℕ) (σ : Equiv.Perm (Fin d)) :
    vertexBallGraph d k ≃g vertexBallGraph d k where
  toEquiv := rootedBranchAutomorphism (d-1) k σ (fun _ => 1)
  map_rel_iff' := by
    intro v w
    have hc (u : VertexBallVertex d k) : regularTreeRootPermutation d σ (vertexBallEmbedding d k u)=
        vertexBallEmbedding d k (rootedBranchAutomorphism (d-1) k σ (fun _ => 1) u) := by
      cases u with
      | inl t => rfl
      | inr av =>
          change some (σ av.1,(branchPath (d-1) k av.2).reverse)=
            some (σ av.1,(branchPath (d-1) k (branchAutomorphism (d-1) k 1 av.2)).reverse)
          rw [branchAutomorphism_one]
          rfl
    change (regularWordTree d).Adj
      (vertexBallEmbedding d k (rootedBranchAutomorphism (d-1) k σ (fun _ => 1) v))
      (vertexBallEmbedding d k (rootedBranchAutomorphism (d-1) k σ (fun _ => 1) w)) ↔ _
    rw [← hc,← hc]
    exact (regularTreeRootPermutation d σ).map_rel_iff

@[simp] theorem vertexBallRootPermutationIso_root (d k : ℕ) (σ : Equiv.Perm (Fin d)) :
    vertexBallRootPermutationIso d k σ (vertexBallRoot d k)=vertexBallRoot d k := rfl

@[simp] theorem vertexBallRootPermutationIso_neighbor (d k : ℕ) (σ : Equiv.Perm (Fin d)) (a : Fin d) :
    vertexBallRootPermutationIso d k σ (vertexBallNeighbor d k a)=vertexBallNeighbor d k (σ a) := by
  change Sum.inr (σ a,branchAutomorphism (d-1) k 1 (branchRoot (d-1) k))=_
  rw [branchAutomorphism_root]
  rfl

def vertexPathPairCode (d q k : ℕ) (a : Fin d) (w : VertexBallVertex d k → Fin q) :
    Fin (pathNeighborhoodPalette q k) × Fin (pathNeighborhoodPalette q k) :=
  (vertexPathStarCode d q k w 0,vertexPathStarCode d q k w a.succ)

theorem vertexPathPairCode_rootPermutation {d q k : ℕ} (σ : Equiv.Perm (Fin d))
    (a : Fin d) (w : VertexBallVertex d k → Fin q) :
    vertexPathPairCode d q k (σ a) (w ∘ (vertexBallRootPermutationIso d k σ).symm)=
      vertexPathPairCode d q k a w := by
  apply Prod.ext
  · change (Fintype.equivFin (PathNeighborhoodCode (Fin q) k))
      (pathNeighborhoodCode (vertexBallGraph d k) k _ (vertexBallRoot d k))=_
    apply congrArg (Fintype.equivFin (PathNeighborhoodCode (Fin q) k))
    have h := pathNeighborhoodCode_graphIso (vertexBallRootPermutationIso d k σ) k w (vertexBallRoot d k)
    simpa only [vertexBallRootPermutationIso_root] using h
  · change (Fintype.equivFin (PathNeighborhoodCode (Fin q) k))
      (pathNeighborhoodCode (vertexBallGraph d k) k _ (vertexBallNeighbor d k (σ a)))=_
    apply congrArg (Fintype.equivFin (PathNeighborhoodCode (Fin q) k))
    have h := pathNeighborhoodCode_graphIso (vertexBallRootPermutationIso d k σ) k w (vertexBallNeighbor d k a)
    simpa only [vertexBallRootPermutationIso_neighbor] using h

theorem vertexPathPairCode_mass_eq {d q k : ℕ} (hd : 0 < d)
    (p : (VertexBallVertex d k → Fin q) → ℝ)
    (hinv : ∀ (σ : Equiv.Perm (Fin d)) w,p (w ∘ (vertexBallRootPermutationIso d k σ).symm)=p w)
    (a : Fin d) (ab : Fin (pathNeighborhoodPalette q k) × Fin (pathNeighborhoodPalette q k)) :
    pushMass (vertexPathPairCode d q k a) p ab=pushMass (vertexPathPairCode d q k ⟨0,hd⟩) p ab := by
  let σ := Equiv.swap (⟨0,hd⟩ : Fin d) a
  let e := vertexBallRootPermutationIso d k σ
  let S : Equiv.Perm (VertexBallVertex d k → Fin q) :=
    Equiv.arrowCongr e.toEquiv (Equiv.refl (Fin q))
  have hcode (w : VertexBallVertex d k → Fin q) : vertexPathPairCode d q k a (S w)=
      vertexPathPairCode d q k ⟨0,hd⟩ w := by
    have h := vertexPathPairCode_rootPermutation (q := q) (k := k) σ ⟨0,hd⟩ w
    simpa only [σ,Equiv.swap_apply_left] using h
  have hsum := Equiv.sum_comp S (fun w => p w*(if vertexPathPairCode d q k a w=ab then (1 : ℝ) else 0))
  have hp (w : VertexBallVertex d k → Fin q) : p (S w)=p w := hinv σ w
  simp_rw [hp,hcode] at hsum
  rw [pushMass_as_sum,pushMass_as_sum]
  convert hsum.symm using 1 <;> apply Finset.sum_congr rfl <;> intro w hw <;> split_ifs <;> rfl

theorem vertexPathStarCode_edgeMass_eq {d q k : ℕ} (hd : 0 < d)
    (p : (VertexBallVertex d k → Fin q) → ℝ)
    (hinv : ∀ (σ : Equiv.Perm (Fin d)) w,p (w ∘ (vertexBallRootPermutationIso d k σ).symm)=p w) :
    edgeMassOfStar (pushMass (vertexPathStarCode d q k) p)=
      pushMass (vertexPathPairCode d q k ⟨0,hd⟩) p := by
  funext ab
  rw [edgeMassOfStar_pushMass]
  have he (a : Fin d) : pushMass (fun w => (vertexPathStarCode d q k w 0,vertexPathStarCode d q k w a.succ)) p ab=
      pushMass (vertexPathPairCode d q k ⟨0,hd⟩) p ab := vertexPathPairCode_mass_eq hd p hinv a ab
  simp_rw [he]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [← mul_assoc,inv_mul_cancel₀ (by positivity : (d : ℝ) ≠ 0),one_mul]

end GaussianWave.BS.Lower
