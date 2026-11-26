import GaussianWave.BS.Lower.PathCoverComparison
import GaussianWave.BS.Lower.CoverRecoloring

/-! Exact finite sampling identities for actual path-neighborhood recoding.
The graph entropy profiles are pushforwards of the actual recolored cover
law, before the small collision error is estimated. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
set_option maxHeartbeats 1400000
namespace GaussianWave.BS.Lower
open GaussianWave.BS GaussianWave.BS.Reused.Graph GaussianWave.BS.Reused.Graph.Configuration
open GaussianWave.BS.Reused.Graph.ColorProfiles
open GaussianWave.BS.Reused.Entropy GaussianWave.BS.Reused.Entropy.Finite

def vertexBallStarCenter (d k : ℕ) : Fin (d+1) → VertexBallVertex d k :=
  Fin.cases (vertexBallRoot d k) (vertexBallNeighbor d k)

theorem vertexBallStarCenter_depth (d k : ℕ) (j : Fin (d+1)) :
    regularTreeDepth (vertexBallEmbedding d k (vertexBallStarCenter d k j)) ≤ 1 := by
  refine Fin.cases ?_ (fun a => ?_) j
  · simp [vertexBallStarCenter,vertexBallRoot,vertexBallEmbedding,regularTreeDepth]
  · have hr : branchPath (d-1) k (branchRoot (d-1) k)=[] := by cases k <;> rfl
    simp [vertexBallStarCenter,vertexBallNeighbor,vertexBallEmbedding,regularTreeDepth,hr]

def vertexPathStarCode (d q k : ℕ) (w : VertexBallVertex d k → Fin q) :
    StarWord d (pathNeighborhoodPalette q k) :=
  fun j => Fintype.equivFin (PathNeighborhoodCode (Fin q) k)
    (pathNeighborhoodCode (vertexBallGraph d k) k w (vertexBallStarCenter d k j))

theorem vertexPathStarCode_graphCover {N m q : ℕ} (G : RegularGraph N (m+2)) (k : ℕ)
    (seed : VertexCoverSeed N m k) (color : Fin N → Fin q) :
    vertexPathStarCode (m+2) q k (color ∘ vertexGraphCover G k seed)=
      sampledStarWord G (pathNeighborhoodRecoding G k color) (seed.1,seed.2.1.symm) := by
  funext j
  have h (i : Fin (m+2+1)) := congrArg (Fintype.equivFin (PathNeighborhoodCode (Fin q) k))
    (pathNeighborhoodCode_vertexGraphCover G k seed color (vertexBallStarCenter (m+2) k i)
      (vertexBallStarCenter_depth (m+2) k i))
  refine Fin.cases ?_ (fun a => ?_) j
  · change (Fintype.equivFin (PathNeighborhoodCode (Fin q) k))
      (pathNeighborhoodCode (vertexBallGraph (m+2) k) k (color ∘ vertexGraphCover G k seed) (vertexBallRoot (m+2) k))=
      (Fintype.equivFin (PathNeighborhoodCode (Fin q) k)) (pathNeighborhoodCode G.val k color seed.1)
    exact h 0
  · change (Fintype.equivFin (PathNeighborhoodCode (Fin q) k))
      (pathNeighborhoodCode (vertexBallGraph (m+2) k) k (color ∘ vertexGraphCover G k seed) (vertexBallNeighbor (m+2) k a))=
      (Fintype.equivFin (PathNeighborhoodCode (Fin q) k))
        (pathNeighborhoodCode G.val k color (graphNeighbor G seed.1 (seed.2.1 a)))
    simpa only [vertexBallStarCenter,Fin.cases_succ,vertexGraphCover_neighbor] using h a.succ

theorem uniformVertexCoverSeed_rootPort_average {N m : ℕ} (k : ℕ)
    (f : Fin N × Equiv.Perm (Fin (m+2)) → ℝ) :
    (Fintype.card (VertexCoverSeed N m k) : ℝ)⁻¹*
      (∑ seed : VertexCoverSeed N m k,f (seed.1,seed.2.1.symm)) =
      (Fintype.card (Fin N × Equiv.Perm (Fin (m+2))) : ℝ)⁻¹*∑ z,f z := by
  have hinv (v : Fin N) : (∑ π : Equiv.Perm (Fin (m+2)),f (v,π.symm))=
      ∑ π : Equiv.Perm (Fin (m+2)),f (v,π) := by
    simpa only [Equiv.Perm.inv_def] using Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin (m+2)))) (fun π => f (v,π))
  simp only [VertexCoverSeed,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,
    Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  simp_rw [← Finset.mul_sum,hinv]
  have hB : (Fintype.card (Fin (m+2) → BranchCoverOrdering (m+1) k) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  by_cases hN : N=0
  · subst N; simp
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hP : (Fintype.card (Equiv.Perm (Fin (m+2))) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp
  ring

theorem pushMass_actualCoverRecolorMass {N m q : ℕ} {B : Type*} [Fintype B]
    (G : RegularGraph N (m+2)) (k : ℕ)
    (p : Fin N → Fin q → ℝ) (hp : ∀ v b,0 ≤ p v b) (hs : ∀ v,∑ b,p v b=1)
    (code : (VertexBallVertex (m+2) k → Fin q) → B) (b : B) :
    pushMass code (actualCoverRecolorMass G k p hp hs) b=
      (Fintype.card (VertexCoverSeed N m k) : ℝ)⁻¹*
        ∑ seed : VertexCoverSeed N m k,lawMass (independentColoringLaw p hp hs)
          (fun c => code (c ∘ vertexGraphCover G k seed)) b := by
  let P := independentColoringLaw p hp hs
  calc
    _ = (Fintype.card (VertexCoverSeed N m k) : ℝ)⁻¹*
        ∑ seed : VertexCoverSeed N m k,pushMass code
          (lawMass P (fun c => c ∘ vertexGraphCover G k seed)) b := by
      unfold pushMass actualCoverRecolorMass
      rw [← Finset.mul_sum,Finset.sum_comm]
      rfl
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro seed hseed
      rw [finite_pushMass_lawMass P _ (measurable_of_finite _) code]
      rfl

/-- The exact mean graph-star profile of the concrete neighborhood
recoding is the finite pushforward of the actual sampled cover law. -/
theorem mean_pathRecoded_starProfile {N m q : ℕ} (G : RegularGraph N (m+2)) (k : ℕ)
    (p : Fin N → Fin q → ℝ) (hp : ∀ v b,0 ≤ p v b) (hs : ∀ v,∑ b,p v b=1) :
    meanProfile (independentColoringLaw p hp hs)
      (fun c => graphStarProfile G (pathNeighborhoodRecoding G k c))=
      pushMass (vertexPathStarCode (m+2) q k) (actualCoverRecolorMass G k p hp hs) := by
  let P := independentColoringLaw p hp hs
  funext s
  rw [pushMass_actualCoverRecolorMass]
  simp_rw [vertexPathStarCode_graphCover]
  rw [uniformVertexCoverSeed_rootPort_average k
    (fun z => lawMass (independentColoringLaw p hp hs)
      (fun c => sampledStarWord G (pathNeighborhoodRecoding G k c) z) s)]
  rw [mean_graphStarProfile_eq_sample_law G P (pathNeighborhoodRecoding G k) (measurable_of_finite _)]
  rw [lawMass_finiteSampleLaw P _ (uniformSampleWeight_nonneg _) _ (fun _ => measurable_of_finite _) id measurable_id]
  simp only [uniformSampleWeight,← Finset.mul_sum,Function.comp_id,Function.id_comp]
  rfl

end GaussianWave.BS.Lower
