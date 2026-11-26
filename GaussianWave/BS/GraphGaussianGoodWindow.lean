import GaussianWave.BS.GaussianLabelRestriction
import GaussianWave.BS.Lower.CoverInjectivityEvent

/-! The actual enlarged good-root event implies the exact Gaussian window
law required for local smoothing. No no-collision law is assumed. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GaussianWave.BS
open Reused.Graph Lower

/-- The finite good-root definition implies injectivity of the actual
infinite cover extension throughout the corresponding actual tree ball. -/
theorem infiniteVertexGraphCover_injOn_ball_of_good {N m : ℕ}
    (G : RegularGraph N (m+2)) (k : ℕ) (seed : VertexCoverSeed N m k)
    (hgood : GoodVertexCoverRoot G k seed.1) :
    Set.InjOn (infiniteVertexGraphCover G k seed)
      {v : RegularTreeVertex (m+2) | regularTreeDepth v ≤ k+1} := by
  intro v hv w hw he
  obtain ⟨a,ha⟩ := (vertexBallEmbedding_range (m+2) k ▸ hv :
    v ∈ Set.range (vertexBallEmbedding (m+2) k))
  obtain ⟨b,hb⟩ := (vertexBallEmbedding_range (m+2) k ▸ hw :
    w ∈ Set.range (vertexBallEmbedding (m+2) k))
  rw [← ha,← hb,infiniteVertexGraphCover_restrict,infiniteVertexGraphCover_restrict] at he
  exact ha.symm.trans ((congrArg (vertexBallEmbedding (m+2) k)
    (hgood seed rfl he)).trans hb)

/-- The support used by a window's block rule lies in its literal enlarged
root ball. The radius is derived from the triangle inequality. -/
theorem radialGaussianWindow_support_depth (d : ℕ) (x : ℝ) (b k : ℕ)
    {J : Type*} [Fintype J] (site : J → RegularTreeVertex d)
    (hsite : ∀ j,regularTreeDepth (site j) ≤ k+1) :
    (finiteSupportGaussianUnion (fun j => radialGaussianBlockCoefficient d x b (site j)) :
      Set (RegularTreeVertex d)) ⊆ {v | regularTreeDepth v ≤ (k+b+1)+1} := by
  classical
  intro v hv
  simp only [finiteSupportGaussianUnion,Finset.mem_coe,Finset.mem_biUnion,Finset.mem_univ,true_and] at hv
  obtain ⟨j,hvj⟩ := hv
  have hne := Finsupp.mem_support_iff.mp hvj
  have hdist : (regularWordTree d).dist v (site j) ≤ b+1 := by
    by_contra hn
    apply hne
    simp [radialGaussianBlockCoefficient,regularTreeRadialFinsupp_apply,hn]
  calc
    regularTreeDepth v = (regularWordTree d).dist none v := (regularTree_dist_root d v).symm
    _ ≤ (regularWordTree d).dist none (site j)+(regularWordTree d).dist (site j) v :=
      (regularWordTree_isTree d).isConnected.dist_triangle
    _ ≤ (k+1)+(b+1) := add_le_add (by rw [regularTree_dist_root]; exact hsite j)
      (by rw [SimpleGraph.dist_comm]; exact hdist)
    _ = _ := by omega

/-- A genuine enlarged good root gives exactly the tree Gaussian block
window law for the actual finite-graph sampler. -/
theorem graphRadialGaussianLaw_window_of_good {N m : ℕ}
    (G : RegularGraph N (m+2)) (k b : ℕ)
    (seed : VertexCoverSeed N m (k+b+1)) (x : ℝ)
    {J : Type*} [Fintype J] (site : J → RegularTreeVertex (m+2))
    (hsite : ∀ j,regularTreeDepth (site j) ≤ k+1)
    (hgood : GoodVertexCoverRoot G (k+b+1) seed.1) :
    finiteSupportGaussianLaw (fun j => graphRadialGaussianCoefficient G.val (m+2) x b
      (infiniteVertexGraphCover G (k+b+1) seed (site j))) =
    finiteSupportGaussianLaw (fun j => radialGaussianBlockCoefficient (m+2) x b (site j)) := by
  apply graphRadialGaussianLaw_cover_window
  exact (infiniteVertexGraphCover_injOn_ball_of_good G _ seed hgood).mono
    (radialGaussianWindow_support_depth _ x b k site hsite)

end GaussianWave.BS
