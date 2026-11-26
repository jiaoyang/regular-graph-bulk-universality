import GaussianWave.BS.UniformTreeCoverLaw
import GaussianWave.BS.InfiniteCoverSampling

/-! Every finite window of the actual infinite cover coloring is the
literal uniform finite-seed law, at any containing ball radius. -/
noncomputable section
open MeasureTheory
open scoped Classical
namespace GaussianWave.BS
open Reused.Graph

/-- This identity permits enlarging the cover ball for a local Gaussian
rule without changing the signal's actual finite-window law. -/
theorem uniformLiftedTreeLaw_window_atomic {N m r : ℕ}
    (G : RegularGraph N (m+2)) (hN : 0 < N) (f : Fin r → Fin N → ℝ)
    (L : ℕ) {J : Type*} (site : J → RegularTreeVertex (m+2))
    (hsite : ∀ j,regularTreeDepth (site j) ≤ L+1) :
    Measure.map (fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ =>
      fun aj : Fin r × J => z (aj.1,site aj.2)) (uniformLiftedTreeLaw G hN f) =
    uniformAtomicLaw (fun seed : VertexCoverSeed N m L => fun aj : Fin r × J =>
      f aj.1 (infiniteVertexGraphCover G L seed (site aj.2))) := by
  have hex (j : J) : ∃ v : VertexBallVertex (m+2) L,vertexBallEmbedding (m+2) L v=site j := by
    have hmem : site j ∈ Set.range (vertexBallEmbedding (m+2) L) := by
      rw [vertexBallEmbedding_range]
      exact hsite j
    exact hmem
  choose pos hpos using hex
  let B := fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ =>
    fun av : Fin r × VertexBallVertex (m+2) L => z (av.1,vertexBallEmbedding (m+2) L av.2)
  let R := fun z : (Fin r × VertexBallVertex (m+2) L) → ℝ => fun aj : Fin r × J => z (aj.1,pos aj.2)
  have hB : Measurable B := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have hR : Measurable R := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have he : (fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ =>
      fun aj : Fin r × J => z (aj.1,site aj.2)) = R ∘ B := by
    funext z aj
    simp only [Function.comp_apply,R,B,hpos]
  rw [he,← Measure.map_map hR hB,uniformLiftedTreeLaw_ball]
  change Measure.map R (uniformAtomicLaw
    (fun seed : VertexCoverSeed N m L => fun av : Fin r × VertexBallVertex (m+2) L =>
      f av.1 (vertexGraphCover G L seed av.2))) = _
  rw [uniformAtomicLaw_map _ R hR]
  congr 1
  funext seed aj
  dsimp only [Function.comp_apply,R]
  rw [← infiniteVertexGraphCover_restrict,hpos]

end GaussianWave.BS
