import GaussianWave.BS.Lower.CommonGraphEvents
import GaussianWave.BS.Lower.PathRecoloringLimit

/-! The fixed-radius path-code lower bound on the genuine simultaneous
random-graph events. No local-tree, entropy, or finite-palette counting
conclusion is assumed separately. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical Topology
namespace GaussianWave.BS.Lower
open GaussianWave.BS GaussianWave.BS.Reused.Graph GaussianWave.BS.Reused.Graph.Configuration
open GaussianWave.BS.Reused.Graph.ColorProfiles
open GaussianWave.BS.Reused.Entropy GaussianWave.BS.Reused.Entropy.Finite

theorem common_graph_path_code_entropy_lower_of_graph_limit {m q r : ℕ} (hq : 0 < q)
    (N E : ℕ → ℕ) (hN : ∀ n,0 < N n) (hNinf : Tendsto N atTop atTop)
    (hNE : ∀ n,N n*(m+2)=2*E n) (G : ∀ n,RegularGraph (N n) (m+2))
    (C : ℝ) (K : ℕ → ℕ) (hK : Tendsto K atTop atTop)
    (hgood : ∀ᶠ n in atTop,CommonGraphGood (E := E n) C (K n) (G n))
    (k : ℕ) (x : ∀ n,Fin (N n) → Fin r → ℝ)
    (ν : Measure ((Fin r × VertexBallVertex (m+2) k) → ℝ))
    (hweak : WeakLawConverges (fun n => finiteVertexCoverLaw (G n) k (fun a v => x n v a)) ν)
    (φ : (Fin r → ℝ) → Fin q → ℝ)
    (hφ0 : ∀ y b,0 ≤ φ y b) (hφ1 : ∀ y,∑ b,φ y b=1)
    (hφc : ∀ b,Continuous (fun y => φ y b)) :
    (∫ y,windowRootEntropyTest φ (vertexBallRoot (m+2) k) y ∂ν) ≤
      entropy (pushMass (vertexPathStarCode (m+2) q k) (windowRecolorMass ν φ))-
      (((m+2 : ℕ) : ℝ)/2)*entropy (edgeMassOfStar
        (pushMass (vertexPathStarCode (m+2) q k) (windowRecolorMass ν φ))) := by
  apply randomized_path_code_entropy_lower_of_graph_limit hq N E hN hNinf hNE G k x
    (C+paletteShift (pathNeighborhoodPalette q k)) (8*(m+2)*(m+2+1))
    (hgood.mono (fun n hn => hn.1 (pathNeighborhoodPalette q k))) ν hweak
    (common_graph_good_bad_fraction_tendsto_zero m N E hNinf G C K hK hgood k) φ hφ0 hφ1 hφc

end GaussianWave.BS.Lower
