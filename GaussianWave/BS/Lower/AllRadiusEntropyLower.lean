import GaussianWave.BS.Lower.CommonGraphPathLower
import GaussianWave.BS.Lower.MarkerCodeToEntropy
import GaussianWave.BS.Lower.ProcessFixedEdge

/-! The actual all-radius randomized finite-recoloring entropy lower bound
from common good regular graphs and genuine marked-cover weak limits.
Every counting, locality, coding, symmetry, marker and finite-alphabet
transport step is proved upstream. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical Topology
set_option maxHeartbeats 1600000
namespace GaussianWave.BS.Lower
open GaussianWave.BS GaussianWave.BS.Reused.Graph GaussianWave.BS.Reused.Graph.Configuration
open GaussianWave.BS.Reused.Entropy GaussianWave.BS.Reused.Entropy.Finite

/-- Source Theorem 6.1 at one arbitrary radius, for genuine vector-valued
process marks. The source process invariance and weak convergence are
ordinary probability-law hypotheses, with no entropy conclusion assumed. -/
theorem common_graph_finite_recoloring_entropy_lower {m r : ℕ}
    (N E : ℕ → ℕ) (hN : ∀ n,0 < N n) (hNinf : Tendsto N atTop atTop)
    (hNE : ∀ n,N n*(m+2)=2*E n) (G : ∀ n,RegularGraph (N n) (m+2))
    (C : ℝ) (K : ℕ → ℕ) (hK : Tendsto K atTop atTop)
    (hgood : ∀ᶠ n in atTop,CommonGraphGood (E := E n) C (K n) (G n))
    (x : ∀ n,Fin (N n) → Fin r → ℝ)
    (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) [IsProbabilityMeasure P]
    (hP : ∀ e : regularWordTree (m+2) ≃g regularWordTree (m+2),
      Measure.map (fun z av => z (av.1,e av.2)) P=P)
    (k : ℕ)
    (hweak : WeakLawConverges (fun n => finiteVertexCoverLaw (G n) k (fun a v => x n v a))
      (vertexProcessWindow m k P)) :
    HasFiniteRecoloringEntropyLower
      (Measure.map (siteFirstCoordinates r) (vertexProcessWindow m k P))
      (Measure.map (siteFirstCoordinates r) (edgeProcessWindow m k P))
      (rootProcessWindow m P) (((m+2 : ℕ) : ℝ)/2) := by
  apply hasFiniteRecoloringEntropyLower_of_fin
  intro q hq φ hφc hφ0 hφ1
  have hCmass : recolorMass (Measure.map (siteFirstCoordinates r) (vertexProcessWindow m k P)) φ=
      windowRecolorMass (vertexProcessWindow m k P) φ := by
    funext b
    exact (windowRecolorMass_eq_siteFirst _ φ (fun b => (hφc b).measurable) b).symm
  have hEmass : recolorMass (Measure.map (siteFirstCoordinates r) (edgeProcessWindow m k P)) φ=
      windowRecolorMass (edgeProcessWindow m k P) φ := by
    funext b
    exact (windowRecolorMass_eq_siteFirst _ φ (fun b => (hφc b).measurable) b).symm
  rw [hCmass,hEmass]
  apply marker_code_lower_to_entropy m k hq P hP _ φ hφc hφ0 hφ1
  intro Q hQ θ hθc hθ0 hθ1
  have hraw := common_graph_path_code_entropy_lower_of_graph_limit hQ N E hN hNinf hNE G C K hK hgood
    k x (vertexProcessWindow m k P) hweak θ hθ0 hθ1 hθc
  rw [process_code_edge_entropy m k P hP θ hθ0 hθ1 hθc] at hraw
  rw [entropy_vertexPathStarCode] at hraw
  rw [← process_root_entropy_eq_vertex m k P θ hθc] at hraw
  simpa only [entropy,pushMass_as_sum,← tsum_fintype] using hraw

/-- One common graph sequence works for every finite radius and every
continuous finite probability kernel simultaneously. -/
theorem common_graph_all_radius_finite_recoloring_entropy_lower {m r : ℕ}
    (N E : ℕ → ℕ) (hN : ∀ n,0 < N n) (hNinf : Tendsto N atTop atTop)
    (hNE : ∀ n,N n*(m+2)=2*E n) (G : ∀ n,RegularGraph (N n) (m+2))
    (C : ℝ) (K : ℕ → ℕ) (hK : Tendsto K atTop atTop)
    (hgood : ∀ᶠ n in atTop,CommonGraphGood (E := E n) C (K n) (G n))
    (x : ∀ n,Fin (N n) → Fin r → ℝ)
    (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) [IsProbabilityMeasure P]
    (hP : ∀ e : regularWordTree (m+2) ≃g regularWordTree (m+2),
      Measure.map (fun z av => z (av.1,e av.2)) P=P)
    (hweak : ∀ k : ℕ,WeakLawConverges (fun n => finiteVertexCoverLaw (G n) k (fun a v => x n v a))
      (vertexProcessWindow m k P)) :
    ∀ k : ℕ,HasFiniteRecoloringEntropyLower
      (Measure.map (siteFirstCoordinates r) (vertexProcessWindow m k P))
      (Measure.map (siteFirstCoordinates r) (edgeProcessWindow m k P))
      (rootProcessWindow m P) (((m+2 : ℕ) : ℝ)/2) :=
  fun k => common_graph_finite_recoloring_entropy_lower N E hN hNinf hNE G C K hK hgood x P hP k (hweak k)

end GaussianWave.BS.Lower
