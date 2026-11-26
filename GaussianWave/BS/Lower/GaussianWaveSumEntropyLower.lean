import GaussianWave.BS.GaussianSmoothingClosure
import GaussianWave.BS.Lower.AllRadiusEntropyLower

/-! The all-radius finite-alphabet entropy lower bound for the actual
independent Gaussian-wave sum. Smoothing typicality is proved by graph
realization, then fed directly into the proved common-graph counting theorem. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical Topology
namespace GaussianWave.BS.Lower
open GaussianWave.BS Reused.Graph

theorem common_graph_gaussian_wave_sum_finite_recoloring_entropy_lower
    (N E : ℕ → ℕ) (m r : ℕ) (hm : 0 < m)
    (G : ∀ n,RegularGraph (N n) (m+2)) (hN : ∀ n,0 < N n)
    (hNinf : Tendsto N atTop atTop) (hNE : ∀ n,N n*(m+2)=2*E n)
    (C : ℝ) (K : ℕ → ℕ) (hK : Tendsto K atTop atTop)
    (hgood : ∀ᶠ n in atTop,CommonGraphGood (E := E n) C (K n) (G n))
    (f : ∀ n,Fin r → Fin (N n) → ℝ) (S : ℝ)
    (hS : ∀ n,graphMarkRootEnergy (f n) ≤ S)
    (x : ℝ) (hx : |x|<1)
    (P : ProbabilityMeasure ((Fin r × RegularTreeVertex (m+2)) → ℝ))
    (hweak : ∀ k,WeakLawConverges (fun n => finiteVertexCoverLaw (G n) k (f n))
      (vertexProcessWindow m k (P : Measure _))) :
    let Q := independentTreeSumLaw (P : Measure _)
      (jointGaussianTreeProcessLaw r m (radialEnergy m x))
    ∀ k,HasFiniteRecoloringEntropyLower
      (Measure.map (siteFirstCoordinates r) (vertexProcessWindow m k Q))
      (Measure.map (siteFirstCoordinates r) (edgeProcessWindow m k Q))
      (rootProcessWindow m Q) (((m+2 : ℕ) : ℝ)/2) := by
  dsimp only
  have hbad (k : ℕ) : Tendsto (fun n => (N n : ℝ)⁻¹*badVertexCoverRootCount (G n) k) atTop (𝓝 0) :=
    common_graph_good_bad_fraction_tendsto_zero m N E hNinf G C K hK hgood k
  have hsize : Tendsto (fun n => (N n : ℝ)) atTop atTop :=
    (show Tendsto (fun j : ℕ => (j : ℝ)) atTop atTop from tendsto_natCast_atTop_atTop).comp hNinf
  obtain ⟨n,hn,g,henergy,hconv⟩ := exists_graph_realization_independent_gaussian_wave_sum
    N m r hm G hN hsize f S hS x hx P hweak hbad
  let Q := independentTreeSumLaw (P : Measure _) (jointGaussianTreeProcessLaw r m (radialEnergy m x))
  letI : IsProbabilityMeasure Q := independentTreeSumLaw_probability _ _
  let Qp : ProbabilityMeasure ((Fin r × RegularTreeVertex (m+2)) → ℝ) := ⟨Q,inferInstance⟩
  let laws (j : ℕ) := uniformLiftedTreeProbabilityLaw (G (n j)) (hN (n j)) (g j)
  have hQ : ∀ e : regularWordTree (m+2) ≃g regularWordTree (m+2),
      Measure.map (fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ =>
        fun av : Fin r × RegularTreeVertex (m+2) => z (av.1,e av.2)) Q=Q := by
    intro e
    exact process_invariance_of_tendsto laws Qp hconv _
      (continuous_pi (fun av => continuous_apply (av.1,e av.2)))
      (fun j => uniformLiftedTreeLaw_invariant (G (n j)) (hN (n j)) (g j) e)
  have hw (k : ℕ) : WeakLawConverges
      (fun j => finiteVertexCoverLaw (G (n j)) k (g j)) (vertexProcessWindow m k Q) := by
    have h := process_finiteWindow_weakConverges_of_tendsto laws Qp hconv
      (fun av : Fin r × VertexBallVertex (m+2) k => (av.1,vertexBallEmbedding (m+2) k av.2))
    change WeakLawConverges
      (fun j => Measure.map (fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ =>
          fun av : Fin r × VertexBallVertex (m+2) k => z (av.1,vertexBallEmbedding (m+2) k av.2))
        (uniformLiftedTreeLaw (G (n j)) (hN (n j)) (g j))) (vertexProcessWindow m k Q) at h
    simpa only [uniformLiftedTreeLaw_ball] using h
  exact common_graph_all_radius_finite_recoloring_entropy_lower (N ∘ n) (E ∘ n)
    (fun j => hN (n j)) (hNinf.comp hn.tendsto_atTop) (fun j => hNE (n j))
    (fun j => G (n j)) C (K ∘ n) (hK.comp hn.tendsto_atTop)
    (hn.tendsto_atTop.eventually hgood) (fun j v a => g j a v) Q hQ hw

end GaussianWave.BS.Lower
