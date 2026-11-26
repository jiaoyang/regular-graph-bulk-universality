import GaussianWave.BS.CommonGraphEigenprocessClassification
import GaussianWave.BS.LiftedProcessLimits
import GaussianWave.StarNormalization

/-! Qualitative BS classification for genuine finite-graph marks. Every weak
subsequential finite-window limit is centered Gaussian, from bounded root L2
and vanishing empirical eigen-residuals on actual common-good graphs. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical Topology
namespace GaussianWave.BS
open Reused.Graph

/-- Every existing finite-window limit of approximate common-energy graph
eigenvectors is centered Gaussian. No fourth-moment bound or covariance
preservation assumption is used. -/
theorem common_graph_approximate_window_limit_gaussian
    (N E : ℕ → ℕ) (m r : ℕ) (hm : 0 < m)
    (G : ∀ n,RegularGraph (N n) (m+2)) (hN : ∀ n,0<N n)
    (hNinf : Tendsto N atTop atTop) (hNE : ∀ n,N n*(m+2)=2*E n)
    (C : ℝ) (K : ℕ → ℕ) (hK : Tendsto K atTop atTop)
    (hgood : ∀ᶠ n in atTop,Lower.CommonGraphGood (E := E n) C (K n) (G n))
    (f : ∀ n,Fin r → Fin (N n) → ℝ) (M : Fin r → ℝ)
    (hM : ∀ n a,(N n : ℝ)⁻¹*∑ v,(f n a v)^2 ≤ M a)
    (energies : ℕ → Fin r → ℝ) (energy : ℝ)
    (henergies : ∀ a,Tendsto (fun n => energies n a) atTop (𝓝 energy))
    (hbulk : |energy|<2*Real.sqrt (m+1))
    (hres : ∀ a,Tendsto (fun n => (N n : ℝ)⁻¹*∑ v,
      (graphEigenResidual (G n) (energies n a) (f n a) v)^2) atTop (𝓝 0))
    {J : Type*} [Fintype J] [DecidableEq J] (site : J → RegularTreeVertex (m+2))
    (ρ : ProbabilityMeasure ((Fin r × J) → ℝ))
    (hρ : WeakLawConverges (fun n => Measure.map (jointTreeWindow site)
      (uniformLiftedTreeLaw (G n) (hN n) (f n))) (ρ : Measure ((Fin r × J) → ℝ))) :
    CenteredGaussianLaw (ρ : Measure ((Fin r × J) → ℝ)) := by
  obtain ⟨P,s,hs,hPweak,hPL2,hPInv,hPE⟩ :=
    uniformLiftedTreeLaw_approximate_eigenprocess_subsequence_of_root_second
      m r N G hN f M hM energies (fun _ => energy) henergies hres
  let laws (n : ℕ) := uniformLiftedTreeProbabilityLaw (G (s n)) (hN (s n)) (f (s n))
  have hballs (k : ℕ) : WeakLawConverges
      (fun n => finiteVertexCoverLaw (G (s n)) k (f (s n))) (Lower.vertexProcessWindow m k (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ))) := by
    have h := process_finiteWindow_weakConverges_of_tendsto laws P hPweak
      (fun av : Fin r × VertexBallVertex (m+2) k => (av.1,vertexBallEmbedding (m+2) k av.2))
    change WeakLawConverges
      (fun n => Measure.map (fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ =>
        fun av : Fin r × VertexBallVertex (m+2) k => z (av.1,vertexBallEmbedding (m+2) k av.2))
        (uniformLiftedTreeLaw (G (s n)) (hN (s n)) (f (s n)))) (Lower.vertexProcessWindow m k (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ))) at h
    simpa only [uniformLiftedTreeLaw_ball] using h
  have htotal (n : ℕ) : graphMarkRootEnergy (f n) ≤ ∑ a,M a := by
    unfold graphMarkRootEnergy
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun a _ => hM n a)
  have hG := common_graph_eigenprocess_finite_gaussian (N ∘ s) (E ∘ s) m r hm
    (fun n => G (s n)) (fun n => hN (s n)) (hNinf.comp hs.tendsto_atTop)
    (fun n => hNE (s n)) C (K ∘ s) (hK.comp hs.tendsto_atTop)
    (hs.tendsto_atTop.eventually hgood) (fun n => f (s n)) (∑ a,M a)
    (fun n => htotal (s n)) P hballs hPInv (fun av => (hPL2 av.1 av.2).1)
    energy hbulk (fun a v => hPE.mono (fun x hx => hx a v)) site
  have hwindow := process_finiteWindow_weakConverges_of_tendsto laws P hPweak
    (fun aj : Fin r × J => (aj.1,site aj.2))
  change WeakLawConverges (fun n => Measure.map (jointTreeWindow site)
    (uniformLiftedTreeLaw (G (s n)) (hN (s n)) (f (s n))))
    (Measure.map (jointTreeWindow site) (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ))) at hwindow
  letI (n : ℕ) : IsProbabilityMeasure (Measure.map (jointTreeWindow site)
      (uniformLiftedTreeLaw (G (s n)) (hN (s n)) (f (s n)))) :=
    isProbabilityMeasure_map (measurable_jointTreeWindow site).aemeasurable
  letI : IsProbabilityMeasure (Measure.map (jointTreeWindow site) (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ))) :=
    isProbabilityMeasure_map (measurable_jointTreeWindow site).aemeasurable
  have hρs : WeakLawConverges (fun n => Measure.map (jointTreeWindow site)
      (uniformLiftedTreeLaw (G (s n)) (hN (s n)) (f (s n)))) (ρ : Measure ((Fin r × J) → ℝ)) :=
    fun F => (hρ F).comp hs.tendsto_atTop
  have heq : Measure.map (jointTreeWindow site) (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ))=(ρ : Measure ((Fin r × J) → ℝ)) := by
    apply measure_eq_of_linear_characteristic
    intro t
    exact tendsto_nhds_unique (weakLaw_characteristic _ _ hwindow t)
      (weakLaw_characteristic _ _ hρs t)
  rw [heq] at hG
  exact hG

/-- The public qualitative BS interface is a proved conclusion for the
actual sampled window laws, uniformly over every good graph subsequence. -/
theorem common_graph_approximate_BSJointClassification
    (N E : ℕ → ℕ) (m r : ℕ) (hm : 0 < m)
    (G : ∀ n,RegularGraph (N n) (m+2)) (hN : ∀ n,0<N n)
    (hNinf : Tendsto N atTop atTop) (hNE : ∀ n,N n*(m+2)=2*E n)
    (C : ℝ) (K : ℕ → ℕ) (hK : Tendsto K atTop atTop)
    (hgood : ∀ᶠ n in atTop,Lower.CommonGraphGood (E := E n) C (K n) (G n))
    (f : ∀ n,Fin r → Fin (N n) → ℝ) (M : Fin r → ℝ)
    (hM : ∀ n a,(N n : ℝ)⁻¹*∑ v,(f n a v)^2 ≤ M a)
    (energies : ℕ → Fin r → ℝ) (energy : ℝ)
    (henergies : ∀ a,Tendsto (fun n => energies n a) atTop (𝓝 energy))
    (hbulk : |energy|<2*Real.sqrt (m+1))
    (hres : ∀ a,Tendsto (fun n => (N n : ℝ)⁻¹*∑ v,
      (graphEigenResidual (G n) (energies n a) (f n a) v)^2) atTop (𝓝 0))
    {J : Type*} [Fintype J] [DecidableEq J] (site : J → RegularTreeVertex (m+2)) :
    BSJointClassification (fun n => Measure.map (jointTreeWindow site)
      (uniformLiftedTreeLaw (G n) (hN n) (f n))) := by
  intro φ hφ ρ hρ
  exact common_graph_approximate_window_limit_gaussian (N ∘ φ) (E ∘ φ) m r hm
    (fun n => G (φ n)) (fun n => hN (φ n)) (hNinf.comp hφ.tendsto_atTop)
    (fun n => hNE (φ n)) C (K ∘ φ) (hK.comp hφ.tendsto_atTop)
    (hφ.tendsto_atTop.eventually hgood) (fun n => f (φ n)) M (fun n a => hM (φ n) a)
    (fun n => energies (φ n)) energy (fun a => (henergies a).comp hφ.tendsto_atTop)
    hbulk (fun a => (hres a).comp hφ.tendsto_atTop) site ρ hρ

end GaussianWave.BS
