import GaussianWave.BS.QualitativeGraphLimits

/-! Actual high-probability events for the uniform labeled simple regular
graph ensemble, with proved qualitative Gaussian classification for all
finite-channel approximate eigenvector selections on those graph events. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical Topology
namespace GaussianWave.BS
open Reused.Graph

/-- These fields describe only actual graph-counting/local-cover events.
No Gaussianity or eigenvector classification is part of the event data. -/
structure RRGClassificationEvents (m : ℕ) (N E : ℕ → ℕ) where
  entropyConstant : ℝ
  entropyConstant_nonneg : 0 ≤ entropyConstant
  radius : ℕ → ℕ
  radius_tendsto : Tendsto radius atTop atTop
  failure_tendsto : Tendsto (fun n => (regularGraphLaw (N n) (m+2)).real
    {G | ¬Lower.CommonGraphGood (E := E n) entropyConstant (radius n) G}) atTop (𝓝 0)

def RRGClassificationEvents.good {m : ℕ} {N E : ℕ → ℕ}
    (A : RRGClassificationEvents m N E) (n : ℕ) : Set (RegularGraph (N n) (m+2)) :=
  {G | Lower.CommonGraphGood (E := E n) A.entropyConstant (A.radius n) G}

/-- The events are constructed from the actual uniform-simple-RRG counting
and local-cycle bounds. There is no probabilistic external theorem input. -/
theorem exists_RRGClassificationEvents (m : ℕ) (N E : ℕ → ℕ)
    (hNinf : Tendsto N atTop atTop) (hgraphs : ∀ n,Nonempty (RegularGraph (N n) (m+2)))
    (hNE : ∀ n,N n*(m+2)=2*E n) : Nonempty (RRGClassificationEvents m N E) := by
  obtain ⟨C,K,hC,hK,hfailure⟩ := Lower.exists_common_graph_good_events m N E hNinf hgraphs hNE
  exact ⟨⟨C,hC,K,hK,hfailure⟩⟩

/-- Literal probability of the constructed good event tends to one. -/
theorem RRGClassificationEvents.good_probability_tendsto_one {m : ℕ} {N E : ℕ → ℕ}
    (A : RRGClassificationEvents m N E) (hgraphs : ∀ n,Nonempty (RegularGraph (N n) (m+2))) :
    Tendsto (fun n => (regularGraphLaw (N n) (m+2)).real (A.good n)) atTop (𝓝 1) := by
  letI (n : ℕ) : Nonempty (RegularGraph (N n) (m+2)) := hgraphs n
  letI (n : ℕ) : IsProbabilityMeasure (regularGraphLaw (N n) (m+2)) := regularGraphLaw_isProbability _ _
  have he (n : ℕ) : (regularGraphLaw (N n) (m+2)).real (A.good n) =
      1-(regularGraphLaw (N n) (m+2)).real
        {G | ¬Lower.CommonGraphGood (E := E n) A.entropyConstant (A.radius n) G} := by
    have hm : MeasurableSet {G : RegularGraph (N n) (m+2) |
        ¬Lower.CommonGraphGood (E := E n) A.entropyConstant (A.radius n) G} := (Set.toFinite _).measurableSet
    have h := measureReal_compl (μ := regularGraphLaw (N n) (m+2)) hm
    simpa only [RRGClassificationEvents.good,Set.compl_setOf,not_not,measureReal_univ_eq_one] using h
  simp_rw [he]
  have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  simpa only [sub_zero] using hc.sub A.failure_tendsto

/-- The qualitative BS conclusion holds for arbitrary selected approximate
common-energy marks on every deterministic sequence eventually in the
constructed high-probability graph events. -/
theorem RRGClassificationEvents.approximate_BSJointClassification
    {m : ℕ} {N E : ℕ → ℕ} (A : RRGClassificationEvents m N E)
    (hm : 0 < m) (r : ℕ) (G : ∀ n,RegularGraph (N n) (m+2)) (hN : ∀ n,0<N n)
    (hNinf : Tendsto N atTop atTop) (hNE : ∀ n,N n*(m+2)=2*E n)
    (hgood : ∀ᶠ n in atTop,G n ∈ A.good n)
    (f : ∀ n,Fin r → Fin (N n) → ℝ) (M : Fin r → ℝ)
    (hM : ∀ n a,(N n : ℝ)⁻¹*∑ v,(f n a v)^2 ≤ M a)
    (energies : ℕ → Fin r → ℝ) (energy : ℝ)
    (henergies : ∀ a,Tendsto (fun n => energies n a) atTop (𝓝 energy))
    (hbulk : |energy|<2*Real.sqrt (m+1))
    (hres : ∀ a,Tendsto (fun n => (N n : ℝ)⁻¹*∑ v,
      (graphEigenResidual (G n) (energies n a) (f n a) v)^2) atTop (𝓝 0))
    {J : Type*} [Fintype J] [DecidableEq J] (site : J → RegularTreeVertex (m+2)) :
    BSJointClassification (fun n => Measure.map (jointTreeWindow site)
      (uniformLiftedTreeLaw (G n) (hN n) (f n))) :=
  common_graph_approximate_BSJointClassification N E m r hm G hN hNinf hNE
    A.entropyConstant A.radius A.radius_tendsto hgood f M hM energies energy henergies hbulk hres site

end GaussianWave.BS
