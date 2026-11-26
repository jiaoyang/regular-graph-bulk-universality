import GeneralizedBulk.Graph.UniformSwitching
import GaussianWave.BulkInput
import GaussianWave.BS.SpectralBSClassification

/-! The proved random-graph classification supplies a common qualitative BS
event for arbitrary orthonormal eigenfamilies on each actual finite graph. -/
noncomputable section
open MeasureTheory Filter
open scoped Classical BigOperators Topology

namespace GeneralizedBulk.Graph

/-- The full candidate family of actual orthonormal eigenfamilies on one graph.
No measurability or countability restriction is placed on this family. -/
def GraphEigenCandidate (d M k : ℕ) (g : RegularGraph M d) :=
  {A : GaussianWave.RegularEigenData d M k // A.adjacency=g.val.adjMatrix ℝ}

namespace GraphEigenCandidate
variable {d M k : ℕ} {g : RegularGraph M d}

theorem regularGraph_eq (s : GraphEigenCandidate d M k g) : s.val.regularGraph=g := by
  apply Subtype.ext
  apply SimpleGraph.ext
  funext v w
  apply propext
  change s.val.adjacency v w=1 ↔ g.val.Adj v w
  rw [s.property]
  by_cases h : g.val.Adj v w <;> simp [SimpleGraph.adjMatrix_apply,h]

end GraphEigenCandidate

private theorem graph_handshake {M d : ℕ} (g : RegularGraph M d) : M*d=2*(M*d/2) := by
  have h := g.val.sum_degrees_eq_twice_card_edges
  simp only [g.property.degree_eq,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at h
  have he : M*d=2*g.val.edgeFinset.card := by simpa using h
  rw [he]
  omega

private theorem exists_uniformCandidateBS_shifted (m k : ℕ) (hm : 0 < m)
    (N : ℕ → ℕ) (hNinf : Tendsto N atTop atTop)
    (hgraphs : ∀ n,Nonempty (RegularGraph (N n) (m+2)))
    (K : Set ℝ) (hbulk : ∀ x∈K,|x|<2*Real.sqrt (m+1 : ℝ)) (δ : ℕ → ℝ) :
    ∃ good : ∀ n,Set (RegularGraph (N n) (m+2)),
      (∀ n,MeasurableSet (good n)) ∧
      Tendsto (fun n => (regularGraphLaw (N n) (m+2) (good n)ᶜ).toReal) atTop (𝓝 0) ∧
      GaussianWave.UniformBSOn
        (fun n g (s : GraphEigenCandidate (m+2) (N n) k g) => s.val) K δ good := by
  let E := fun n => N n*(m+2)/2
  have hNE : ∀ n,N n*(m+2)=2*E n := fun n => graph_handshake (Classical.choice (hgraphs n))
  have hgraphs' : ∀ n,Nonempty (GaussianWave.BS.Reused.Graph.RegularGraph (N n) (m+2)) := hgraphs
  let A := Classical.choice (GaussianWave.BS.exists_RRGClassificationEvents m N E hNinf hgraphs' hNE)
  let good : ∀ n,Set (RegularGraph (N n) (m+2)) := fun n => A.good n
  refine ⟨good,(fun n => (Set.to_countable _).measurableSet),?_,?_⟩
  · simpa only [good,GaussianWave.BS.RRGClassificationEvents.good,Set.compl_setOf]
      using A.failure_tendsto
  · intro r hr g s hg hadm energy henergyK henergies
    have hgood : ∀ᶠ j in atTop,
        GaussianWave.BS.Lower.CommonGraphGood (E := E (r j)) A.entropyConstant
          (A.radius (r j)) (s j).val.regularGraph := by
      apply Eventually.of_forall
      intro j
      rw [GraphEigenCandidate.regularGraph_eq]
      exact hg j
    have hresult := GaussianWave.BS.common_graph_eigenvectors_BSJointClassification
      (N ∘ r) (E ∘ r) m k hm (fun _ => k) (fun j => (s j).val)
      (hNinf.comp hr.tendsto_atTop) (fun j => hNE (r j))
      A.entropyConstant (A.radius ∘ r) (A.radius_tendsto.comp hr.tendsto_atTop)
      hgood (fun _ => id) energy henergies (hbulk energy henergyK)
    exact hresult

/-- Actual common-good graphs for the entire candidate family. The conclusion
uses the established UniformBSOn interface without a Gaussianity premise. -/
theorem exists_uniformCandidateBS (d k : ℕ) (hd : 3 ≤ d)
    (N : ℕ → ℕ) (hNinf : Tendsto N atTop atTop)
    (hgraphs : ∀ n,Nonempty (RegularGraph (N n) d))
    (K : Set ℝ) (hbulk : ∀ x∈K,|x|<2*Real.sqrt ((d : ℝ)-1)) (δ : ℕ → ℝ) :
    ∃ good : ∀ n,Set (RegularGraph (N n) d),
      (∀ n,MeasurableSet (good n)) ∧
      Tendsto (fun n => (regularGraphLaw (N n) d (good n)ᶜ).toReal) atTop (𝓝 0) ∧
      GaussianWave.UniformBSOn
        (fun n g (s : GraphEigenCandidate d (N n) k g) => s.val) K δ good := by
  cases d with
  | zero => omega
  | succ d =>
    cases d with
    | zero => omega
    | succ m =>
      apply exists_uniformCandidateBS_shifted m k (by omega) N hNinf hgraphs K
      intro x hx
      convert hbulk x hx using 1 <;> norm_num <;> ring

end GeneralizedBulk.Graph
