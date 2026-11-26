import GaussianWave.BS.RandomRegularGraphClassification
import GaussianWave.BS.SpectralStarCover
import GaussianWave.BS.SpectralResidualAdapter

/-! The ordinary spectral-data BS interface, proved from actual uniform
simple regular-graph events. Exact and approximate eigenvectors are included.
No Gaussianity, entropy, fourth-moment, or covariance-loss premise remains. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical Topology
namespace GaussianWave.BS

/-- Actual infinite-tree sites for root plus the d ordered neighbors. -/
def spectralStarTreeSite (m : ℕ) (j : Fin (m+2+1)) : RegularTreeVertex (m+2) :=
  vertexBallEmbedding (m+2) 0 (starBallSite m j)

end GaussianWave.BS
namespace GaussianWave.RegularEigenData
open BS BS.Reused.Graph
variable {N m c : ℕ} (D : RegularEigenData (m+2) N c)

/-- The actual spectral star law is an actual lifted-process marginal. -/
theorem starLaw_eq_lifted_star_window {r : ℕ} (q : Fin r → Fin N → ℝ) :
    D.starLaw q = Measure.map (jointTreeWindow (spectralStarTreeSite m))
      (uniformLiftedTreeLaw D.regularGraph D.size_pos (fun a v => Real.sqrt N*q a v)) := by
  have hT : Measurable (fun z : (Fin r × VertexBallVertex (m+2) 0) → ℝ =>
      fun aj : Fin r × Fin (m+2+1) => z (aj.1,starBallSite m aj.2)) :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have hB : Measurable (fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ =>
      fun av : Fin r × VertexBallVertex (m+2) 0 => z (av.1,vertexBallEmbedding (m+2) 0 av.2)) :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  rw [D.starLaw_eq_cover_zero q,← uniformLiftedTreeLaw_ball D.regularGraph D.size_pos
    (fun a v => Real.sqrt N*q a v) 0,Measure.map_map hT hB]
  rfl

end GaussianWave.RegularEigenData
namespace GaussianWave.BS
open Reused.Graph

/-- Arbitrary bounded-L2 matrix approximate eigenvectors satisfy the precise
qualitative BSJointClassification interface on the actual common-good graphs.
The eigenvalues may vary by channel and converge to a common bulk energy. -/
theorem common_graph_signal_BSJointClassification
    (N E : ℕ → ℕ) (m r : ℕ) (hm : 0 < m) (c : ℕ → ℕ)
    (D : ∀ n,RegularEigenData (m+2) (N n) (c n))
    (hNinf : Tendsto N atTop atTop) (hNE : ∀ n,N n*(m+2)=2*E n)
    (C : ℝ) (K : ℕ → ℕ) (hK : Tendsto K atTop atTop)
    (hgood : ∀ᶠ n in atTop,Lower.CommonGraphGood (E := E n) C (K n) (D n).regularGraph)
    (q : ∀ n,Fin r → Fin (N n) → ℝ) (M : Fin r → ℝ)
    (hM : ∀ n a,squareMass (q n a) ≤ M a)
    (energies : ℕ → Fin r → ℝ) (energy : ℝ)
    (henergies : ∀ a,Tendsto (fun n => energies n a) atTop (𝓝 energy))
    (hbulk : |energy|<2*Real.sqrt (m+1))
    (hres : ∀ a,Tendsto (fun n => squareMass
      (eigenResidual (D n).adjacency (energies n a) (q n a))) atTop (𝓝 0)) :
    BSJointClassification (fun n => (D n).starLaw (q n)) := by
  have hb := common_graph_approximate_BSJointClassification N E m r hm
    (fun n => (D n).regularGraph) (fun n => (D n).size_pos) hNinf hNE C K hK hgood
    (fun n a v => Real.sqrt (N n)*q n a v) M
    (fun n a => by rw [(D n).normalized_signal_root_second]; exact hM n a)
    energies energy henergies hbulk
    (fun a => by simpa only [RegularEigenData.normalized_signal_residual_second] using hres a)
    (spectralStarTreeSite m)
  simpa only [← RegularEigenData.starLaw_eq_lifted_star_window] using hb

/-- Exact selected eigenvectors need no auxiliary L2 or residual hypothesis:
both are derived from the literal finite spectral identities. Repeated
channels and arbitrary orthonormal choices inside eigenspaces are allowed. -/
theorem common_graph_eigenvectors_BSJointClassification
    (N E : ℕ → ℕ) (m r : ℕ) (hm : 0 < m) (c : ℕ → ℕ)
    (D : ∀ n,RegularEigenData (m+2) (N n) (c n))
    (hNinf : Tendsto N atTop atTop) (hNE : ∀ n,N n*(m+2)=2*E n)
    (C : ℝ) (K : ℕ → ℕ) (hK : Tendsto K atTop atTop)
    (hgood : ∀ᶠ n in atTop,Lower.CommonGraphGood (E := E n) C (K n) (D n).regularGraph)
    (a : ∀ n,Fin r → Fin (c n)) (energy : ℝ)
    (henergies : ∀ i,Tendsto (fun n => (D n).eigenvalue (a n i)) atTop (𝓝 energy))
    (hbulk : |energy|<2*Real.sqrt (m+1)) :
    BSJointClassification (fun n => (D n).starLaw (fun i => (D n).eigenvector (a n i))) := by
  apply common_graph_signal_BSJointClassification N E m r hm c D hNinf hNE C K hK hgood
    (fun n i => (D n).eigenvector (a n i)) (fun _ => 1)
  · intro n i
    have h := (D n).orthonormal (a n i) (a n i)
    have he : squareMass ((D n).eigenvector (a n i))=1 := by
      simpa only [squareMass,if_pos rfl,pow_two] using h
    exact he.le
  · exact henergies
  · exact hbulk
  · intro i
    simpa only [RegularEigenData.eigenvector_commonEnergy_residual_square,sub_self,zero_pow (by omega : 2 ≠ 0)] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

/-- Direct public approximate-eigenvector endpoint on the actual RRG events. -/
theorem RRGClassificationEvents.signals_BSJointClassification
    {m : ℕ} {N E : ℕ → ℕ} (A : RRGClassificationEvents m N E)
    (hm : 0 < m) (r : ℕ) (c : ℕ → ℕ)
    (D : ∀ n,RegularEigenData (m+2) (N n) (c n))
    (hNinf : Tendsto N atTop atTop) (hNE : ∀ n,N n*(m+2)=2*E n)
    (hgood : ∀ᶠ n in atTop,(D n).regularGraph ∈ A.good n)
    (q : ∀ n,Fin r → Fin (N n) → ℝ) (M : Fin r → ℝ)
    (hM : ∀ n a,squareMass (q n a) ≤ M a)
    (energies : ℕ → Fin r → ℝ) (energy : ℝ)
    (henergies : ∀ a,Tendsto (fun n => energies n a) atTop (𝓝 energy))
    (hbulk : |energy|<2*Real.sqrt (m+1))
    (hres : ∀ a,Tendsto (fun n => squareMass
      (eigenResidual (D n).adjacency (energies n a) (q n a))) atTop (𝓝 0)) :
    BSJointClassification (fun n => (D n).starLaw (q n)) :=
  common_graph_signal_BSJointClassification N E m r hm c D hNinf hNE
    A.entropyConstant A.radius A.radius_tendsto hgood q M hM energies energy henergies hbulk hres

/-- Direct public spectral endpoint on the actual high-probability RRG events. -/
theorem RRGClassificationEvents.eigenvectors_BSJointClassification
    {m : ℕ} {N E : ℕ → ℕ} (A : RRGClassificationEvents m N E)
    (hm : 0 < m) (r : ℕ) (c : ℕ → ℕ)
    (D : ∀ n,RegularEigenData (m+2) (N n) (c n))
    (hNinf : Tendsto N atTop atTop) (hNE : ∀ n,N n*(m+2)=2*E n)
    (hgood : ∀ᶠ n in atTop,(D n).regularGraph ∈ A.good n)
    (a : ∀ n,Fin r → Fin (c n)) (energy : ℝ)
    (henergies : ∀ i,Tendsto (fun n => (D n).eigenvalue (a n i)) atTop (𝓝 energy))
    (hbulk : |energy|<2*Real.sqrt (m+1)) :
    BSJointClassification (fun n => (D n).starLaw (fun i => (D n).eigenvector (a n i))) :=
  common_graph_eigenvectors_BSJointClassification N E m r hm c D hNinf hNE
    A.entropyConstant A.radius A.radius_tendsto hgood a energy henergies hbulk

end GaussianWave.BS
