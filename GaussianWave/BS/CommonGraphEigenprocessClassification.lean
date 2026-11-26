import GaussianWave.BS.SmoothEigenprocessClassification
import GaussianWave.BS.ProcessSmoothingEntropy
import GaussianWave.BS.GaussianSumCancellation
import GaussianWave.BS.Lower.GaussianWaveSumEntropyLower
import GaussianWave.BS.Lower.RecoloringProcessTransport

/-!
# Qualitative joint Gaussianity from actual common-good regular graphs

All entropy, smoothing, gluing and Gaussianity inputs are discharged. The
source assumptions concern only actual graph marks, their genuine local
weak limit, finite second moments and the common-energy eigen-equations.
Original covariance may lose rank or variance, and zero channels are allowed.
-/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical Topology
namespace GaussianWave.BS
open Reused.Graph

theorem common_graph_whitened_eigenprocess_classification
    (N E : ℕ → ℕ) (m r : ℕ) (hm : 0 < m)
    (G : ∀ n,RegularGraph (N n) (m+2)) (hN : ∀ n,0<N n)
    (hNinf : Tendsto N atTop atTop) (hNE : ∀ n,N n*(m+2)=2*E n)
    (C : ℝ) (K : ℕ → ℕ) (hK : Tendsto K atTop atTop)
    (hgood : ∀ᶠ n in atTop,Lower.CommonGraphGood (E := E n) C (K n) (G n))
    (f : ∀ n,Fin r → Fin (N n) → ℝ) (S : ℝ)
    (hS : ∀ n,graphMarkRootEnergy (f n) ≤ S)
    (P : ProbabilityMeasure ((Fin r × RegularTreeVertex (m+2)) → ℝ))
    (hweak : ∀ k,WeakLawConverges (fun n => finiteVertexCoverLaw (G n) k (f n))
      (Lower.vertexProcessWindow m k (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ))))
    (hP : ChannelTreeInvariant (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)))
    (hi : ∀ av : Fin r × RegularTreeVertex (m+2),
      Integrable (fun x : (Fin r × RegularTreeVertex (m+2)) → ℝ => x av^2) (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)))
    (energy : ℝ) (hbulk : |energy|<2*Real.sqrt (m+1))
    (hE : ∀ a v,∀ᵐ x ∂(P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)),treeEigenResidual (m+2) r (fun _ => energy) a v x=0) :
    whitenedGaussianSumLaw (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) hi energy=jointGaussianTreeProcessLaw r m energy := by
  let he := abs_energy_lt_degree_of_strict_bulk m energy hbulk
  let x := energy/(2*Real.sqrt (m+1))
  have hden : (0 : ℝ)<2*Real.sqrt (m+1) := by positivity
  have hx : |x|<1 := by
    rw [show x=energy/(2*Real.sqrt (m+1)) from rfl,abs_div,abs_of_pos hden]
    exact (div_lt_one hden).2 hbulk
  have hradial : radialEnergy m x=energy := by
    unfold radialEnergy x
    exact mul_div_cancel₀ energy hden.ne'
  let Q := independentTreeSumLaw (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) (jointGaussianTreeProcessLaw r m energy)
  let B := positiveRootWhitening (treeRootCovariance (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ))) (treeRootCovariance_posSemidef (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) hi)
  have hfiniteQ := Lower.common_graph_gaussian_wave_sum_finite_recoloring_entropy_lower
    N E m r hm G hN hNinf hNE C K hK hgood f S hS x hx P hweak
  rw [hradial] at hfiniteQ
  have hfinite (k : ℕ) : Lower.HasFiniteRecoloringEntropyLower
      (vertexSiteFirstProcessLaw (whitenedGaussianSumLaw (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) hi energy) k)
      (edgeSiteFirstProcessLaw (whitenedGaussianSumLaw (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) hi energy) k)
      (Lower.rootProcessWindow m (whitenedGaussianSumLaw (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) hi energy)) ((m+2 : ℝ)/2) := by
    have h := Lower.finite_recoloring_entropy_lower_channelProcessMap Q k
      (((m+2 : ℕ) : ℝ)/2) (hfiniteQ k) B
    simpa only [Nat.cast_add,Nat.cast_ofNat] using h
  exact smooth_normalized_eigenprocess_eq_jointGaussian hm
    (whitenedGaussianSumLaw (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) hi energy)
    (whitenedGaussianSumLaw_invariant (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) hi energy he hP)
    (whitenedGaussianSumLaw_integrable_square (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) hi energy he) energy hbulk
    (whitenedGaussianSumLaw_eigenrelations (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) hi energy he hE)
    (whitenedGaussianSumLaw_root_identitySecondMoments (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) hi energy he)
    hfinite (whitenedGaussianSumVertexInnovationDensity (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) hi energy he)
    (whitenedGaussianSumEdgeInnovationDensity (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) hi energy he)
    (whitenedGaussianSumVertexInnovationDensity_law (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) hi energy he)
    (whitenedGaussianSumEdgeInnovationDensity_law (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) hi energy he)

theorem common_graph_eigenprocess_finite_gaussian
    (N E : ℕ → ℕ) (m r : ℕ) (hm : 0 < m)
    (G : ∀ n,RegularGraph (N n) (m+2)) (hN : ∀ n,0<N n)
    (hNinf : Tendsto N atTop atTop) (hNE : ∀ n,N n*(m+2)=2*E n)
    (C : ℝ) (K : ℕ → ℕ) (hK : Tendsto K atTop atTop)
    (hgood : ∀ᶠ n in atTop,Lower.CommonGraphGood (E := E n) C (K n) (G n))
    (f : ∀ n,Fin r → Fin (N n) → ℝ) (S : ℝ)
    (hS : ∀ n,graphMarkRootEnergy (f n) ≤ S)
    (P : ProbabilityMeasure ((Fin r × RegularTreeVertex (m+2)) → ℝ))
    (hweak : ∀ k,WeakLawConverges (fun n => finiteVertexCoverLaw (G n) k (f n))
      (Lower.vertexProcessWindow m k (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ))))
    (hP : ChannelTreeInvariant (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)))
    (hi : ∀ av : Fin r × RegularTreeVertex (m+2),
      Integrable (fun x : (Fin r × RegularTreeVertex (m+2)) → ℝ => x av^2) (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)))
    (energy : ℝ) (hbulk : |energy|<2*Real.sqrt (m+1))
    (hE : ∀ a v,∀ᵐ x ∂(P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)),treeEigenResidual (m+2) r (fun _ => energy) a v x=0)
    {J : Type*} [Fintype J] [DecidableEq J] (site : J → RegularTreeVertex (m+2)) :
    CenteredGaussianLaw (Measure.map (jointTreeWindow site) (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ))) := by
  exact finiteGaussian_of_classified_whitened_sum (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) hi energy
    (abs_energy_lt_degree_of_strict_bulk m energy hbulk)
    (common_graph_whitened_eigenprocess_classification N E m r hm G hN hNinf hNE
      C K hK hgood f S hS P hweak hP hi energy hbulk hE) site

end GaussianWave.BS
