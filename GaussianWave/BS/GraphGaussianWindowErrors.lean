import GaussianWave.BS.GraphGaussianWindowObservations
import GaussianWave.BS.BoundedObservationErrors

/-! Genuine mean-square accuracy of bounded observations of the actual
Gaussian-perturbed graph-cover laws at every fixed local block rule. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical Topology
namespace GaussianWave.BS
open Reused.Graph Lower

theorem graphGaussianWindowObservation_second_error_tendsto
    (N : ℕ → ℕ) (m r k b : ℕ) (G : ∀ n,RegularGraph (N n) (m+2))
    (hN : ∀ n,0 < N n) (hsize : Tendsto (fun n => (N n : ℝ)) atTop atTop)
    (f : ∀ n,Fin r → Fin (N n) → ℝ) (x η : ℝ)
    {J : Type*} [Fintype J] (site : J → RegularTreeVertex (m+2))
    (hsite : ∀ j,regularTreeDepth (site j) ≤ k+1)
    (μ : Measure ((Fin r × J) → ℝ)) [IsProbabilityMeasure μ]
    (hweak : WeakLawConverges
      (fun n => Measure.map (fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ =>
        fun aj : Fin r × J => z (aj.1,site aj.2))
        (uniformLiftedTreeLaw (G n) (hN n) (f n))) μ)
    (hbad : Tendsto (fun n => (N n : ℝ)⁻¹*badVertexCoverRootCount (G n) (k+b+1))
      atTop (𝓝 0)) (F : BoundedContinuousFunction ((Fin r × J) → ℝ) ℝ)
    (hF0 : ∀ z,0 ≤ F z) (hF1 : ∀ z,F z ≤ 1) :
    let c := ∫ z,F z ∂independentAddLaw μ (Measure.map
      (fun y : (Fin r × RegularTreeVertex (m+2)) → ℝ =>
        fun aj : Fin r × J => y (aj.1,site aj.2))
      (jointRadialGaussianBlockLaw r (m+2) x b)) η
    (∀ n,Integrable (fun ξ =>
      (graphGaussianWindowObservation (G n) (hN n) r x b (f n) η site F ξ-c)^2)
      (gaussianLabelLaw (Fin r × Fin (N n)))) ∧
    Tendsto (fun n => ∫ ξ,
      (graphGaussianWindowObservation (G n) (hN n) r x b (f n) η site F ξ-c)^2
      ∂gaussianLabelLaw (Fin r × Fin (N n))) atTop (𝓝 0) := by
  dsimp only
  apply boundedObservation_second_error_tendsto
    (fun n => (Fin r × Fin (N n)) → ℝ)
    (fun n => gaussianLabelLaw (Fin r × Fin (N n)))
    (fun n => graphGaussianWindowObservation (G n) (hN n) r x b (f n) η site F)
    (fun n => measurable_graphGaussianWindowObservation (G n) (hN n) r k x b (f n) η site hsite F)
    (fun n ξ => graphGaussianWindowObservation_bounds (G n) (hN n) r x b (f n) η site F hF0 hF1 ξ)
    _ (graphGaussianWindowObservation_mean_tendsto N m r k b G hN f x η site hsite μ hweak hbad F)
    (fun n => (regularBallBound (m+2) (2*(k+b+2)) : ℝ)/(N n : ℝ))
    (fun n => graphGaussianWindowObservation_variance (G n) (hN n) r k x b (f n) η site hsite F hF0 hF1)
  exact hsize.const_div_atTop _

end GaussianWave.BS
