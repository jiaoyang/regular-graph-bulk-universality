import GaussianWave.BS.GraphGaussianLocalTests
import GaussianWave.BS.GraphGaussianSmoothingMeanLimit

/-! Literal observations of the uniformly lifted, Gaussian-perturbed graph
marks: measurability, mean convergence and variance are all derived. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical Topology
namespace GaussianWave.BS
open Reused.Graph Lower

def graphGaussianWindowObservation {N m : ℕ} (G : RegularGraph N (m+2))
    (hN : 0 < N) (r : ℕ) (x : ℝ) (b : ℕ) (f : Fin r → Fin N → ℝ) (η : ℝ)
    {J : Type*} (site : J → RegularTreeVertex (m+2))
    (F : BoundedContinuousFunction ((Fin r × J) → ℝ) ℝ)
    (ξ : (Fin r × Fin N) → ℝ) : ℝ :=
  ∫ z,F (fun aj : Fin r × J => z (aj.1,site aj.2))
    ∂uniformLiftedTreeLaw G hN (graphGaussianPerturbedMark G r x b f η ξ)

/-- Measurability is obtained from the actual finite source representation. -/
theorem measurable_graphGaussianWindowObservation {N m : ℕ} (G : RegularGraph N (m+2))
    (hN : 0 < N) (r k : ℕ) (x : ℝ) (b : ℕ) (f : Fin r → Fin N → ℝ) (η : ℝ)
    {J : Type*} [Fintype J] (site : J → RegularTreeVertex (m+2))
    (hsite : ∀ j,regularTreeDepth (site j) ≤ k+1)
    (F : BoundedContinuousFunction ((Fin r × J) → ℝ) ℝ) :
    Measurable (graphGaussianWindowObservation G hN r x b f η site F) := by
  have he : graphGaussianWindowObservation G hN r x b f η site F =
      fun ξ => (N : ℝ)⁻¹*∑ v,graphGaussianRootTest G r k x b f η site F v ξ := by
    funext ξ
    exact integral_uniformLifted_perturbed_window G hN r k x b f η site hsite F ξ
  rw [he]
  exact (Finset.measurable_sum _ (fun v _ => measurable_graphGaussianRootTest G r k x b f η site F v)).const_mul _

/-- Probability averaging preserves the actual test's [0,1] bound. -/
theorem graphGaussianWindowObservation_bounds {N m : ℕ} (G : RegularGraph N (m+2))
    (hN : 0 < N) (r : ℕ) (x : ℝ) (b : ℕ) (f : Fin r → Fin N → ℝ) (η : ℝ)
    {J : Type*} (site : J → RegularTreeVertex (m+2))
    (F : BoundedContinuousFunction ((Fin r × J) → ℝ) ℝ)
    (hF0 : ∀ z,0 ≤ F z) (hF1 : ∀ z,F z ≤ 1) (ξ : (Fin r × Fin N) → ℝ) :
    0 ≤ graphGaussianWindowObservation G hN r x b f η site F ξ ∧
      graphGaussianWindowObservation G hN r x b f η site F ξ ≤ 1 := by
  constructor
  · exact integral_nonneg (fun z => hF0 _)
  · have h := integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun z => hF0 (fun aj : Fin r × J => z (aj.1,site aj.2))))
      (integrable_const (μ := uniformLiftedTreeLaw G hN (graphGaussianPerturbedMark G r x b f η ξ)) (1 : ℝ))
      (Filter.Eventually.of_forall (fun z => hF1 (fun aj : Fin r × J => z (aj.1,site aj.2))))
    simpa only [integral_const,measureReal_univ_eq_one,one_smul] using h

/-- The expected actual observation is the finite source average used in the
proved no-collision mean estimate. -/
theorem integral_graphGaussianWindowObservation {N m : ℕ} (G : RegularGraph N (m+2))
    (hN : 0 < N) (r L : ℕ) (x : ℝ) (b : ℕ) (f : Fin r → Fin N → ℝ) (η : ℝ)
    {J : Type*} [Fintype J] (site : J → RegularTreeVertex (m+2))
    (hsite : ∀ j,regularTreeDepth (site j) ≤ L+1)
    (F : BoundedContinuousFunction ((Fin r × J) → ℝ) ℝ) :
    (∫ ξ,graphGaussianWindowObservation G hN r x b f η site F ξ
      ∂gaussianLabelLaw (Fin r × Fin N)) =
    (Fintype.card (VertexCoverSeed N m L) : ℝ)⁻¹*
      ∑ seed : VertexCoverSeed N m L,
        ∫ ξ,F (fun aj : Fin r × J => graphGaussianPerturbedMark G r x b f η ξ aj.1
          (infiniteVertexGraphCover G L seed (site aj.2))) ∂gaussianLabelLaw (Fin r × Fin N) := by
  let T (seed : VertexCoverSeed N m L) (ξ : (Fin r × Fin N) → ℝ) :=
    F (fun aj : Fin r × J => graphGaussianPerturbedMark G r x b f η ξ aj.1
      (infiniteVertexGraphCover G L seed (site aj.2)))
  have hm (seed : VertexCoverSeed N m L) : Measurable (T seed) := by
    apply F.continuous.measurable.comp
    apply measurable_pi_lambda
    intro aj
    exact measurable_const.add (((measurable_pi_apply _).comp
      (measurable_finiteSupportGaussianSample (jointGraphGaussianCoefficient G r x b))).const_mul η)
  have hi (seed : VertexCoverSeed N m L) : Integrable (T seed) (gaussianLabelLaw (Fin r × Fin N)) :=
    (integrable_const ‖F‖).mono' (hm seed).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun _ => F.norm_coe_le_norm _))
  have he (ξ : (Fin r × Fin N) → ℝ) :
      graphGaussianWindowObservation G hN r x b f η site F ξ =
        (Fintype.card (VertexCoverSeed N m L) : ℝ)⁻¹*∑ seed,T seed ξ := by
    let W := fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ =>
      fun aj : Fin r × J => z (aj.1,site aj.2)
    have hW : Measurable W := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
    rw [graphGaussianWindowObservation,← integral_map hW.aemeasurable F.continuous.aestronglyMeasurable,
      uniformLiftedTreeLaw_window_atomic G hN _ L site hsite,integral_uniformAtomicLaw_boundedTest]
  simp_rw [he]
  rw [integral_const_mul,integral_finset_sum _ (fun seed _ => hi seed)]

/-- Variance of an actual lifted-process observation, not an abstract local
observation supplied with independence or locality conditions. -/
theorem graphGaussianWindowObservation_variance {N m : ℕ} (G : RegularGraph N (m+2))
    (hN : 0 < N) (r k : ℕ) (x : ℝ) (b : ℕ) (f : Fin r → Fin N → ℝ) (η : ℝ)
    {J : Type*} [Fintype J] (site : J → RegularTreeVertex (m+2))
    (hsite : ∀ j,regularTreeDepth (site j) ≤ k+1)
    (F : BoundedContinuousFunction ((Fin r × J) → ℝ) ℝ)
    (hF0 : ∀ z,0 ≤ F z) (hF1 : ∀ z,F z ≤ 1) :
    (∫ ξ,(graphGaussianWindowObservation G hN r x b f η site F ξ-
      ∫ ζ,graphGaussianWindowObservation G hN r x b f η site F ζ
        ∂gaussianLabelLaw (Fin r × Fin N))^2 ∂gaussianLabelLaw (Fin r × Fin N)) ≤
      (regularBallBound (m+2) (2*(k+b+2)) : ℝ)/(N : ℝ) := by
  have he (ξ) := integral_uniformLifted_perturbed_window G hN r k x b f η site hsite F ξ
  simp only [graphGaussianWindowObservation]
  simp_rw [he]
  exact graphGaussianRootTest_average_variance G hN r k k x b f η site hsite F hF0 hF1

/-- At a fixed block radius, expectations of actual lifted smoothed graph
observations converge to independent smoothing of the genuine signal limit. -/
theorem graphGaussianWindowObservation_mean_tendsto
    (N : ℕ → ℕ) (m r k b : ℕ) (G : ∀ n,RegularGraph (N n) (m+2))
    (hN : ∀ n,0 < N n) (f : ∀ n,Fin r → Fin (N n) → ℝ) (x η : ℝ)
    {J : Type*} [Fintype J] (site : J → RegularTreeVertex (m+2))
    (hsite : ∀ j,regularTreeDepth (site j) ≤ k+1)
    (μ : Measure ((Fin r × J) → ℝ)) [IsProbabilityMeasure μ]
    (hweak : WeakLawConverges
      (fun n => Measure.map (fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ =>
        fun aj : Fin r × J => z (aj.1,site aj.2))
        (uniformLiftedTreeLaw (G n) (hN n) (f n))) μ)
    (hbad : Tendsto (fun n => (N n : ℝ)⁻¹*badVertexCoverRootCount (G n) (k+b+1))
      atTop (𝓝 0)) (F : BoundedContinuousFunction ((Fin r × J) → ℝ) ℝ) :
    Tendsto (fun n => ∫ ξ,graphGaussianWindowObservation (G n) (hN n) r x b (f n) η site F ξ
      ∂gaussianLabelLaw (Fin r × Fin (N n))) atTop
      (𝓝 (∫ z,F z ∂independentAddLaw μ (Measure.map
        (fun y : (Fin r × RegularTreeVertex (m+2)) → ℝ =>
          fun aj : Fin r × J => y (aj.1,site aj.2))
        (jointRadialGaussianBlockLaw r (m+2) x b)) η)) := by
  simp_rw [integral_graphGaussianWindowObservation (G _) (hN _) r (k+b+1) x b (f _) η site
    (fun j => (hsite j).trans (by omega)) F]
  exact graphGaussianSmoothing_mean_tendsto N m r k b G hN f x η site hsite μ hweak hbad F

end GaussianWave.BS
