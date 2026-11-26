import GaussianWave.BS.JointGraphGaussianWindowMean

/-! Fixed-block smoothing of genuine graph-limit signals: expected actual
finite-cover observations converge to the literal independent sum law. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical Topology
namespace GaussianWave.BS
open Reused.Graph Lower

theorem graphGaussianSmoothing_mean_tendsto
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
    Tendsto (fun n => (Fintype.card (VertexCoverSeed (N n) m (k+b+1)) : ℝ)⁻¹*
      ∑ seed : VertexCoverSeed (N n) m (k+b+1),
        ∫ ξ,F ((fun aj : Fin r × J => f n aj.1
          (infiniteVertexGraphCover (G n) (k+b+1) seed (site aj.2)))+
          η • (fun aj : Fin r × J => finiteSupportGaussianSample
            (jointGraphGaussianCoefficient (G n) r x b) ξ
            (aj.1,infiniteVertexGraphCover (G n) (k+b+1) seed (site aj.2))))
          ∂gaussianLabelLaw (Fin r × Fin (N n))) atTop
      (𝓝 (∫ z,F z ∂independentAddLaw μ (Measure.map
        (fun y : (Fin r × RegularTreeVertex (m+2)) → ℝ =>
          fun aj : Fin r × J => y (aj.1,site aj.2))
        (jointRadialGaussianBlockLaw r (m+2) x b)) η)) := by
  let W := fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ =>
    fun aj : Fin r × J => z (aj.1,site aj.2)
  have hW : Measurable W := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  let P (n : ℕ) := Measure.map W (uniformLiftedTreeLaw (G n) (hN n) (f n))
  letI (n : ℕ) : IsProbabilityMeasure (P n) := isProbabilityMeasure_map hW.aemeasurable
  let L := Measure.map W (jointRadialGaussianBlockLaw r (m+2) x b)
  letI : IsProbabilityMeasure L := isProbabilityMeasure_map hW.aemeasurable
  let signal (n : ℕ) (seed : VertexCoverSeed (N n) m (k+b+1)) (aj : Fin r × J) :=
    f n aj.1 (infiniteVertexGraphCover (G n) (k+b+1) seed (site aj.2))
  let A (n : ℕ) := (Fintype.card (VertexCoverSeed (N n) m (k+b+1)) : ℝ)⁻¹*
    ∑ seed : VertexCoverSeed (N n) m (k+b+1),
      ∫ ξ,F (signal n seed+η • (fun aj : Fin r × J => finiteSupportGaussianSample
        (jointGraphGaussianCoefficient (G n) r x b) ξ
        (aj.1,infiniteVertexGraphCover (G n) (k+b+1) seed (site aj.2))))
        ∂gaussianLabelLaw (Fin r × Fin (N n))
  let B (n : ℕ) := ∫ z,F z ∂independentAddLaw (P n) L η
  have herror (n : ℕ) : |A n-B n| ≤
      2*‖F‖*((N n : ℝ)⁻¹*badVertexCoverRootCount (G n) (k+b+1)) := by
    have hw := uniformLiftedTreeLaw_window_atomic (G n) (hN n) (f n) (k+b+1) site
      (fun j => (hsite j).trans (by omega))
    have he := jointGraphGaussianWindow_mean_error (G n) (hN n) r k b x η site hsite (signal n) F
    rw [← hw] at he
    exact he
  have hdiff : Tendsto (fun n => A n-B n) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => by simpa only [Real.norm_eq_abs] using herror n)
    simpa only [mul_zero] using hbad.const_mul (2*‖F‖)
  have ht : Tendsto B atTop (𝓝 (∫ z,F z ∂independentAddLaw μ L η)) :=
    independentAddLaw_weakConverges_left P μ L η hweak F
  change Tendsto A atTop (𝓝 (∫ z,F z ∂independentAddLaw μ L η))
  simpa only [sub_add_cancel,zero_add] using hdiff.add ht

end GaussianWave.BS
