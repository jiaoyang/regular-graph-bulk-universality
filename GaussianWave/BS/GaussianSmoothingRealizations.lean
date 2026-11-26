import GaussianWave.BS.GraphGaussianWindowErrors
import GaussianWave.BS.GraphGaussianPerturbedEnergy
import GaussianWave.BS.DiagonalSampleSelection
import GaussianWave.BS.GaussianSmoothingApproximation

/-! Actual graph realizations of independent Gaussian-wave smoothing,
simultaneously for any prescribed countable family of bounded finite-window
tests. Neither smoothed typicality nor a smoothed entropy inequality is an
input. The construction uses actual iid graph labels and a strict diagonal. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical Topology
namespace GaussianWave.BS
open Reused.Graph Lower

theorem exists_graphGaussian_smoothing_test_realizations
    (N : ℕ → ℕ) (m r : ℕ) (hm : 0 < m)
    (G : ∀ n,RegularGraph (N n) (m+2)) (hN : ∀ n,0 < N n)
    (hsize : Tendsto (fun n => (N n : ℝ)) atTop atTop)
    (f : ∀ n,Fin r → Fin (N n) → ℝ) (S : ℝ)
    (hS : ∀ n,graphMarkRootEnergy (f n) ≤ S)
    (x : ℝ) (hx : |x|<1) (η : ℝ)
    (μ : ∀ k,ProbabilityMeasure ((Fin r × VertexBallVertex (m+2) k) → ℝ))
    (hweak : ∀ k,WeakLawConverges (fun n => finiteVertexCoverLaw (G n) k (f n)) (μ k : Measure _))
    (hbad : ∀ k,Tendsto (fun n => (N n : ℝ)⁻¹*badVertexCoverRootCount (G n) k) atTop (𝓝 0))
    (k : ℕ → ℕ)
    (F : ∀ i,BoundedContinuousFunction ((Fin r × VertexBallVertex (m+2) (k i)) → ℝ) ℝ)
    (hF0 : ∀ i z,0 ≤ F i z) (hF1 : ∀ i z,F i z ≤ 1) :
    ∃ (n : ℕ → ℕ),StrictMono n ∧
      ∃ (g : ∀ b,Fin r → Fin (N (n b)) → ℝ),
      (∀ b,graphMarkRootEnergy (g b)<4*S+4*η^2*(r : ℝ)+3) ∧
      ∀ i,Tendsto (fun b => ∫ z,F i z ∂finiteVertexCoverLaw (G (n b)) (k i) (g b)) atTop
        (𝓝 (∫ z,F i z ∂independentAddLaw (μ (k i) : Measure _) (Measure.map
          (fun y : (Fin r × RegularTreeVertex (m+2)) → ℝ =>
            fun aj : Fin r × VertexBallVertex (m+2) (k i) =>
              y (aj.1,vertexBallEmbedding (m+2) (k i) aj.2))
          (jointGaussianTreeProcessLaw r m (radialEnergy m x))) η)) := by
  let site (i : ℕ) := vertexBallEmbedding (m+2) (k i)
  let Ω (n : ℕ) := (Fin r × Fin (N n)) → ℝ
  let P (n : ℕ) := gaussianLabelLaw (Fin r × Fin (N n))
  let X (b n i : ℕ) : Ω n → ℝ :=
    graphGaussianWindowObservation (G n) (hN n) r x b (f n) η (site i) (F i)
  let target (b i : ℕ) := ∫ z,F i z ∂independentAddLaw (μ (k i) : Measure _)
    (Measure.map (fun y : (Fin r × RegularTreeVertex (m+2)) → ℝ =>
      fun aj : Fin r × VertexBallVertex (m+2) (k i) => y (aj.1,site i aj.2))
      (jointRadialGaussianBlockLaw r (m+2) x b)) η
  let H (b n : ℕ) (ξ : Ω n) := graphMarkRootEnergy (graphGaussianPerturbedMark (G n) r x b (f n) η ξ)
  have hsignal (i : ℕ) : WeakLawConverges
      (fun n => Measure.map (fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ =>
        fun aj : Fin r × VertexBallVertex (m+2) (k i) => z (aj.1,site i aj.2))
        (uniformLiftedTreeLaw (G n) (hN n) (f n))) (μ (k i) : Measure _) := by
    simp only [site,uniformLiftedTreeLaw_ball]
    exact hweak (k i)
  have herr (b i : ℕ) := graphGaussianWindowObservation_second_error_tendsto N m r (k i) b G hN hsize f x η
    (site i) (vertexBallEmbedding_depth (m+2) (k i)) (μ (k i) : Measure _)
    (hsignal i) (hbad (k i+b+1)) (F i) (hF0 i) (hF1 i)
  have hS0 : 0 ≤ S := (mul_nonneg (by positivity)
    (Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun v _ => sq_nonneg (f 0 a v))))).trans (hS 0)
  let B := 2*S+2*η^2*(r : ℝ)+1
  let M := 4*S+4*η^2*(r : ℝ)+3
  have hM : 0 < M := by dsimp [M]; positivity
  have hbudget : B/M < 1 := (div_lt_one hM).mpr (by dsimp [B,M]; nlinarith [sq_nonneg η,show 0 ≤ (r : ℝ) by positivity])
  have hH (b n : ℕ) : Integrable (H b n) (P n) :=
    integrable_graphGaussianPerturbedRootEnergy (G n) r x b (f n) η
  have hH0 (b n : ℕ) (ξ : Ω n) : 0 ≤ H b n ξ :=
    mul_nonneg (by positivity) (Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun v _ => sq_nonneg _)))
  obtain ⟨n,hn,ξ,henergy,haccuracy⟩ := exists_diagonal_samples_of_second_error_tendsto Ω P X target H
    hH hH0 (fun b n i => (herr b i).1 n) (fun b i => (herr b i).2)
    B M hM hbudget (fun b => eventually_integral_graphGaussianPerturbedRootEnergy_le N m r G hN f S hS x η hbad b)
    (fun b => 1/((b : ℝ)+1)) (fun b => by positivity)
  let g (b : ℕ) := graphGaussianPerturbedMark (G (n b)) r x b (f (n b)) η (ξ b)
  refine ⟨n,hn,g,henergy,fun i => ?_⟩
  have htarget : Tendsto (fun b => target b i) atTop
      (𝓝 (∫ z,F i z ∂independentAddLaw (μ (k i) : Measure _) (Measure.map
        (fun y : (Fin r × RegularTreeVertex (m+2)) → ℝ =>
          fun aj : Fin r × VertexBallVertex (m+2) (k i) => y (aj.1,site i aj.2))
        (jointGaussianTreeProcessLaw r m (radialEnergy m x))) η)) :=
    independentAdd_jointGaussianBlock_weakConverges r m hm x hx (site i) (μ (k i) : Measure _) η (F i)
  have hdiff : Tendsto (fun b => X b (n b) i (ξ b)-target b i) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [eventually_ge_atTop i] with b hbi
    simpa only [Real.norm_eq_abs] using (haccuracy b ⟨i,by omega⟩).le
  have hobs (b : ℕ) : X b (n b) i (ξ b) = ∫ z,F i z ∂finiteVertexCoverLaw (G (n b)) (k i) (g b) := by
    let W := fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ =>
      fun aj : Fin r × VertexBallVertex (m+2) (k i) => z (aj.1,site i aj.2)
    have hW : Measurable W := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
    change (∫ z,F i (W z) ∂uniformLiftedTreeLaw (G (n b)) (hN (n b)) (g b)) = _
    rw [← integral_map hW.aemeasurable (F i).continuous.aestronglyMeasurable,
      uniformLiftedTreeLaw_ball]
  have ht := hdiff.add htarget
  simp only [sub_add_cancel,zero_add,hobs] at ht
  exact ht

end GaussianWave.BS
