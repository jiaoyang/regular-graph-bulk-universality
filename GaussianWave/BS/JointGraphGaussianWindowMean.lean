import GaussianWave.BS.GraphGaussianWindowMean
import GaussianWave.BS.JointGraphGaussianBlockFactor
import GaussianWave.BS.LiftedCoverFiniteWindows

/-! The expected joint Gaussian perturbation of an actual finite-graph cover
window is the independent sum law up to the enlarged bad-root fraction. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GaussianWave.BS
open Reused.Graph Lower

theorem jointGraphGaussianWindow_test_eq_of_good {N m : ℕ}
    (G : RegularGraph N (m+2)) (r k b : ℕ)
    (seed : VertexCoverSeed N m (k+b+1)) (x η : ℝ)
    {J : Type*} [Fintype J] (site : J → RegularTreeVertex (m+2))
    (hsite : ∀ j,regularTreeDepth (site j) ≤ k+1)
    (hgood : GoodVertexCoverRoot G (k+b+1) seed.1)
    (z : (Fin r × J) → ℝ) (F : BoundedContinuousFunction ((Fin r × J) → ℝ) ℝ) :
    (∫ ξ,F (z+η • (fun aj : Fin r × J => finiteSupportGaussianSample
      (jointGraphGaussianCoefficient G r x b) ξ
        (aj.1,infiniteVertexGraphCover G (k+b+1) seed (site aj.2))))
      ∂gaussianLabelLaw (Fin r × Fin N)) =
    ∫ y,F (z+η • y) ∂Measure.map
      (fun y : (Fin r × RegularTreeVertex (m+2)) → ℝ =>
        fun aj : Fin r × J => y (aj.1,site aj.2))
      (jointRadialGaussianBlockLaw r (m+2) x b) := by
  let W := fun y : (Fin r × Fin N) → ℝ => fun aj : Fin r × J =>
    y (aj.1,infiniteVertexGraphCover G (k+b+1) seed (site aj.2))
  have hW : Measurable W := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have hlaw := jointGraphGaussianLaw_window_of_good G r k b seed x site hsite hgood
  have hf : AEStronglyMeasurable (fun y : (Fin r × J) → ℝ => F (z+η • y))
      (Measure.map W (jointGraphGaussianLaw G r x b)) :=
    (F.continuous.comp (continuous_const.add (continuous_const.smul continuous_id))).aestronglyMeasurable
  have he := integral_map hW.aemeasurable hf
  have hs : (∫ y,F (z+η • W y) ∂jointGraphGaussianLaw G r x b) =
      ∫ ξ,F (z+η • W (finiteSupportGaussianSample (jointGraphGaussianCoefficient G r x b) ξ))
        ∂gaussianLabelLaw (Fin r × Fin N) :=
    integral_map (measurable_finiteSupportGaussianSample _).aemeasurable
      ((F.continuous.measurable.comp
        (measurable_const.add (measurable_const.smul hW))).aestronglyMeasurable)
  rw [hlaw] at he
  exact hs.symm.trans he.symm


theorem jointGraphGaussianWindow_mean_error {N m : ℕ}
    (G : RegularGraph N (m+2)) (hN : 0 < N) (r k b : ℕ) (x η : ℝ)
    {J : Type*} [Fintype J] (site : J → RegularTreeVertex (m+2))
    (hsite : ∀ j,regularTreeDepth (site j) ≤ k+1)
    (signal : VertexCoverSeed N m (k+b+1) → (Fin r × J) → ℝ)
    (F : BoundedContinuousFunction ((Fin r × J) → ℝ) ℝ) :
    |(Fintype.card (VertexCoverSeed N m (k+b+1)) : ℝ)⁻¹*
      (∑ seed : VertexCoverSeed N m (k+b+1),
        ∫ ξ,F (signal seed+η • (fun aj : Fin r × J => finiteSupportGaussianSample
          (jointGraphGaussianCoefficient G r x b) ξ
            (aj.1,infiniteVertexGraphCover G (k+b+1) seed (site aj.2)))) ∂gaussianLabelLaw (Fin r × Fin N))-
      ∫ z,F z ∂independentAddLaw (uniformAtomicLaw signal)
        (Measure.map
          (fun y : (Fin r × RegularTreeVertex (m+2)) → ℝ =>
            fun aj : Fin r × J => y (aj.1,site aj.2))
          (jointRadialGaussianBlockLaw r (m+2) x b)) η| ≤
      2*‖F‖*((N : ℝ)⁻¹*badVertexCoverRootCount G (k+b+1)) := by
  letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  letI : IsProbabilityMeasure (uniformAtomicLaw signal) := uniformAtomicLaw_isProbability _
  let L := Measure.map
    (fun y : (Fin r × RegularTreeVertex (m+2)) → ℝ =>
      fun aj : Fin r × J => y (aj.1,site aj.2))
    (jointRadialGaussianBlockLaw r (m+2) x b)
  letI : IsProbabilityMeasure L := isProbabilityMeasure_map
    (measurable_pi_lambda _ (fun _ => measurable_pi_apply _)).aemeasurable
  let A (seed : VertexCoverSeed N m (k+b+1)) :=
    ∫ ξ,F (signal seed+η • (fun aj : Fin r × J => finiteSupportGaussianSample
      (jointGraphGaussianCoefficient G r x b) ξ
        (aj.1,infiniteVertexGraphCover G (k+b+1) seed (site aj.2)))) ∂gaussianLabelLaw (Fin r × Fin N)
  let B (seed : VertexCoverSeed N m (k+b+1)) := ∫ y,F (signal seed+η • y) ∂L
  have htarget : (∫ z,F z ∂independentAddLaw (uniformAtomicLaw signal) L η) =
      (Fintype.card (VertexCoverSeed N m (k+b+1)) : ℝ)⁻¹*∑ seed,B seed := by
    rw [integral_independentAddLaw]
    exact integral_uniformAtomicLaw_boundedTest signal (averagedAddTest L η F)
  have hp (seed : VertexCoverSeed N m (k+b+1)) :
      |A seed-B seed| ≤ 2*‖F‖*(if GoodVertexCoverRoot G (k+b+1) seed.1 then 0 else 1) := by
    by_cases hg : GoodVertexCoverRoot G (k+b+1) seed.1
    · have he := jointGraphGaussianWindow_test_eq_of_good G r k b seed x η site hsite hg (signal seed) F
      change A seed=B seed at he
      simp only [he,sub_self,abs_zero,if_pos hg,mul_zero,le_refl]
    · have hA : |A seed| ≤ ‖F‖ := by
        simpa only [Real.norm_eq_abs,measureReal_univ_eq_one,mul_one] using
          (norm_integral_le_of_norm_le_const
            (Filter.Eventually.of_forall (fun ξ => F.norm_coe_le_norm _)) : ‖A seed‖ ≤ _)
      have hB : |B seed| ≤ ‖F‖ := by
        simpa only [Real.norm_eq_abs,measureReal_univ_eq_one,mul_one] using
          (norm_integral_le_of_norm_le_const
            (Filter.Eventually.of_forall (fun y => F.norm_coe_le_norm _)) : ‖B seed‖ ≤ _)
      rw [if_neg hg,mul_one]
      exact (abs_sub _ _).trans (by linarith)
  rw [htarget]
  change |(Fintype.card (VertexCoverSeed N m (k+b+1)) : ℝ)⁻¹*(∑ seed,A seed)-
    (Fintype.card (VertexCoverSeed N m (k+b+1)) : ℝ)⁻¹*(∑ seed,B seed)| ≤ _
  calc
    _ = (Fintype.card (VertexCoverSeed N m (k+b+1)) : ℝ)⁻¹*|∑ seed,(A seed-B seed)| := by
      rw [← mul_sub,← Finset.sum_sub_distrib,abs_mul,abs_of_nonneg (by positivity)]
    _ ≤ (Fintype.card (VertexCoverSeed N m (k+b+1)) : ℝ)⁻¹*
        ∑ seed : VertexCoverSeed N m (k+b+1),
          (2*‖F‖*(if GoodVertexCoverRoot G (k+b+1) seed.1 then 0 else 1)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun seed _ => hp seed))
    _ = _ := by
      rw [← Finset.mul_sum]
      rw [show (Fintype.card (VertexCoverSeed N m (k+b+1)) : ℝ)⁻¹*
          (2*‖F‖*∑ seed : VertexCoverSeed N m (k+b+1),
            if GoodVertexCoverRoot G (k+b+1) seed.1 then 0 else 1) =
          2*‖F‖*((Fintype.card (VertexCoverSeed N m (k+b+1)) : ℝ)⁻¹*
            ∑ seed : VertexCoverSeed N m (k+b+1),
              if GoodVertexCoverRoot G (k+b+1) seed.1 then 0 else 1) by ring]
      congr 1
      exact uniformVertexCoverSeed_root_average (k+b+1)
        (fun v => if GoodVertexCoverRoot G (k+b+1) v then 0 else 1)


end GaussianWave.BS
