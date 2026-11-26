import GaussianWave.BS.GraphGaussianGoodWindow
import GaussianWave.BS.IndependentAddition
import GaussianWave.BS.FiniteAtomicLaws
import GaussianWave.BS.Lower.CoverRecoloring

/-! Exact expected local Gaussian smoothing at good cover roots, with an
explicit bad-root error for the actual finite cover source. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GaussianWave.BS
open Reused.Graph Lower

/-- Bounded observations integrate over the literal finite uniform source. -/
theorem integral_uniformAtomicLaw_boundedTest {A E : Type*} [Fintype A]
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (mark : A → E) (F : BoundedContinuousFunction E ℝ) :
    (∫ z,F z ∂uniformAtomicLaw mark) = (Fintype.card A : ℝ)⁻¹*∑ a,F (mark a) := by
  letI : MeasurableSpace A := ⊤
  letI : MeasurableSingletonClass A := ⟨fun _ => trivial⟩
  rw [uniformAtomicLaw_eq_map,integral_map (measurable_of_finite mark).aemeasurable
    F.continuous.aestronglyMeasurable,integral_finiteUniform]

/-- A fixed signal shift does not alter the exact good-root noise-law
identity. Every noise sample is taken from the actual finite-graph labels. -/
theorem graphGaussianWindow_test_eq_of_good {N m : ℕ}
    (G : RegularGraph N (m+2)) (k b : ℕ)
    (seed : VertexCoverSeed N m (k+b+1)) (x η : ℝ)
    {J : Type*} [Fintype J] (site : J → RegularTreeVertex (m+2))
    (hsite : ∀ j,regularTreeDepth (site j) ≤ k+1)
    (hgood : GoodVertexCoverRoot G (k+b+1) seed.1)
    (z : J → ℝ) (F : BoundedContinuousFunction (J → ℝ) ℝ) :
    (∫ ξ,F (z+η • (fun j => finiteSupportGaussianSample
      (graphRadialGaussianCoefficient G.val (m+2) x b) ξ
        (infiniteVertexGraphCover G (k+b+1) seed (site j)))) ∂gaussianLabelLaw (Fin N)) =
    ∫ y,F (z+η • y) ∂finiteSupportGaussianLaw
      (fun j => radialGaussianBlockCoefficient (m+2) x b (site j)) := by
  let a := fun j => graphRadialGaussianCoefficient G.val (m+2) x b
    (infiniteVertexGraphCover G (k+b+1) seed (site j))
  have hf : AEStronglyMeasurable (fun y : J → ℝ => F (z+η • y)) (finiteSupportGaussianLaw a) :=
    (F.continuous.comp (continuous_const.add (continuous_const.smul continuous_id))).aestronglyMeasurable
  have he := integral_map (measurable_finiteSupportGaussianSample a).aemeasurable hf
  change (∫ y,F (z+η • y) ∂finiteSupportGaussianLaw a) = _ at he
  rw [graphRadialGaussianLaw_window_of_good G k b seed x site hsite hgood] at he
  exact he.symm

/-- Averaged expected output is the actual independent-addition law of the
uniformly sampled signal window and the fixed tree blockfactor, up to the
explicit enlarged bad-root fraction. -/
theorem graphGaussianWindow_mean_error {N m : ℕ}
    (G : RegularGraph N (m+2)) (hN : 0 < N) (k b : ℕ) (x η : ℝ)
    {J : Type*} [Fintype J] (site : J → RegularTreeVertex (m+2))
    (hsite : ∀ j,regularTreeDepth (site j) ≤ k+1)
    (signal : VertexCoverSeed N m (k+b+1) → J → ℝ)
    (F : BoundedContinuousFunction (J → ℝ) ℝ) :
    |(Fintype.card (VertexCoverSeed N m (k+b+1)) : ℝ)⁻¹*
      (∑ seed : VertexCoverSeed N m (k+b+1),
        ∫ ξ,F (signal seed+η • (fun j => finiteSupportGaussianSample
          (graphRadialGaussianCoefficient G.val (m+2) x b) ξ
            (infiniteVertexGraphCover G (k+b+1) seed (site j)))) ∂gaussianLabelLaw (Fin N))-
      ∫ z,F z ∂independentAddLaw (uniformAtomicLaw signal)
        (finiteSupportGaussianLaw (fun j => radialGaussianBlockCoefficient (m+2) x b (site j))) η| ≤
      2*‖F‖*((N : ℝ)⁻¹*badVertexCoverRootCount G (k+b+1)) := by
  letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  letI : IsProbabilityMeasure (uniformAtomicLaw signal) := uniformAtomicLaw_isProbability _
  let L := finiteSupportGaussianLaw (fun j => radialGaussianBlockCoefficient (m+2) x b (site j))
  let A (seed : VertexCoverSeed N m (k+b+1)) :=
    ∫ ξ,F (signal seed+η • (fun j => finiteSupportGaussianSample
      (graphRadialGaussianCoefficient G.val (m+2) x b) ξ
        (infiniteVertexGraphCover G (k+b+1) seed (site j)))) ∂gaussianLabelLaw (Fin N)
  let B (seed : VertexCoverSeed N m (k+b+1)) := ∫ y,F (signal seed+η • y) ∂L
  have htarget : (∫ z,F z ∂independentAddLaw (uniformAtomicLaw signal) L η) =
      (Fintype.card (VertexCoverSeed N m (k+b+1)) : ℝ)⁻¹*∑ seed,B seed := by
    rw [integral_independentAddLaw]
    exact integral_uniformAtomicLaw_boundedTest signal (averagedAddTest L η F)
  have hp (seed : VertexCoverSeed N m (k+b+1)) :
      |A seed-B seed| ≤ 2*‖F‖*(if GoodVertexCoverRoot G (k+b+1) seed.1 then 0 else 1) := by
    by_cases hg : GoodVertexCoverRoot G (k+b+1) seed.1
    · have he := graphGaussianWindow_test_eq_of_good G k b seed x η site hsite hg (signal seed) F
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
