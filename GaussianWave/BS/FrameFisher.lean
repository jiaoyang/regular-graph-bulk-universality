import GaussianWave.BS.HeatScores
import GaussianWave.BS.HeatEntropyFunctional
import GaussianWave.BS.StarFrame

/-!
# Integrating the actual weighted frame against the heated law

This connects the literal finite-dimensional frame identity to actual L2 heat
scores. The frame identity is geometric data independent of the unknown law;
StarFrame supplies it explicitly for BS rather than assuming it in that case.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianWave.BS

theorem heatDirectionalScore_as_linearForm
    {I : Type*} [Fintype I] (μ : Measure (I → ℝ)) (t : ℝ) (v x : I → ℝ) :
    heatDirectionalScore μ t v x = finiteLinearForm v
      (fun j => heatDensityGradient μ t x j / heatDensity μ t x) := by
  unfold heatDirectionalScore finiteLinearForm
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Integrating the pointwise weighted tight frame gives precisely the full
Fisher information of the actual heat law. -/
theorem heatDirectionalScoreL2_weighted_frame
    {I K : Type*} [Fintype I] [Fintype K]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t)
    (O : K → Matrix Bool I ℝ) (a b : ℝ)
    (hframe : ∀ z : I → ℝ,
      (∑ i, (a * ((O i).mulVec z false) ^ 2 + b * ((O i).mulVec z true) ^ 2)) =
        squareRadius z) :
    (∑ i, (a * ‖heatDirectionalScoreL2 μ ht (O i false)‖ ^ 2 +
      b * ‖heatDirectionalScoreL2 μ ht (O i true)‖ ^ 2)) = heatFisherInformation μ t := by
  have hi (i : K) : Integrable (fun x =>
      (a * heatDirectionalScore μ t (O i false) x ^ 2 +
        b * heatDirectionalScore μ t (O i true) x ^ 2) * heatDensity μ t x) := by
    convert ((integrable_heatDirectionalScore_sq_density μ ht (O i false)).const_mul a).add
      ((integrable_heatDirectionalScore_sq_density μ ht (O i true)).const_mul b) using 1
    funext x
    simp only [Pi.add_apply]
    ring
  have hpoint (x : I → ℝ) :
      (∑ i, (a * heatDirectionalScore μ t (O i false) x ^ 2 +
        b * heatDirectionalScore μ t (O i true) x ^ 2) * heatDensity μ t x) =
        ∑ j, heatFisherCoordinate μ t j x := by
    rw [← Finset.sum_mul]
    simp_rw [heatDirectionalScore_as_linearForm]
    have heq (i : K) (r : Bool) :
        finiteLinearForm (O i r) (fun j => heatDensityGradient μ t x j / heatDensity μ t x) =
          (O i).mulVec (fun j => heatDensityGradient μ t x j / heatDensity μ t x) r := rfl
    simp_rw [heq]
    rw [hframe]
    unfold squareRadius
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    unfold heatFisherCoordinate
    field_simp [(heatDensity_pos μ ht x).ne']
    ring
  simp_rw [heatDirectionalScoreL2_norm_sq μ ht]
  calc
    _ = ∑ i, ∫ x, (a * heatDirectionalScore μ t (O i false) x ^ 2 +
        b * heatDirectionalScore μ t (O i true) x ^ 2) * heatDensity μ t x := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show (fun x => (a * heatDirectionalScore μ t (O i false) x ^ 2 +
          b * heatDirectionalScore μ t (O i true) x ^ 2) * heatDensity μ t x) =
          (fun x => a * (heatDirectionalScore μ t (O i false) x ^ 2 * heatDensity μ t x) +
            b * (heatDirectionalScore μ t (O i true) x ^ 2 * heatDensity μ t x)) from
          funext (fun x => by ring)]
      rw [integral_add
        ((integrable_heatDirectionalScore_sq_density μ ht (O i false)).const_mul a)
        ((integrable_heatDirectionalScore_sq_density μ ht (O i true)).const_mul b)]
      simp only [integral_const_mul]
    _ = ∫ x, ∑ i, (a * heatDirectionalScore μ t (O i false) x ^ 2 +
        b * heatDirectionalScore μ t (O i true) x ^ 2) * heatDensity μ t x :=
      (integral_finset_sum _ (fun i _ => hi i)).symm
    _ = heatFisherInformation μ t := integral_congr_ae (ae_of_all _ hpoint)

/-- BS's explicit root/simplex frame has the required integrated identity for
every actual input probability law, without an abstract frame premise. -/
theorem star_heatDirectionalScoreL2_weighted_frame
    (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1)
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t) :
    (∑ i : Fin d,
      (weightA d c * ‖heatDirectionalScoreL2 μ ht (starEdgeProjection d c i false)‖ ^ 2 +
        weightB d c * ‖heatDirectionalScoreL2 μ ht (starEdgeProjection d c i true)‖ ^ 2)) =
      heatFisherInformation μ t :=
  heatDirectionalScoreL2_weighted_frame μ ht (starEdgeProjection d c) (weightA d c) (weightB d c)
    (starEdgeProjection_weighted_energy d hd c hc)

end GaussianWave.BS
