import GaussianWave.BS.ColoredStarFrame
import GaussianWave.BS.FisherMonotonicity

/-!
# Actual multichannel Fisher monotonicity in the strict bulk

The observation sigma-algebra contains all endpoint coordinates in all
channels. Only simultaneous endpoint reversal of that whole edge law is
assumed. Channel independence is neither assumed nor used.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianWave.BS

def coordinatePermutationMatrix {I : Type*} [Fintype I] [DecidableEq I]
    (e : Equiv.Perm I) : Matrix I I ℝ := fun i j => if j = e i then 1 else 0

theorem coordinatePermutation_eq_matrix {I : Type*} [Fintype I] [DecidableEq I]
    (e : Equiv.Perm I) : (coordinatePermutation e : (I → ℝ) → (I → ℝ)) =
      fun x => (coordinatePermutationMatrix e).mulVec x := by
  funext x i
  simp [coordinatePermutationMatrix, Matrix.mulVec, dotProduct, ite_mul]

theorem coordinatePermutationMatrix_orthogonal {I : Type*} [Fintype I] [DecidableEq I]
    (e : Equiv.Perm I) : coordinatePermutationMatrix e * (coordinatePermutationMatrix e).transpose = 1 := by
  ext i j
  simp [coordinatePermutationMatrix, Matrix.mul_apply, Matrix.transpose_apply,
    ite_mul, Matrix.one_apply, e.injective.eq_iff, eq_comm]

/-- Actual heat flow preserves a finite coordinate-permutation law symmetry. -/
theorem heatedLaw_coordinatePermutation_invariant
    {I : Type*} [Fintype I] [DecidableEq I]
    (ν : Measure (I → ℝ)) [IsProbabilityMeasure ν] (e : Equiv.Perm I)
    (hinv : Measure.map (coordinatePermutation e) ν = ν) (t : ℝ) :
    Measure.map (coordinatePermutation e) (heatedLaw ν t) = heatedLaw ν t := by
  rw [coordinatePermutation_eq_matrix] at hinv ⊢
  exact heatedLaw_orthogonal_symmetry ν (coordinatePermutationMatrix e)
    (coordinatePermutationMatrix_orthogonal e) hinv t

/-- Simultaneous edge reversal equates corresponding actual Fisher energies
even when the channels of the edge law are dependent. -/
theorem colored_integral_heatFisherCoordinate_eq_of_reversal
    (r : ℕ) (ν : Measure ((Bool × Fin r) → ℝ)) [IsProbabilityMeasure ν]
    (hrev : Measure.map (edgeFlipLinear r) ν = ν) {t : ℝ} (ht : 0 < t) (a : Fin r) :
    (∫ x, heatFisherCoordinate ν t (false, a) x) =
      ∫ x, heatFisherCoordinate ν t (true, a) x := by
  have hsym : ∀ x, heatDensity ν t (edgeFlipLinear r x) = heatDensity ν t x := by
    apply density_symmetry_of_map_invariant (heatDensity ν t) (continuous_heatDensity ν ht)
      (heatDensity_nonneg ν t) (edgeFlipLinear r)
      (coordinatePermutation_volume_preserving (edgeFlipIndex r))
    rw [← heatedLaw_eq_withDensity ν ht]
    exact heatedLaw_coordinatePermutation_invariant ν (edgeFlipIndex r) hrev t
  have h := edge_reversal_directionalFisher_equal r (heatDensity ν t)
    ((contDiff_one_heatDensity ν ht).differentiable le_rfl) hsym a
  rw [directionalFisherEnergy_heatDensity_coordinate ν ht,
    directionalFisherEnergy_heatDensity_coordinate ν ht] at h
  exact h

/-- Reversal converts the weighted energy of all observed directions to
half the actual Fisher information of the whole 2r-dimensional marginal. -/
theorem colored_weighted_heatFisher_eq_half
    (r : ℕ) (ν : Measure ((Bool × Fin r) → ℝ)) [IsProbabilityMeasure ν]
    (hrev : Measure.map (edgeFlipLinear r) ν = ν) {t : ℝ} (ht : 0 < t)
    (a b : ℝ) (hab : a + b = 1) :
    (∑ q, (a * (∫ x, heatFisherCoordinate ν t (false, q) x) +
      b * (∫ x, heatFisherCoordinate ν t (true, q) x))) =
        (1 / 2 : ℝ) * heatFisherInformation ν t := by
  have hlocal (q : Fin r) :
      a * (∫ x, heatFisherCoordinate ν t (false, q) x) +
        b * (∫ x, heatFisherCoordinate ν t (true, q) x) =
      (1 / 2 : ℝ) * ((∫ x, heatFisherCoordinate ν t (false, q) x) +
        (∫ x, heatFisherCoordinate ν t (true, q) x)) := by
    rw [← colored_integral_heatFisherCoordinate_eq_of_reversal r ν hrev ht q, ← add_mul, hab]
    ring
  simp_rw [hlocal]
  rw [← Finset.mul_sum]
  congr 1
  unfold heatFisherInformation
  rw [integral_finset_sum _ (fun i _ => integrable_heatFisherCoordinate ν ht i)]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, Finset.sum_add_distrib]
  ring

/-- Integrating a multichannel weighted tight frame against the actual
heat law. This geometric identity does not involve edge independence. -/
theorem colored_heatDirectionalScoreL2_weighted_frame
    {I K : Type*} [Fintype I] [Fintype K]
    (r : ℕ) (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t)
    (O : K → Matrix (Bool × Fin r) I ℝ) (a b : ℝ)
    (hframe : ∀ z : I → ℝ,
      (∑ i, ∑ q, (a * ((O i).mulVec z (false, q)) ^ 2 +
        b * ((O i).mulVec z (true, q)) ^ 2)) = squareRadius z) :
    (∑ i, ∑ q, (a * ‖heatDirectionalScoreL2 μ ht (O i (false, q))‖ ^ 2 +
      b * ‖heatDirectionalScoreL2 μ ht (O i (true, q))‖ ^ 2)) = heatFisherInformation μ t := by
  let O' : (K × Fin r) → Matrix Bool I ℝ := fun p b => O p.1 (b, p.2)
  have hframe' : ∀ z : I → ℝ,
      (∑ p, (a * ((O' p).mulVec z false) ^ 2 + b * ((O' p).mulVec z true) ^ 2)) = squareRadius z := by
    intro z
    simpa only [Fintype.sum_prod_type] using hframe z
  have h := heatDirectionalScoreL2_weighted_frame μ ht O' a b hframe'
  simpa only [Fintype.sum_prod_type] using h

/-- Actual Fisher monotonicity for a whole-edge multichannel observation.
The conditional expectations in the contraction retain every channel, so
arbitrary dependence between channels is allowed. -/
theorem colored_heatFrameFisherDefect_nonneg
    {I K : Type*} [Fintype I] [Fintype K] [DecidableEq I]
    (r : ℕ) (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t)
    (O : K → Matrix (Bool × Fin r) I ℝ) (hO : ∀ i, O i * (O i).transpose = 1)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hframe : ∀ z : I → ℝ,
      (∑ i, ∑ q, (a * ((O i).mulVec z (false, q)) ^ 2 +
        b * ((O i).mulVec z (true, q)) ^ 2)) = squareRadius z)
    (hrev : ∀ i, Measure.map (edgeFlipLinear r) (Measure.map (fun x => (O i).mulVec x) μ) =
      Measure.map (fun x => (O i).mulVec x) μ) :
    0 ≤ heatFrameFisherDefect μ O t := by
  classical
  letI : ∀ i, IsProbabilityMeasure (Measure.map (fun x => (O i).mulVec x) μ) :=
    fun i => isProbabilityMeasure_map (measurable_finiteMatrixAction (O i)).aemeasurable
  have hlocal (i : K) :
      (1 / 2 : ℝ) * heatFisherInformation (Measure.map (fun x => (O i).mulVec x) μ) t ≤
        ∑ q, (a * ‖heatDirectionalScoreL2 μ ht (O i (false, q))‖ ^ 2 +
          b * ‖heatDirectionalScoreL2 μ ht (O i (true, q))‖ ^ 2) := by
    rw [← colored_weighted_heatFisher_eq_half r _ (hrev i) ht a b hab]
    apply Finset.sum_le_sum
    intro q _
    exact add_le_add
      (mul_le_mul_of_nonneg_left
        (marginal_heatFisherCoordinate_le_full_score μ ht (O i) (hO i) (false, q)) ha)
      (mul_le_mul_of_nonneg_left
        (marginal_heatFisherCoordinate_le_full_score μ ht (O i) (hO i) (true, q)) hb)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset K)) => hlocal i)
  rw [← Finset.mul_sum, colored_heatDirectionalScoreL2_weighted_frame r μ ht O a b hframe] at hsum
  exact sub_nonneg.mpr hsum

/-- The strict-bulk common-energy multichannel BS Fisher inequality for
arbitrary joint input laws. No channel independence, score identity, Fisher
inequality, or geometric frame hypothesis remains in this specialization. -/
theorem colored_star_heatFrameFisherDefect_nonneg
    (d r : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (μ : Measure ((Fin r × Fin d) → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t)
    (hrev : ∀ i, Measure.map (edgeFlipLinear r)
      (Measure.map (fun x => (coloredStarEdgeProjection d r c i).mulVec x) μ) =
        Measure.map (fun x => (coloredStarEdgeProjection d r c i).mulVec x) μ) :
    0 ≤ heatFrameFisherDefect μ (coloredStarEdgeProjection d r c) t := by
  have hc := (bulk_rho_lower d hd c hbulk).1
  exact colored_heatFrameFisherDefect_nonneg r μ ht (coloredStarEdgeProjection d r c)
    (coloredStarEdgeProjection_mul_transpose d r (by omega) c hc)
    (weightA d c) (weightB d c) (bulk_weights_pos d hd c hbulk).1.le
    (bulk_weights_pos d hd c hbulk).2.le (weight_sum d c hc)
    (coloredStarEdgeProjection_weighted_energy d r (by omega) c hc) hrev

end GaussianWave.BS
