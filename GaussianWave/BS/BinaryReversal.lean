import GaussianWave.BS.ScoreRotation

/-!
# Actual endpoint reversal and observed Fisher energies

The symmetry is imposed on the original two-dimensional marginal law.
Heat equivariance proves the same symmetry at positive times, and the actual
smooth density then has equal Fisher energies in its exchanged coordinates.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianWave.BS

def binarySwap : (Bool → ℝ) ≃L[ℝ] (Bool → ℝ) :=
  coordinatePermutation (Equiv.swap false true)

def binarySwapMatrix : Matrix Bool Bool ℝ := fun b a => if a = !b then 1 else 0

theorem binarySwap_eq_matrix : (binarySwap : (Bool → ℝ) → (Bool → ℝ)) =
    fun x => binarySwapMatrix.mulVec x := by
  funext x b
  cases b <;> simp [binarySwap, coordinatePermutation_apply, Equiv.swap_apply_def,
    binarySwapMatrix, Matrix.mulVec, dotProduct, Fintype.sum_bool]

theorem binarySwapMatrix_orthogonal : binarySwapMatrix * binarySwapMatrix.transpose = 1 := by
  ext b a
  cases b <;> cases a <;> norm_num [binarySwapMatrix, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.one_apply, Fintype.sum_bool]

theorem binarySwap_volume_preserving :
    MeasurePreserving binarySwap (volume : Measure (Bool → ℝ)) volume :=
  coordinatePermutation_volume_preserving _

theorem binarySwap_basis_false : binarySwap (Pi.single false (1 : ℝ)) = Pi.single true 1 := by
  ext b
  cases b <;> simp [binarySwap, coordinatePermutation_apply, Equiv.swap_apply_def]

theorem heatedLaw_binarySwap_invariant
    (ν : Measure (Bool → ℝ)) [IsProbabilityMeasure ν]
    (hrev : Measure.map binarySwap ν = ν) (t : ℝ) :
    Measure.map binarySwap (heatedLaw ν t) = heatedLaw ν t := by
  rw [binarySwap_eq_matrix] at hrev ⊢
  exact heatedLaw_orthogonal_symmetry ν binarySwapMatrix binarySwapMatrix_orthogonal hrev t

theorem heatDensity_binarySwap_invariant
    (ν : Measure (Bool → ℝ)) [IsProbabilityMeasure ν]
    (hrev : Measure.map binarySwap ν = ν) {t : ℝ} (ht : 0 < t) :
    ∀ x, heatDensity ν t (binarySwap x) = heatDensity ν t x := by
  apply density_symmetry_of_map_invariant (heatDensity ν t) (continuous_heatDensity ν ht)
    (heatDensity_nonneg ν t) binarySwap binarySwap_volume_preserving
  rw [← heatedLaw_eq_withDensity ν ht]
  exact heatedLaw_binarySwap_invariant ν hrev t

theorem directionalFisherEnergy_heatDensity_coordinate
    {I : Type*} [Fintype I] [DecidableEq I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t) (i : I) :
    directionalFisherEnergy (heatDensity μ t) (Pi.single i 1) =
      ∫ x, heatFisherCoordinate μ t i x := by
  unfold directionalFisherEnergy directionalScore
  simp_rw [fderiv_heatDensity_apply μ ht]
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  apply integral_congr_ae
  filter_upwards [] with x
  unfold heatFisherCoordinate
  field_simp [(heatDensity_pos μ ht x).ne']
  ring

/-- Source equation(11.6) for the actual heated marginal, derived from
reversal of the original marginal law. -/
theorem integral_heatFisherCoordinate_eq_of_reversal
    (ν : Measure (Bool → ℝ)) [IsProbabilityMeasure ν]
    (hrev : Measure.map binarySwap ν = ν) {t : ℝ} (ht : 0 < t) :
    (∫ x, heatFisherCoordinate ν t false x) = (∫ x, heatFisherCoordinate ν t true x) := by
  have h := directionalFisherEnergy_reversal (heatDensity ν t)
    ((contDiff_one_heatDensity ν ht).differentiable (by norm_num)) binarySwap
    binarySwap_volume_preserving (heatDensity_binarySwap_invariant ν hrev ht) (Pi.single false 1)
  rw [binarySwap_basis_false, directionalFisherEnergy_heatDensity_coordinate ν ht,
    directionalFisherEnergy_heatDensity_coordinate ν ht] at h
  exact h.symm

/-- Reversal makes the weighted sum of the two actual observed directional
energies equal to half the full observed Fisher information. -/
theorem weighted_binary_heatFisher_eq_half
    (ν : Measure (Bool → ℝ)) [IsProbabilityMeasure ν]
    (hrev : Measure.map binarySwap ν = ν) {t : ℝ} (ht : 0 < t)
    (a b : ℝ) (hab : a + b = 1) :
    a * (∫ x, heatFisherCoordinate ν t false x) +
      b * (∫ x, heatFisherCoordinate ν t true x) = (1 / 2 : ℝ) * heatFisherInformation ν t := by
  have heq := integral_heatFisherCoordinate_eq_of_reversal ν hrev ht
  unfold heatFisherInformation
  simp only [Fintype.sum_bool]
  rw [integral_add (integrable_heatFisherCoordinate ν ht true) (integrable_heatFisherCoordinate ν ht false)]
  rw [← heq]
  rw [← add_mul, hab]
  ring

end GaussianWave.BS
