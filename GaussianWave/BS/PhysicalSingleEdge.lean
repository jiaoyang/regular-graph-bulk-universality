import GaussianWave.BS.PhysicalUpperBound

/-!
# The published single-edge form of the physical BS upper theorem

Only one finite-entropy edge witness and its reversal are needed: actual
neighbor-permutation invariance identifies all other edge laws. The entropy
is measured in any common intrinsic chart; the Gaussian-relative statement
is independent of the chart's fixed linear Jacobian.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianWave.BS

theorem physical_edge_laws_equal_of_permutation_invariant
    {d : ℕ} (ν : Measure (Fin (d + 1) → ℝ))
    (hperm : ∀ p : Equiv.Perm (Fin d), Measure.map (physicalStarPermutation p) ν = ν)
    (i j : Fin d) :
    Measure.map (physicalEdgeCoordinates i) ν = Measure.map (physicalEdgeCoordinates j) ν := by
  let p : Equiv.Perm (Fin d) := Equiv.swap i j
  have hp : p i = j := Equiv.swap_apply_left i j
  calc
    _ = Measure.map (physicalEdgeCoordinates i) (Measure.map (physicalStarPermutation p) ν) := by rw [hperm]
    _ = _ := by
      rw [Measure.map_map (measurable_physicalEdgeCoordinates i) (measurable_physicalStarPermutation p)]
      congr 1
      funext x b
      cases b <;> simp [Function.comp_def, physicalEdgeCoordinates, physicalStarPermutation, hp]

theorem physical_single_edge_entropy_upper_and_equality
    (d : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (chart : physicalStarHyperplane d c ≃ₗ[ℝ] (Fin d → ℝ))
    (N : Measure (physicalStarHyperplane d c)) [IsProbabilityMeasure N]
    (hC : HasSecondMoments (Measure.map (fun z : physicalStarHyperplane d c =>
        (z : Fin (d + 1) → ℝ)) N)
      (RegularEigenData.starWaveCovariance d ((d : ℝ) * c)))
    (f : FiniteEntropyDensity (Measure.map chart N)) (i₀ : Fin d)
    (g₀ : FiniteEntropyDensity (Measure.map (physicalEdgeCoordinates i₀)
      (Measure.map (fun z : physicalStarHyperplane d c => (z : Fin (d + 1) → ℝ)) N)))
    (hrev : Measure.map binarySwap (Measure.map (physicalEdgeCoordinates i₀)
      (Measure.map (fun z : physicalStarHyperplane d c => (z : Fin (d + 1) → ℝ)) N)) =
        Measure.map (physicalEdgeCoordinates i₀)
          (Measure.map (fun z : physicalStarHyperplane d c => (z : Fin (d + 1) → ℝ)) N))
    (hperm : ∀ p : Equiv.Perm (Fin d), Measure.map (physicalStarPermutation p)
      (Measure.map (fun z : physicalStarHyperplane d c => (z : Fin (d + 1) → ℝ)) N) =
        Measure.map (fun z : physicalStarHyperplane d c => (z : Fin (d + 1) → ℝ)) N) :
    let GaussianValue :=
      (physicalGaussianStarEntropyDensity d (by omega) c (bulk_rho_lower d hd c hbulk).1 chart).entropy -
        (d : ℝ) / 2 * (physicalGaussianEdgeEntropyDensity c (bulk_rho_lower d hd c hbulk).1).entropy
    (f.entropy - (d : ℝ) / 2 * g₀.entropy ≤ GaussianValue) ∧
      ((f.entropy - (d : ℝ) / 2 * g₀.entropy = GaussianValue) ↔
        N = physicalGaussianHyperplaneLaw d (by omega) c (bulk_rho_lower d hd c hbulk).1) := by
  let ν := Measure.map (fun z : physicalStarHyperplane d c => (z : Fin (d + 1) → ℝ)) N
  have heq (i : Fin d) : Measure.map (physicalEdgeCoordinates i) ν =
      Measure.map (physicalEdgeCoordinates i₀) ν :=
    physical_edge_laws_equal_of_permutation_invariant ν hperm i i₀
  let g := fun i : Fin d => g₀.cast (heq i)
  have hrevAll (i : Fin d) : Measure.map binarySwap (Measure.map (physicalEdgeCoordinates i) ν) =
      Measure.map (physicalEdgeCoordinates i) ν := by
    rw [heq i]
    exact hrev
  have hup := physical_hyperplane_entropy_upper d hd c hbulk chart N hC f g hrevAll
  have hequality := physical_hyperplane_entropy_equality_iff_gaussian d hd c hbulk chart N hC f g hrevAll hperm
  have hsum : (1 / 2 : ℝ) * ∑ i, (g i).entropy = (d : ℝ) / 2 * g₀.entropy := by
    simp only [g, FiniteEntropyDensity.cast_entropy, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hsum] at hup hequality
  exact ⟨hup, hequality⟩

theorem normalized_bulk_parameter_of_energy
    (d : ℕ) (hd : 3 ≤ d) (energy : ℝ)
    (henergy : |energy| < 2 * Real.sqrt ((d : ℝ) - 1)) :
    (energy / d) ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2 := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hs := (sq_lt_sq₀ (abs_nonneg energy)
    (by positivity : 0 ≤ 2 * Real.sqrt ((d : ℝ) - 1))).mpr henergy
  have he : energy ^ 2 < 4 * ((d : ℝ) - 1) := by
    simpa only [sq_abs, mul_pow, Real.sq_sqrt (by linarith : 0 ≤ (d : ℝ) - 1),
      show (2 : ℝ) ^ 2 = 4 from by norm_num] using hs
  rw [div_pow]
  exact div_lt_div_of_pos_right he (sq_pos_of_pos hdpos)

end GaussianWave.BS
