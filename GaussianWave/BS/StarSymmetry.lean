import GaussianWave.BS.UpperBound

/-!
# Permutation symmetry identifies all actual edge laws

This recovers BS's single-edge formulation from the averaged-edge upper bound.
The entropy equality uses uniqueness of actual densities, not a premise that
different edge entropy values have already been identified.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianWave.BS

theorem starRootForm_permutation {d : ℕ} (p : Equiv.Perm (Fin d)) (x : Fin d → ℝ) :
    starRootForm (fun j => x (p j)) = starRootForm x := by
  unfold starRootForm
  rw [Equiv.sum_comp p]

theorem starCenteredCoordinate_permutation {d : ℕ} (p : Equiv.Perm (Fin d))
    (x : Fin d → ℝ) (i : Fin d) :
    starCenteredCoordinate (fun j => x (p j)) i = starCenteredCoordinate x (p i) := by
  unfold starCenteredCoordinate
  rw [Equiv.sum_comp p]

theorem starEdgeProjection_permutation {d : ℕ} (c : ℝ) (p : Equiv.Perm (Fin d))
    (x : Fin d → ℝ) (i : Fin d) :
    (starEdgeProjection d c i).mulVec (fun j => x (p j)) =
      (starEdgeProjection d c (p i)).mulVec x := by
  ext b
  cases b <;> simp only [starEdgeProjection_apply_false, starEdgeProjection_apply_true,
    starRootForm_permutation, starCenteredCoordinate_permutation]

theorem star_edge_laws_equal_of_permutation_invariant
    {d : ℕ} (c : ℝ) (μ : Measure (Fin d → ℝ))
    (hperm : ∀ p : Equiv.Perm (Fin d), Measure.map (fun x : Fin d → ℝ => fun j => x (p j)) μ = μ)
    (i j : Fin d) :
    Measure.map (fun x => (starEdgeProjection d c i).mulVec x) μ =
      Measure.map (fun x => (starEdgeProjection d c j).mulVec x) μ := by
  let p : Equiv.Perm (Fin d) := Equiv.swap i j
  have hp : p i = j := Equiv.swap_apply_left i j
  calc
    _ = Measure.map (fun x => (starEdgeProjection d c i).mulVec x)
        (Measure.map (fun x : Fin d → ℝ => fun k => x (p k)) μ) := by rw [hperm]
    _ = Measure.map (fun x => (starEdgeProjection d c j).mulVec x) μ := by
      rw [Measure.map_map (measurable_finiteMatrixAction _)
        (measurable_pi_lambda _ (fun k => measurable_pi_apply (p k)))]
      congr 1
      funext x
      exact (starEdgeProjection_permutation c p x i).trans (by rw [hp])

/-- The published single-edge entropy upper bound in white coordinates. -/
theorem star_single_edge_entropy_upper
    (d : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] (hmom : HasIdentitySecondMoments μ)
    (f : FiniteEntropyDensity μ)
    (g : ∀ i, FiniteEntropyDensity
      (Measure.map (fun x => (starEdgeProjection d c i).mulVec x) μ))
    (hrev : ∀ i, Measure.map binarySwap
      (Measure.map (fun x => (starEdgeProjection d c i).mulVec x) μ) =
        Measure.map (fun x => (starEdgeProjection d c i).mulVec x) μ)
    (hperm : ∀ p : Equiv.Perm (Fin d), Measure.map (fun x : Fin d → ℝ => fun j => x (p j)) μ = μ)
    (i₀ : Fin d) :
    f.entropy ≤ (d : ℝ) / 2 * (g i₀).entropy := by
  have h := star_entropy_upper d hd c hbulk μ
    (integrable_squareRadius_of_identitySecondMoments μ hmom) hmom f g hrev
  have heq (i : Fin d) : (g i).entropy = (g i₀).entropy :=
    (g i).entropy_eq_of_measure_eq (g i₀)
      (star_edge_laws_equal_of_permutation_invariant c μ hperm i i₀)
  simp_rw [heq] at h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  convert h using 1 <;> ring

end GaussianWave.BS
