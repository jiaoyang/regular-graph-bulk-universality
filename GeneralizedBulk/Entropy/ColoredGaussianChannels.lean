import GeneralizedBulk.Entropy.ColoredObservationGeometry

/-! Concrete Gaussian star channels in the fixed scalar-adapted coordinates. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Channel
open GeneralizedBulk.Entropy.Hermite

def coloredObservationMatrix (d k : ℕ) (hd : 2 ≤ d) (i : Fin d) :
    Matrix (ScalarCoordinate d k) (ScalarCoordinate d k) ℝ :=
  observationMatrix (scalarAdaptedBasis d k) (coloredEdgeSpace d k hd i)

def coloredObserved (d k : ℕ) (hd : 2 ≤ d) (i : Fin d) : Finset (ScalarCoordinate d k) :=
  observationIndices (scalarAdaptedBasis d k) (coloredEdgeSpace d k hd i)

theorem coloredObservationMatrix_orthogonal (d k : ℕ) (hd : 2 ≤ d) (i : Fin d) :
    coloredObservationMatrix d k hd i * (coloredObservationMatrix d k hd i).transpose = 1 :=
  observationMatrix_orthogonal (scalarAdaptedBasis d k) (coloredEdgeSpace d k hd i)

/-- The retained coordinate space is the actual geometric overlapping edge
space, with no parameter-dependent change of scalar coordinates. -/
theorem colored_observation_mem_iff (d k : ℕ) (hd : 2 ≤ d) (i : Fin d) (x : ColoredStar d k) :
    scalarCoordinates d k x ∈ observationSubspace (coloredObservationMatrix d k hd i) (coloredObserved d k hd i) ↔
      x ∈ coloredEdgeSpace d k hd i := by
  change (∀ j, j ∉ observationIndices (scalarAdaptedBasis d k) (coloredEdgeSpace d k hd i) →
    (observationMatrix (scalarAdaptedBasis d k) (coloredEdgeSpace d k hd i)).transpose.mulVec
      ((scalarAdaptedBasis d k).repr x) j = 0) ↔ _
  rw [observationMatrix_transpose_repr]
  exact (observationBasis_mem_iff (scalarAdaptedBasis d k) (coloredEdgeSpace d k hd i) x).symm

def coloredDirectionCoordinatesA (d k : ℕ) (hd : 2 ≤ d) (c : Fin k → ℝ) (i : Fin d) (a : Fin k) :
    ScalarCoordinate d k → ℝ := scalarCoordinates d k (coloredDirectionA d k hd c i a)

def coloredDirectionCoordinatesB (d k : ℕ) (hd : 2 ≤ d) (c : Fin k → ℝ) (i : Fin d) (a : Fin k) :
    ScalarCoordinate d k → ℝ := scalarCoordinates d k (coloredDirectionB d k hd c i a)

def coloredReversalMatrix (d k : ℕ) (hd : 2 ≤ d) (c : Fin k → ℝ) (i : Fin d) :
    Matrix (ScalarCoordinate d k) (ScalarCoordinate d k) ℝ :=
  isometryMatrix (scalarAdaptedBasis d k) (coloredReversal d k hd c i)

theorem scalarCoordinates_dot (d k : ℕ) (x y : ColoredStar d k) :
    (∑ j, scalarCoordinates d k x j * scalarCoordinates d k y j) = @inner ℝ (ColoredStar d k) _ x y :=
  orthonormalCoordinates_dot (scalarAdaptedBasis d k) x y

theorem scalarCoordinates_sq (d k : ℕ) (x : ColoredStar d k) :
    (∑ j, (scalarCoordinates d k x j) ^ 2) = ‖x‖ ^ 2 :=
  orthonormalCoordinates_sq (scalarAdaptedBasis d k) x

/-- Every geometric hypothesis of the Gaussian square theorem is discharged
for the actual correlated regular-star channels. -/
def coloredGaussianFrameSystem (d k : ℕ) (hd : 2 ≤ d) (c : Fin k → ℝ)
    (hc : ∀ a, |c a| < 1) : GaussianFrameSystem (ScalarCoordinate d k) (Fin d) (Fin k) where
  coordinates := coloredObservationMatrix d k hd
  orthogonal := coloredObservationMatrix_orthogonal d k hd
  observed := coloredObserved d k hd
  directionA := coloredDirectionCoordinatesA d k hd c
  directionB := coloredDirectionCoordinatesB d k hd c
  weightA := fun _ a => weightA d (c a)
  weightB := fun _ a => weightB d (c a)
  retainedA := fun i a => (colored_observation_mem_iff d k hd i _).mpr
    (coloredDirectionA_mem_edgeSpace d k hd c i a)
  retainedB := fun i a => (colored_observation_mem_iff d k hd i _).mpr
    (coloredDirectionB_mem_edgeSpace d k hd c i a)
  weight_sum := fun _ a => weight_sum d (c a) (hc a)
  global_frame := by
    intro u
    let x := (scalarCoordinates d k).symm u
    have hx : scalarCoordinates d k x = u := (scalarCoordinates d k).apply_symm_apply u
    have hdA (i : Fin d) (a : Fin k) :
        (∑ j, coloredDirectionCoordinatesA d k hd c i a j * u j) =
          @inner ℝ (ColoredStar d k) _ (coloredDirectionA d k hd c i a) x := by
      rw [← hx]
      exact scalarCoordinates_dot d k _ _
    have hdB (i : Fin d) (a : Fin k) :
        (∑ j, coloredDirectionCoordinatesB d k hd c i a j * u j) =
          @inner ℝ (ColoredStar d k) _ (coloredDirectionB d k hd c i a) x := by
      rw [← hx]
      exact scalarCoordinates_dot d k _ _
    simp_rw [hdA, hdB]
    rw [colored_weighted_frame_energy d k hd c hc, ← scalarCoordinates_sq d k x, hx]
  observation_frame := by
    intro i u hu
    let x := (scalarCoordinates d k).symm u
    have hx : scalarCoordinates d k x = u := (scalarCoordinates d k).apply_symm_apply u
    have hmem : x ∈ coloredEdgeSpace d k hd i :=
      (colored_observation_mem_iff d k hd i x).mp (hx.symm ▸ hu)
    have hp := (mem_coloredEdgeSpace_iff d k hd i x).mp hmem
    have hdA (a : Fin k) : (∑ j, coloredDirectionCoordinatesA d k hd c i a j * u j) =
        @inner ℝ (ColoredStar d k) _ (coloredDirectionA d k hd c i a) x := by
      rw [← hx]
      exact scalarCoordinates_dot d k _ _
    have hdB (a : Fin k) : (∑ j, coloredDirectionCoordinatesB d k hd c i a j * u j) =
        @inner ℝ (ColoredStar d k) _ (coloredDirectionB d k hd c i a) x := by
      rw [← hx]
      exact scalarCoordinates_dot d k _ _
    simp_rw [hdA, hdB]
    rw [colored_edge_frame_energy d k hd c hc i x, hp, ← scalarCoordinates_sq d k x, hx]
  reversal := coloredReversalMatrix d k hd c
  reversal_orthogonal := fun i => isometryMatrix_orthogonal (scalarAdaptedBasis d k) (coloredReversal d k hd c i)
  reversal_swap := by
    intro i a
    change (isometryMatrix (scalarAdaptedBasis d k) (coloredReversal d k hd c i)).mulVec
      ((scalarAdaptedBasis d k).repr (coloredDirectionA d k hd c i a)) =
      (scalarAdaptedBasis d k).repr (coloredDirectionB d k hd c i a)
    rw [isometryMatrix_repr, coloredReversal_directionA d k hd c hc i a]

/-- Positivity of the actual correlated-star channel defect in every positive
homogeneous chaos degree, for every genuine reversal-admissible polynomial. -/
theorem coloredGaussian_defect_nonneg (d k : ℕ) (hd : 3 ≤ d) (c : Fin k → ℝ)
    (hbulk : ∀ a, (c a) ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (degree : ℕ) (hdegree : 0 < degree) (coeff : DegreeIndex (ScalarCoordinate d k) degree → ℝ)
    (hadm : (coloredGaussianFrameSystem d k (by omega) c
      (fun a => (bulk_rho_lower d hd (c a) (hbulk a)).1)).Admissible
        (chaosLp (degreeIndexNat (ScalarCoordinate d k)) coeff)) :
    0 ≤ (coloredGaussianFrameSystem d k (by omega) c
      (fun a => (bulk_rho_lower d hd (c a) (hbulk a)).1)).defect
        (chaosLp (degreeIndexNat (ScalarCoordinate d k)) coeff) := by
  apply GaussianFrameSystem.defect_nonneg _ degree hdegree coeff hadm
  · intro i a
    exact (bulk_weights_pos d hd (c a) (hbulk a)).1.le
  · intro i a
    exact (bulk_weights_pos d hd (c a) (hbulk a)).2.le


/-- Discarded geometric directions have zero retained observation coordinates,
proved from the self-adjoint actual edge projector. -/
theorem colored_discarded_coordinates (d k : ℕ) (hd : 2 ≤ d) (i : Fin d)
    (u : ColoredStar d k) (j : ScalarCoordinate d k) (hj : j ∈ coloredObserved d k hd i) :
    (coloredObservationMatrix d k hd i).transpose.mulVec
      (scalarCoordinates d k (u - coloredEdgeProjection d k hd i u)) j = 0 := by
  change (observationMatrix (scalarAdaptedBasis d k) (coloredEdgeSpace d k hd i)).transpose.mulVec
    ((scalarAdaptedBasis d k).repr (u - coloredEdgeProjection d k hd i u)) j = 0
  rw [observationMatrix_transpose_repr, OrthonormalBasis.repr_apply_apply, inner_sub_right]
  have hm : observationBasis (scalarAdaptedBasis d k) (coloredEdgeSpace d k hd i) j ∈
      coloredEdgeSpace d k hd i :=
    (mem_observationIndices (scalarAdaptedBasis d k) (coloredEdgeSpace d k hd i) j).mp hj
  have hp := (mem_coloredEdgeSpace_iff d k hd i _).mp hm
  rw [← coloredEdgeProjection_selfAdjoint, hp, sub_self]


/-- Vanishing of all retained observation coordinates is exactly orthogonality
to the actual edge space, hence annihilation by the true edge projector. -/
theorem colored_projection_zero_of_discarded_coordinates (d k : ℕ) (hd : 2 ≤ d) (i : Fin d)
    (u : ColoredStar d k)
    (hu : ∀ j, j ∈ coloredObserved d k hd i →
      (coloredObservationMatrix d k hd i).transpose.mulVec (scalarCoordinates d k u) j = 0) :
    coloredEdgeProjection d k hd i u = 0 := by
  let b := observationBasis (scalarAdaptedBasis d k) (coloredEdgeSpace d k hd i)
  have hp : coloredEdgeProjection d k hd i u ∈ coloredEdgeSpace d k hd i := ⟨u, rfl⟩
  apply b.repr.injective
  ext j
  simp only [map_zero, PiLp.zero_apply]
  by_cases hj : j ∈ coloredObserved d k hd i
  · have hb : b j ∈ coloredEdgeSpace d k hd i :=
      (mem_observationIndices (scalarAdaptedBasis d k) (coloredEdgeSpace d k hd i) j).mp hj
    have hbfix := (mem_coloredEdgeSpace_iff d k hd i _).mp hb
    have hh := hu j hj
    change (observationMatrix (scalarAdaptedBasis d k) (coloredEdgeSpace d k hd i)).transpose.mulVec
      ((scalarAdaptedBasis d k).repr u) j = 0 at hh
    rw [observationMatrix_transpose_repr, OrthonormalBasis.repr_apply_apply] at hh
    rw [OrthonormalBasis.repr_apply_apply, ← coloredEdgeProjection_selfAdjoint, hbfix]
    exact hh
  · exact (observationBasis_mem_iff (scalarAdaptedBasis d k) (coloredEdgeSpace d k hd i) _).mp hp j hj

end GeneralizedBulk.Entropy.Channel
