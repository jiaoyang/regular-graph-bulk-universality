import GeneralizedBulk.Entropy.ContinuousChannels
import GeneralizedBulk.Entropy.ObservationMixtureSymmetry

/-! Actual endpoint reversal and the observation coordinates used by Gaussian channels. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Channel
open GeneralizedBulk.Entropy.Hermite GeneralizedBulk.Entropy.Mehler

theorem endpointReversal_projection_commute (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1)
    (i : Fin d) (y : WhiteStar d) :
    endpointReversal d hd c i (edgeProjection d hd i y) =
      edgeProjection d hd i (endpointReversal d hd c i y) := by
  let v := directionA d hd c i - directionB d hd c i
  have hv : edgeProjection d hd i v = v := by
    simp only [v, map_sub, edgeProjection_directionA, edgeProjection_directionB]
  rw [endpointReversal_formula d hd c hc i, endpointReversal_formula d hd c hc i,
    map_sub, map_smul]
  change edgeProjection d hd i y - (@inner ℝ (WhiteStar d) _ v (edgeProjection d hd i y)) • v =
    edgeProjection d hd i y - (@inner ℝ (WhiteStar d) _ v y) • edgeProjection d hd i v
  rw [← edgeProjection_selfAdjoint, hv]

theorem coloredReversal_projection_commute (d k : ℕ) (hd : 2 ≤ d) (c : Fin k → ℝ)
    (hc : ∀ a, |c a| < 1) (i : Fin d) (y : ColoredStar d k) :
    coloredReversal d k hd c i (coloredEdgeProjection d k hd i y) =
      coloredEdgeProjection d k hd i (coloredReversal d k hd c i y) := by
  apply (WithLp.equiv 2 _).injective
  funext a
  exact endpointReversal_projection_commute d hd (c a) (hc a) i (y a)

theorem coloredReversal_involutive (d k : ℕ) (hd : 2 ≤ d) (c : Fin k → ℝ) (i : Fin d) :
    Function.Involutive (coloredReversal d k hd c i) := by
  intro y
  apply (WithLp.equiv 2 _).injective
  funext a
  exact endpointReversal_involutive d hd (c a) i (y a)

def coloredObservationCoordinates (d k : ℕ) (hd : 2 ≤ d) (i : Fin d) :
    ColoredStar d k ≃L[ℝ] (ScalarCoordinate d k → ℝ) :=
  (observationBasis (scalarAdaptedBasis d k) (coloredEdgeSpace d k hd i)).repr.toContinuousLinearEquiv.trans
    (WithLp.linearEquiv 2 ℝ (ScalarCoordinate d k → ℝ)).toContinuousLinearEquiv

theorem coloredObservationCoordinates_eq (d k : ℕ) (hd : 2 ≤ d) (i : Fin d) (x : ColoredStar d k) :
    coloredObservationCoordinates d k hd i x =
      (coloredObservationMatrix d k hd i).transpose.mulVec (scalarCoordinates d k x) :=
  (observationMatrix_transpose_repr (scalarAdaptedBasis d k) (coloredEdgeSpace d k hd i) x).symm

theorem coloredObservationCoordinates_projection (d k : ℕ) (hd : 2 ≤ d) (i : Fin d) (x : ColoredStar d k) :
    coloredObservationCoordinates d k hd i (coloredEdgeProjection d k hd i x) =
      coordinateProjection (coloredObserved d k hd i) (coloredObservationCoordinates d k hd i x) := by
  funext j
  by_cases hj : j ∈ coloredObserved d k hd i
  · have h := colored_discarded_coordinates d k hd i x j hj
    rw [← coloredObservationCoordinates_eq, map_sub] at h
    simp only [Pi.sub_apply] at h
    simp only [coordinateProjection, hj, ↓reduceIte]
    linarith
  · have hm : coloredEdgeProjection d k hd i x ∈ coloredEdgeSpace d k hd i := ⟨x, rfl⟩
    have h := (observationBasis_mem_iff (scalarAdaptedBasis d k) (coloredEdgeSpace d k hd i) _).mp hm j hj
    simpa only [coordinateProjection, hj, ↓reduceIte] using h

def coloredObservationReversal (d k : ℕ) (hd : 2 ≤ d) (c : Fin k → ℝ) (i : Fin d) :
    Matrix (ScalarCoordinate d k) (ScalarCoordinate d k) ℝ :=
  isometryMatrix (observationBasis (scalarAdaptedBasis d k) (coloredEdgeSpace d k hd i))
    (coloredReversal d k hd c i)

theorem coloredObservationReversal_orthogonal (d k : ℕ) (hd : 2 ≤ d) (c : Fin k → ℝ) (i : Fin d) :
    coloredObservationReversal d k hd c i * (coloredObservationReversal d k hd c i).transpose = 1 :=
  isometryMatrix_orthogonal _ _

theorem coloredObservationReversal_action (d k : ℕ) (hd : 2 ≤ d) (c : Fin k → ℝ) (i : Fin d) (x : ColoredStar d k) :
    (coloredObservationReversal d k hd c i).mulVec (coloredObservationCoordinates d k hd i x) =
      coloredObservationCoordinates d k hd i (coloredReversal d k hd c i x) :=
  isometryMatrix_repr _ _ _

theorem coloredObservationReversal_involutive (d k : ℕ) (hd : 2 ≤ d) (c : Fin k → ℝ) (i : Fin d)
    (x : ScalarCoordinate d k → ℝ) :
    (coloredObservationReversal d k hd c i).mulVec ((coloredObservationReversal d k hd c i).mulVec x) = x := by
  obtain ⟨y, rfl⟩ := (coloredObservationCoordinates d k hd i).surjective x
  rw [coloredObservationReversal_action, coloredObservationReversal_action,
    coloredReversal_involutive d k hd c i y]

theorem coloredObservationReversal_projection (d k : ℕ) (hd : 2 ≤ d) (c : Fin k → ℝ)
    (hc : ∀ a, |c a| < 1) (i : Fin d) (x : ScalarCoordinate d k → ℝ) :
    coordinateProjection (coloredObserved d k hd i) ((coloredObservationReversal d k hd c i).mulVec x) =
      (coloredObservationReversal d k hd c i).mulVec (coordinateProjection (coloredObserved d k hd i) x) := by
  obtain ⟨y, rfl⟩ := (coloredObservationCoordinates d k hd i).surjective x
  rw [coloredObservationReversal_action, ← coloredObservationCoordinates_projection,
    ← coloredObservationCoordinates_projection, coloredObservationReversal_action,
    coloredReversal_projection_commute d k hd c hc i y]

theorem coloredObservationReversal_coordinates (d k : ℕ) (hd : 2 ≤ d) (c : Fin k → ℝ) (i : Fin d)
    (x : ScalarCoordinate d k → ℝ) :
    (coloredObservationMatrix d k hd i).transpose.mulVec ((coloredReversalMatrix d k hd c i).mulVec x) =
      (coloredObservationReversal d k hd c i).mulVec ((coloredObservationMatrix d k hd i).transpose.mulVec x) := by
  obtain ⟨y, rfl⟩ := (scalarCoordinates d k).surjective x
  have h := isometryMatrix_repr (scalarAdaptedBasis d k) (coloredReversal d k hd c i) y
  change (coloredReversalMatrix d k hd c i).mulVec (scalarCoordinates d k y) = scalarCoordinates d k _ at h
  rw [h, ← coloredObservationCoordinates_eq, ← coloredObservationCoordinates_eq,
    coloredObservationReversal_action]

end GeneralizedBulk.Entropy.Channel
