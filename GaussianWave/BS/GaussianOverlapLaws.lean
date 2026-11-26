import GaussianWave.BS.GaussianCoverDistances

/-!
# Actual Gaussian reference laws on the overlap windows

These are literal coordinate restrictions of the constructed Gaussian ball
laws.  Their identification uses the proved radial kernels and the proved
distance-preserving physical embeddings.
-/
noncomputable section
open MeasureTheory
namespace GaussianWave.BS

theorem linearImageGaussian_rowRestriction {I J K : Type*} [Fintype I]
    (L : Matrix J I ℝ) (g : K → J) :
    Measure.map (fun x : J → ℝ => fun k => x (g k)) (linearImageGaussian L) =
      linearImageGaussian (fun k i => L (g k) i) := by
  unfold linearImageGaussian
  rw [Measure.map_map (by fun_prop) (measurable_finiteMatrixAction L)]
  rfl

theorem linearImageGaussian_eq_of_gram_eq {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    (L : Matrix K I ℝ) (M : Matrix K J ℝ) (h : L * L.transpose = M * M.transpose) :
    linearImageGaussian L = linearImageGaussian M := by
  apply measure_eq_of_linear_characteristic
  intro t
  exact ((linearImageGaussian_characteristic L) t).trans
    (h ▸ ((linearImageGaussian_characteristic M) t).symm)

theorem vertexGaussianBallLaw_edge_window (m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) (a : Fin (m + 2)) :
    Measure.map (fun x => fun v => x (edgeInVertexCover m k a v))
      (vertexGaussianBallLaw m (k + 1) energy) = edgeGaussianBallLaw m (k + 1) energy := by
  have hne : energy ≠ (m + 2 : ℝ) := ne_of_lt ((le_abs_self energy).trans_lt he)
  rw [vertexGaussianBallLaw_eq_waveFactor m (k + 1) energy hne,
    edgeGaussianBallLaw_eq_waveFactor, linearImageGaussian_rowRestriction]
  apply linearImageGaussian_eq_of_gram_eq
  ext v w
  have hv := congrArg (fun M => M (edgeInVertexCover m k a v) (edgeInVertexCover m k a w))
    (vertexWaveCoefficient_gram m (k + 1) energy he)
  have he' := congrArg (fun M => M v w) (edgeWaveCoefficient_gram m (k + 1) energy he)
  change (∑ i, vertexWaveCoefficient m (k + 1) energy (edgeInVertexCover m k a v) i *
    vertexWaveCoefficient m (k + 1) energy (edgeInVertexCover m k a w) i) = _
  rw [show (∑ i, vertexWaveCoefficient m (k + 1) energy (edgeInVertexCover m k a v) i *
      vertexWaveCoefficient m (k + 1) energy (edgeInVertexCover m k a w) i) =
      sphericalCovariance (m + 2) energy (edgeBallDistance m (k + 1) v w) by
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, edgeInVertexCover_distance] using hv]
  exact he'.symm

theorem edgeGaussianBallLaw_vertex_window (m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) (b : Bool) :
    Measure.map (fun x => fun v => x (vertexInEdgeCover m k b v))
      (edgeGaussianBallLaw m (k + 1) energy) = vertexGaussianBallLaw m k energy := by
  have hne : energy ≠ (m + 2 : ℝ) := ne_of_lt ((le_abs_self energy).trans_lt he)
  rw [edgeGaussianBallLaw_eq_waveFactor,
    vertexGaussianBallLaw_eq_waveFactor m k energy hne, linearImageGaussian_rowRestriction]
  apply linearImageGaussian_eq_of_gram_eq
  ext v w
  have he' := congrArg (fun M => M (vertexInEdgeCover m k b v) (vertexInEdgeCover m k b w))
    (edgeWaveCoefficient_gram m (k + 1) energy he)
  have hv := congrArg (fun M => M v w) (vertexWaveCoefficient_gram m k energy he)
  change (∑ i, edgeWaveCoefficient m (k + 1) energy (vertexInEdgeCover m k b v) i *
    edgeWaveCoefficient m (k + 1) energy (vertexInEdgeCover m k b w) i) = _
  rw [show (∑ i, edgeWaveCoefficient m (k + 1) energy (vertexInEdgeCover m k b v) i *
      edgeWaveCoefficient m (k + 1) energy (vertexInEdgeCover m k b w) i) =
      sphericalCovariance (m + 2) energy (vertexBallDistance m k v w) by
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, vertexInEdgeCover_distance] using he']
  exact hv.symm

end GaussianWave.BS
