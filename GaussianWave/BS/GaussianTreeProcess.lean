import GaussianWave.BS.BallProcessExtension
import GaussianWave.BS.GaussianBallCovariance

/-! An actual infinite Gaussian reference law, constructed from the
already proved consistent independent-noise finite ball laws. -/
noncomputable section
open MeasureTheory Set
open scoped Topology BigOperators Classical
namespace GaussianWave.BS

theorem exists_gaussianTreeProcessLaw (m : ℕ) (energy : ℝ) :
    ∃ Q : ProbabilityMeasure (RegularTreeVertex (m + 2) → ℝ), ∀ n,
      Measure.map (fun x : RegularTreeVertex (m + 2) → ℝ =>
        fun v => x (vertexBallEmbedding (m + 2) n v)) (Q : Measure _) = vertexGaussianBallLaw m n energy := by
  exact exists_tree_processLaw_of_ball_marginals m
    (fun n => ⟨vertexGaussianBallLaw m n energy, inferInstance⟩)
    (fun n => vertexGaussianBallLaw_consistent m n energy)

def gaussianTreeProcessLaw (m : ℕ) (energy : ℝ) : ProbabilityMeasure (RegularTreeVertex (m + 2) → ℝ) :=
  Classical.choose (exists_gaussianTreeProcessLaw m energy)

theorem gaussianTreeProcessLaw_ball (m n : ℕ) (energy : ℝ) :
    Measure.map (fun x : RegularTreeVertex (m + 2) → ℝ =>
      fun v => x (vertexBallEmbedding (m + 2) n v))
      (gaussianTreeProcessLaw m energy : Measure _) = vertexGaussianBallLaw m n energy :=
  Classical.choose_spec (exists_gaussianTreeProcessLaw m energy) n

theorem gaussianTreeProcessLaw_finite_linearImage
    (m : ℕ) (energy : ℝ) {J : Type*} [Fintype J]
    (site : J → RegularTreeVertex (m + 2)) :
    ∃ (K : Type) (_ : Fintype K) (L : Matrix J K ℝ),
      Measure.map (fun x : RegularTreeVertex (m + 2) → ℝ => fun j => x (site j))
        (gaussianTreeProcessLaw m energy : Measure _) = linearImageGaussian L := by
  let S : Finset (RegularTreeVertex (m + 2)) := Finset.univ.image site
  let n := finiteTreeDepth S
  let lift : J → VertexBallVertex (m + 2) n := fun j =>
    treeBallIndexOfDepth (m + 2) n (site j)
      (depth_le_finiteTreeDepth S ⟨site j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩)
  have hlift (j) : vertexBallEmbedding (m + 2) n (lift j) = site j := treeBallIndexOfDepth_spec _ _ _ _
  let L : Matrix J (VertexGaussianInput m n) ℝ := fun j a => vertexGaussianMatrix m n energy (lift j) a
  refine ⟨VertexGaussianInput m n, inferInstance, L, ?_⟩
  let T := fun x : VertexBallVertex (m + 2) n → ℝ => fun j => x (lift j)
  have hT : Measurable T := measurable_pi_lambda _ (fun j => measurable_pi_apply _)
  have hB : Measurable (fun x : RegularTreeVertex (m + 2) → ℝ =>
      fun v => x (vertexBallEmbedding (m + 2) n v)) :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have hcomp : (fun x : RegularTreeVertex (m + 2) → ℝ => fun j => x (site j)) =
      T ∘ (fun x : RegularTreeVertex (m + 2) → ℝ => fun v => x (vertexBallEmbedding (m + 2) n v)) := by
    funext x j
    exact congrArg x (hlift j).symm
  rw [hcomp, ← Measure.map_map hT hB, gaussianTreeProcessLaw_ball,
    vertexGaussianBallLaw_eq_linearImage]
  unfold linearImageGaussian
  rw [Measure.map_map hT (measurable_finiteMatrixAction (vertexGaussianMatrix m n energy))]
  rfl

/-- Every finite window of the constructed whole law is jointly Gaussian,
proved through an actual finite linear Gaussian factor. -/
theorem gaussianTreeProcessLaw_finite_gaussian
    (m : ℕ) (energy : ℝ) {J : Type*} [Fintype J]
    (site : J → RegularTreeVertex (m + 2)) :
    CenteredGaussianLaw (Measure.map
      (fun x : RegularTreeVertex (m + 2) → ℝ => fun j => x (site j))
      (gaussianTreeProcessLaw m energy : Measure _)) := by
  obtain ⟨K, hK, L, hL⟩ := gaussianTreeProcessLaw_finite_linearImage m energy site
  letI := hK
  rw [hL]
  refine ⟨inferInstance, L * L.transpose, ?_, ?_, linearImageGaussian_characteristic L⟩
  · intro i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, mul_comm]
  · intro t
    rw [finiteCovarianceQuadratic_gram]
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

end GaussianWave.BS
