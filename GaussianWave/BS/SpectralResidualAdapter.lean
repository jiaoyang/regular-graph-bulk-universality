import GaussianWave.BS.SpectralGraphAdapter
import GaussianWave.BS.LiftedApproximateEigenrelations
import GaussianWave.AlmostEigenvectors

/-! Exact spectral-matrix to actual-cover residual and moment identities.
The arbitrary signals need not be orthogonal or eigenvectors. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianWave.RegularEigenData
open BS BS.Reused.Graph BS.Reused.Graph.Configuration

variable {d N c : ℕ} (D : RegularEigenData d N c)

include D

theorem graph_neighbor_sum (v : Fin N) (f : Fin N → ℝ) :
    (∑ j, f (graphNeighbor D.regularGraph v j)) = ∑ w, D.adjacency v w * f w := by
  have he := Equiv.sum_comp (D.canonicalNeighborRelabel v)
    (fun j => f (graphNeighbor D.regularGraph v j))
  simp only [D.graphNeighbor_relabel] at he
  rw [← he]
  exact D.sum_neighbor v f

theorem graphEigenResidual_sqrtScale (energy : ℝ) (q : Fin N → ℝ) (v : Fin N) :
    graphEigenResidual D.regularGraph energy (fun w => Real.sqrt N * q w) v =
      Real.sqrt N * eigenResidual D.adjacency energy q v := by
  unfold graphEigenResidual eigenResidual
  rw [← Finset.mul_sum, D.graph_neighbor_sum]
  ring

theorem normalized_signal_root_second (q : Fin N → ℝ) :
    (N : ℝ)⁻¹ * ∑ v, (Real.sqrt N * q v) ^ 2 = squareMass q := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt D.size_pos)
  simp_rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
  rw [← Finset.mul_sum, inv_mul_cancel_left₀ hN]
  rfl

theorem normalized_signal_residual_second (energy : ℝ) (q : Fin N → ℝ) :
    (N : ℝ)⁻¹ * ∑ v, graphEigenResidual D.regularGraph energy
      (fun w => Real.sqrt N * q w) v ^ 2 = squareMass (eigenResidual D.adjacency energy q) := by
  simp_rw [D.graphEigenResidual_sqrtScale]
  exact D.normalized_signal_root_second _

theorem eigenvector_commonEnergy_residual_square (i : Fin c) (energy : ℝ) :
    squareMass (eigenResidual D.adjacency energy (D.eigenvector i)) = (D.eigenvalue i - energy) ^ 2 := by
  have he : eigenResidual D.adjacency energy (D.eigenvector i) =
      fun v => (D.eigenvalue i - energy) * D.eigenvector i v := by
    funext v
    unfold eigenResidual
    rw [D.eigen_equation]
    ring
  have hn : (∑ v, D.eigenvector i v ^ 2) = 1 := by
    simpa only [if_pos rfl, pow_two] using D.orthonormal i i
  rw [he, squareMass]
  simp_rw [mul_pow]
  rw [← Finset.mul_sum, hn, mul_one]

end GaussianWave.RegularEigenData

namespace GaussianWave.RegularEigenData
open BS BS.Reused.Graph BS.Reused.Graph.Configuration
variable {m N c r : ℕ} (D : RegularEigenData (m + 2) N c)

theorem integral_lifted_normalized_signal_second
    (q : Fin r → Fin N → ℝ) (a : Fin r) (u : RegularTreeVertex (m + 2)) :
    (∫ x, x (a, u) ^ 2 ∂uniformLiftedTreeLaw D.regularGraph D.size_pos
      (fun b v => Real.sqrt N * q b v)) = squareMass (q a) := by
  rw [integral_uniformLiftedTreeLaw_coordinate D.regularGraph D.size_pos
    (fun b v => Real.sqrt N * q b v) a u (fun x => x ^ 2) (by fun_prop)]
  exact D.normalized_signal_root_second (q a)

theorem integral_lifted_normalized_signal_residual_sq
    (energy : Fin r → ℝ) (q : Fin r → Fin N → ℝ) (a : Fin r)
    (u : RegularTreeVertex (m + 2)) :
    (∫ x, treeEigenResidual (m + 2) r energy a u x ^ 2
      ∂uniformLiftedTreeLaw D.regularGraph D.size_pos (fun b v => Real.sqrt N * q b v)) =
      squareMass (eigenResidual D.adjacency (energy a) (q a)) := by
  rw [integral_uniformLiftedTreeLaw_residual_sq]
  exact D.normalized_signal_residual_second (energy a) (q a)

theorem integral_lifted_eigenvector_commonEnergy_residual_sq
    (selection : Fin r → Fin c) (energy : Fin r → ℝ) (a : Fin r)
    (u : RegularTreeVertex (m + 2)) :
    (∫ x, treeEigenResidual (m + 2) r energy a u x ^ 2
      ∂uniformLiftedTreeLaw D.regularGraph D.size_pos
        (fun b v => Real.sqrt N * D.eigenvector (selection b) v)) =
      (D.eigenvalue (selection a) - energy a) ^ 2 := by
  rw [D.integral_lifted_normalized_signal_residual_sq, D.eigenvector_commonEnergy_residual_square]

end GaussianWave.RegularEigenData
