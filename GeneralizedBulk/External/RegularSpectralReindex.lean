import GeneralizedBulk.ExternalInputs

/-! Literal strict-subsequence reindexing of the finite spectral model.
No BS/HY contract is strengthened or reindexed by this construction. -/
noncomputable section
open MeasureTheory Filter
namespace GeneralizedBulk.External.RegularSpectralData
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

def reindex (r : ℕ → ℕ) (hr : StrictMono r) : RegularSpectralData d (fun n => N (r n)) Ω where
  size_pos n := D.size_pos (r n)
  size_tendsto := D.size_tendsto.comp hr.tendsto_atTop
  adjacency n := D.adjacency (r n)
  eigenvalue n := D.eigenvalue (r n)
  eigenvector n := D.eigenvector (r n)
  neighbor n := D.neighbor (r n)
  symmetric n := D.symmetric (r n)
  diagonal_zero n := D.diagonal_zero (r n)
  entry_zero_one n := D.entry_zero_one (r n)
  regular n := D.regular (r n)
  neighbor_injective n := D.neighbor_injective (r n)
  neighbor_exact n := D.neighbor_exact (r n)
  orthonormal n := D.orthonormal (r n)
  eigen_equation n := D.eigen_equation (r n)
  ordered n := D.ordered (r n)
  constant_eigenvalue n := D.constant_eigenvalue (r n)
  constant_eigenvector n := D.constant_eigenvector (r n)
  measurable_adjacency n := D.measurable_adjacency (r n)
  measurable_eigenvalue n := D.measurable_eigenvalue (r n)
  measurable_eigenvector n := D.measurable_eigenvector (r n)
  measurable_neighbor n := D.measurable_neighbor (r n)

@[simp] theorem reindex_resolvent (r : ℕ → ℕ) (hr : StrictMono r)
    (n : ℕ) (ω : Ω) (z : ℂ) : (D.reindex r hr).resolvent n ω z=D.resolvent (r n) ω z := rfl

@[simp] theorem reindex_scalarResolvent (r : ℕ → ℕ) (hr : StrictMono r)
    (n : ℕ) (ω : Ω) (z : ℂ) : (D.reindex r hr).scalarResolvent n ω z=D.scalarResolvent (r n) ω z := rfl

end GeneralizedBulk.External.RegularSpectralData
