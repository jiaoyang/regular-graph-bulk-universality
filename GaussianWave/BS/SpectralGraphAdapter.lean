import GaussianWave.Covariance
import GaussianWave.BS.Reused.Graph.ColorSampling

/-! The finite spectral data determine an actual labeled simple regular
graph. Its chosen neighbor ordering differs from the canonical counting
ordering by a proved finite permutation. -/
noncomputable section
open scoped BigOperators Classical
namespace GaussianWave.RegularEigenData
open BS.Reused.Graph BS.Reused.Graph.Configuration
variable {d N c : ℕ} (D : RegularEigenData d N c)

def simpleGraph : SimpleGraph (Fin N) where
  Adj v w := D.adjacency v w = 1
  symm v w h := (D.symmetric w v).trans h
  loopless v h := by
    change D.adjacency v v = 1 at h
    rw [D.diagonal_zero] at h
    norm_num at h

def neighborGraphEquiv (v : Fin N) : Fin d ≃ (D.simpleGraph).neighborSet v :=
  Equiv.ofBijective (fun j => ⟨D.neighbor v j, (D.neighbor_exact v _).mpr ⟨j, rfl⟩⟩)
    ⟨fun a b h => D.neighbor_injective v (congrArg Subtype.val h),
      fun w => by
        obtain ⟨j, hj⟩ := (D.neighbor_exact v w).mp w.property
        exact ⟨j, Subtype.ext hj⟩⟩

theorem simpleGraph_regular : D.simpleGraph.IsRegularOfDegree d := by
  intro v
  rw [← SimpleGraph.card_neighborSet_eq_degree,
    ← Fintype.card_congr (D.neighborGraphEquiv v), Fintype.card_fin]

def regularGraph : RegularGraph N d := ⟨D.simpleGraph, D.simpleGraph_regular⟩

def canonicalNeighborRelabel (v : Fin N) : Equiv.Perm (Fin d) :=
  (D.neighborGraphEquiv v).trans (canonicalPortLabeling D.regularGraph v).symm

theorem graphNeighbor_relabel (v : Fin N) (j : Fin d) :
    graphNeighbor D.regularGraph v (D.canonicalNeighborRelabel v j) = D.neighbor v j := by
  exact congrArg Subtype.val ((canonicalPortLabeling D.regularGraph v).apply_symm_apply
    (D.neighborGraphEquiv v j))

theorem graph_eigenrelation (a : Fin c) :
    ∀ v, (∑ j, D.eigenvector a (graphNeighbor D.regularGraph v j)) =
      D.eigenvalue a * D.eigenvector a v := by
  intro v
  have he := Equiv.sum_comp (D.canonicalNeighborRelabel v)
    (fun j => D.eigenvector a (graphNeighbor D.regularGraph v j))
  simp only [D.graphNeighbor_relabel] at he
  rw [← he]
  exact D.eigenvector_neighbor_sum a v

theorem graph_normalized_eigenrelation (a : Fin c) :
    ∀ v, (∑ j, Real.sqrt N * D.eigenvector a (graphNeighbor D.regularGraph v j)) =
      D.eigenvalue a * (Real.sqrt N * D.eigenvector a v) := by
  intro v
  rw [← Finset.mul_sum, D.graph_eigenrelation a v]
  ring

end GaussianWave.RegularEigenData
