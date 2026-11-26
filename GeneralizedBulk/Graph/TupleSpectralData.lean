import GeneralizedBulk.Graph.EigenfamilyTuplePinning
import GeneralizedBulk.Graph.EigenfamilySpectralData
import GeneralizedBulk.Graph.UniformCandidateBS
import GeneralizedBulk.BS.SpectralAdapter

/-! Complete measurable spectral data containing a chosen finite orthonormal
eigenfamily, including its exact neighbor enumeration. All choices occur on
the finite graph space, so arbitrary eigenspace rotations are covered. -/
noncomputable section
open MeasureTheory Matrix
open scoped Classical BigOperators RealInnerProductSpace
namespace GeneralizedBulk.Graph.CanonicalSpectrum

variable {M d k : ℕ}

structure NontrivialGraphEigenfamily (g : RegularGraph M d) (k : ℕ) where
  data : GraphEigenCandidate d M k g
  nontrivial : ∀ a, data.val.eigenvalue a ≠ d

def candidateTupleVector {g : RegularGraph M d} (A : GraphEigenCandidate d M k g)
    (a : Fin k) : EuclideanSpace ℝ (Fin M) :=
  (WithLp.equiv 2 (Fin M → ℝ)).symm (A.val.eigenvector a)

theorem candidateTupleVector_orthonormal {g : RegularGraph M d}
    (A : GraphEigenCandidate d M k g) : Orthonormal ℝ (candidateTupleVector A) := by
  rw [orthonormal_iff_ite]
  intro a b
  simpa only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Pi.star_apply,
    star_trivial,candidateTupleVector,mul_comm] using A.val.orthonormal a b

theorem candidateTupleVector_eigen {g : RegularGraph M d}
    (A : GraphEigenCandidate d M k g) (a : Fin k) :
    (g.val.adjMatrix ℝ).toEuclideanLin (candidateTupleVector A a) =
      A.val.eigenvalue a • candidateTupleVector A a := by
  apply PiLp.ext
  intro v
  change (∑ w,g.val.adjMatrix ℝ v w*A.val.eigenvector a w) =
    A.val.eigenvalue a*A.val.eigenvector a v
  simpa only [A.property] using A.val.eigen_equation a v

private def tuplePinningWitness (g : RegularGraph M d) (hM : 0 < M)
    (q : NontrivialGraphEigenfamily g k) :=
  exists_eigenbasis_pinning_family (g.val.adjMatrix ℝ).toEuclideanLin
    (Matrix.isHermitian_iff_isSymmetric.mp (hermitian g))
    (graphBasis g hM) (graphValue g) (graphBasis_eigenLin g hM)
    (candidateTupleVector q.data) q.data.val.eigenvalue
    (candidateTupleVector_orthonormal q.data) (candidateTupleVector_eigen q.data)

private def tuplePinnedBasis (g : RegularGraph M d) (hM : 0 < M)
    (q : NontrivialGraphEigenfamily g k) :
    OrthonormalBasis (Fin M) ℝ (EuclideanSpace ℝ (Fin M)) :=
  Classical.choose (tuplePinningWitness g hM q)

private def tuplePinnedIndex (g : RegularGraph M d) (hM : 0 < M)
    (q : NontrivialGraphEigenfamily g k) : Fin k → Fin M :=
  Classical.choose (Classical.choose_spec (tuplePinningWitness g hM q))

private theorem tuplePinned_spec (g : RegularGraph M d) (hM : 0 < M)
    (q : NontrivialGraphEigenfamily g k) :
    Function.Injective (tuplePinnedIndex g hM q) ∧
      (∀ r,graphValue g (tuplePinnedIndex g hM q r)=q.data.val.eigenvalue r) ∧
      (∀ r,tuplePinnedBasis g hM q (tuplePinnedIndex g hM q r)=candidateTupleVector q.data r) ∧
      (∀ i,(g.val.adjMatrix ℝ).toEuclideanLin (tuplePinnedBasis g hM q i)=
        graphValue g i • tuplePinnedBasis g hM q i) ∧
      (∀ i,(∀ r,graphValue g i≠q.data.val.eigenvalue r) →
        tuplePinnedBasis g hM q i=graphBasis g hM i) :=
  Classical.choose_spec (Classical.choose_spec (tuplePinningWitness g hM q))

def selectedTupleBasis (g : RegularGraph M d) (hM : 0 < M)
    (selection : Option (NontrivialGraphEigenfamily g k)) :
    OrthonormalBasis (Fin M) ℝ (EuclideanSpace ℝ (Fin M)) :=
  selection.elim (graphBasis g hM) (tuplePinnedBasis g hM)

theorem selectedTupleBasis_first (g : RegularGraph M d) (hM : 0 < M)
    (selection : Option (NontrivialGraphEigenfamily g k)) :
    selectedTupleBasis g hM selection ⟨0,hM⟩=constantVector M := by
  cases selection with
  | none => exact graphBasis_first g hM
  | some q =>
    change tuplePinnedBasis g hM q ⟨0,hM⟩ = _
    rw [(tuplePinned_spec g hM q).2.2.2.2 _ (by
      intro r
      rw [graphValue_first g hM]
      exact (q.nontrivial r).symm)]
    exact graphBasis_first g hM

theorem selectedTupleBasis_eigen (g : RegularGraph M d) (hM : 0 < M)
    (selection : Option (NontrivialGraphEigenfamily g k)) (i : Fin M) :
    g.val.adjMatrix ℝ *ᵥ (⇑(selectedTupleBasis g hM selection i)) =
      graphValue g i • (⇑(selectedTupleBasis g hM selection i)) := by
  cases selection with
  | none => exact graphBasis_eigen g hM i
  | some q =>
    exact congrArg (fun x : EuclideanSpace ℝ (Fin M) => ⇑x)
      ((tuplePinned_spec g hM q).2.2.2.1 i)

def selectedTupleNeighbor (g : RegularGraph M d)
    (selection : Option (NontrivialGraphEigenfamily g k)) : Fin M → Fin d → Fin M :=
  selection.elim (fun v j => graphNeighbor g v j) (fun q => q.data.val.neighbor)

end GeneralizedBulk.Graph.CanonicalSpectrum

namespace GeneralizedBulk.Graph
open CanonicalSpectrum

def tupleSpectralData (d k : ℕ) (N : ℕ → ℕ) (hN : ∀ n,0<N n)
    (hlim : Filter.Tendsto N Filter.atTop Filter.atTop)
    (selector : ∀ n,(g : RegularGraph (N n) d) → Option (NontrivialGraphEigenfamily g k)) :
    External.RegularSpectralData d N (UniformEnsemble d N) :=
  { canonicalSpectralData d N hN hlim with
    eigenvector := fun n ω i => ⇑(selectedTupleBasis (ω n) (hN n) (selector n (ω n)) i)
    neighbor := fun n ω => selectedTupleNeighbor (ω n) (selector n (ω n))
    orthonormal := by
      intro n ω i j
      have h := orthonormal_iff_ite.mp (selectedTupleBasis (ω n) (hN n) (selector n (ω n))).orthonormal i j
      simpa only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Pi.star_apply,star_trivial,mul_comm] using h
    eigen_equation := fun n ω i v => congrFun (selectedTupleBasis_eigen (ω n) (hN n) (selector n (ω n)) i) v
    constant_eigenvector := by
      intro n ω v
      exact congrArg (fun x : EuclideanSpace ℝ (Fin (N n)) => x v)
        (selectedTupleBasis_first (ω n) (hN n) (selector n (ω n)))
    neighbor_injective := by
      intro n ω v
      cases hs : selector n (ω n) with
      | none => exact (canonicalSpectralData d N hN hlim).neighbor_injective n ω v
      | some q => exact q.data.val.neighbor_injective v
    neighbor_exact := by
      intro n ω v w
      cases hs : selector n (ω n) with
      | none => exact (canonicalSpectralData d N hN hlim).neighbor_exact n ω v w
      | some q =>
        change (ω n).val.adjMatrix ℝ v w=1 ↔ ∃ j,q.data.val.neighbor v j=w
        simpa only [q.data.property] using q.data.val.neighbor_exact v w
    measurable_eigenvector := fun n i v =>
      (measurable_of_finite (fun g : RegularGraph (N n) d =>
        selectedTupleBasis g (hN n) (selector n g) i v)).comp (measurable_pi_apply n)
    measurable_neighbor := fun n v j =>
      (measurable_of_finite (fun g : RegularGraph (N n) d =>
        selectedTupleNeighbor g (selector n g) v j)).comp (measurable_pi_apply n) }

theorem tupleSpectralData_graph (d k : ℕ) (N : ℕ → ℕ) (hN : ∀ n,0<N n)
    (hlim : Filter.Tendsto N Filter.atTop Filter.atTop)
    (selector : ∀ n,(g : RegularGraph (N n) d) → Option (NontrivialGraphEigenfamily g k))
    (n : ℕ) (ω : UniformEnsemble d N) :
    (tupleSpectralData d k N hN hlim selector).spectralRegularGraph n ω=ω n := by
  apply Subtype.ext
  apply SimpleGraph.ext
  funext v w
  apply propext
  change (ω n).val.adjMatrix ℝ v w=1 ↔ (ω n).val.Adj v w
  by_cases h : (ω n).val.Adj v w <;> simp [SimpleGraph.adjMatrix_apply,h]

theorem tupleSpectralData_contains (d k : ℕ) (N : ℕ → ℕ) (hN : ∀ n,0<N n)
    (hlim : Filter.Tendsto N Filter.atTop Filter.atTop)
    (selector : ∀ n,(g : RegularGraph (N n) d) → Option (NontrivialGraphEigenfamily g k))
    (n : ℕ) (ω : UniformEnsemble d N) (q : NontrivialGraphEigenfamily (ω n) k)
    (hq : selector n (ω n)=some q) :
    ∃ f : Fin k → Fin (N n),Function.Injective f ∧
      (∀ a,(tupleSpectralData d k N hN hlim selector).eigenvalue n ω (f a)=q.data.val.eigenvalue a) ∧
      (∀ a,(tupleSpectralData d k N hN hlim selector).eigenvector n ω (f a)=q.data.val.eigenvector a) ∧
      (tupleSpectralData d k N hN hlim selector).neighbor n ω=q.data.val.neighbor := by
  refine ⟨tuplePinnedIndex (ω n) (hN n) q,(tuplePinned_spec (ω n) (hN n) q).1,
    (tuplePinned_spec (ω n) (hN n) q).2.1,?_,?_⟩
  · intro a
    change ⇑(selectedTupleBasis (ω n) (hN n) (selector n (ω n))
      (tuplePinnedIndex (ω n) (hN n) q a)) = q.data.val.eigenvector a
    rw [hq]
    exact congrArg (fun x : EuclideanSpace ℝ (Fin (N n)) => ⇑x)
      ((tuplePinned_spec (ω n) (hN n) q).2.2.1 a)
  · change selectedTupleNeighbor (ω n) (selector n (ω n)) = q.data.val.neighbor
    rw [hq]
    rfl

end GeneralizedBulk.Graph
