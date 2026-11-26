import GeneralizedBulk.Graph.CanonicalSpectralData
import GeneralizedBulk.Graph.EigenfamilyPinning
import GeneralizedBulk.Graph.ProposalFiberVariance

/-! Measurable complete spectral data containing an optionally chosen actual
nontrivial unit eigenvector. Choices are made on finite graph spaces. -/
noncomputable section
open MeasureTheory Matrix
open scoped Classical BigOperators RealInnerProductSpace

namespace GeneralizedBulk.Graph.CanonicalSpectrum

variable {M d : ℕ}

structure NontrivialUnitGraphEigenvector (g : RegularGraph M d) where
  energy : ℝ
  vector : EuclideanSpace ℝ (Fin M)
  norm_one : ‖vector‖=1
  eigen : (g.val.adjMatrix ℝ).toEuclideanLin vector=energy • vector
  energy_ne_degree : energy ≠ d

theorem graphBasis_eigenLin (g : RegularGraph M d) (hM : 0 < M) (i : Fin M) :
    (g.val.adjMatrix ℝ).toEuclideanLin (graphBasis g hM i) =
      graphValue g i • graphBasis g hM i := by
  apply PiLp.ext
  intro v
  simpa only [Matrix.toEuclideanLin_apply,PiLp.smul_apply,Pi.smul_apply,smul_eq_mul] using
    congrFun (graphBasis_eigen g hM i) v

private def pinningWitness (g : RegularGraph M d) (hM : 0 < M)
    (q : NontrivialUnitGraphEigenvector g) :=
  exists_eigenbasis_pinning (g.val.adjMatrix ℝ).toEuclideanLin
    (Matrix.isHermitian_iff_isSymmetric.mp (hermitian g))
    (graphBasis g hM) (graphValue g) (graphBasis_eigenLin g hM)
    q.vector q.energy q.norm_one q.eigen

private def pinningIndex (g : RegularGraph M d) (hM : 0 < M)
    (q : NontrivialUnitGraphEigenvector g) : Fin M :=
  Classical.choose (pinningWitness g hM q)

private theorem pinningIndex_spec (g : RegularGraph M d) (hM : 0 < M)
    (q : NontrivialUnitGraphEigenvector g) :
    graphValue g (pinningIndex g hM q)=q.energy ∧
      eigenbasisPinning (graphBasis g hM) (pinningIndex g hM q) q.vector
        (pinningIndex g hM q)=q.vector ∧
      (∀ i,(g.val.adjMatrix ℝ).toEuclideanLin
        (eigenbasisPinning (graphBasis g hM) (pinningIndex g hM q) q.vector i)=
          graphValue g i • eigenbasisPinning (graphBasis g hM) (pinningIndex g hM q) q.vector i) ∧
      (∀ i,graphValue g i≠q.energy →
        eigenbasisPinning (graphBasis g hM) (pinningIndex g hM q) q.vector i=graphBasis g hM i) :=
  Classical.choose_spec (pinningWitness g hM q)

def selectedGraphBasis (g : RegularGraph M d) (hM : 0 < M)
    (selection : Option (NontrivialUnitGraphEigenvector g)) :
    OrthonormalBasis (Fin M) ℝ (EuclideanSpace ℝ (Fin M)) :=
  selection.elim (graphBasis g hM) (fun q =>
    eigenbasisPinning (graphBasis g hM) (pinningIndex g hM q) q.vector)

theorem selectedGraphBasis_first (g : RegularGraph M d) (hM : 0 < M)
    (selection : Option (NontrivialUnitGraphEigenvector g)) :
    selectedGraphBasis g hM selection ⟨0,hM⟩=constantVector M := by
  cases selection with
  | none => exact graphBasis_first g hM
  | some q =>
    change eigenbasisPinning (graphBasis g hM) (pinningIndex g hM q) q.vector ⟨0,hM⟩ = _
    rw [(pinningIndex_spec g hM q).2.2.2 _ (by
      rw [graphValue_first g hM]
      exact q.energy_ne_degree.symm)]
    exact graphBasis_first g hM

theorem selectedGraphBasis_eigen (g : RegularGraph M d) (hM : 0 < M)
    (selection : Option (NontrivialUnitGraphEigenvector g)) (i : Fin M) :
    g.val.adjMatrix ℝ *ᵥ (⇑(selectedGraphBasis g hM selection i)) =
      graphValue g i • (⇑(selectedGraphBasis g hM selection i)) := by
  cases selection with
  | none => exact graphBasis_eigen g hM i
  | some q =>
    exact congrArg (fun x : EuclideanSpace ℝ (Fin M) => ⇑x)
      ((pinningIndex_spec g hM q).2.2.1 i)

theorem selectedGraphBasis_contains (g : RegularGraph M d) (hM : 0 < M)
    (q : NontrivialUnitGraphEigenvector g) :
    ∃ j : Fin M, graphValue g j=q.energy ∧
      selectedGraphBasis g hM (some q) j=q.vector :=
  ⟨pinningIndex g hM q,(pinningIndex_spec g hM q).1,(pinningIndex_spec g hM q).2.1⟩

end GeneralizedBulk.Graph.CanonicalSpectrum

namespace GeneralizedBulk.Graph
open CanonicalSpectrum

def eigenfamilySpectralData (d : ℕ) (N : ℕ → ℕ) (hN : ∀ n,0 < N n)
    (hlim : Filter.Tendsto N Filter.atTop Filter.atTop)
    (selector : ∀ n,(g : RegularGraph (N n) d) → Option (NontrivialUnitGraphEigenvector g)) :
    External.RegularSpectralData d N (UniformEnsemble d N) :=
  { canonicalSpectralData d N hN hlim with
    eigenvector := fun n ω i => ⇑(selectedGraphBasis (ω n) (hN n) (selector n (ω n)) i)
    orthonormal := by
      intro n ω i j
      have h := orthonormal_iff_ite.mp (selectedGraphBasis (ω n) (hN n) (selector n (ω n))).orthonormal i j
      simpa only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Pi.star_apply,
        star_trivial,mul_comm] using h
    eigen_equation := fun n ω i v => congrFun (selectedGraphBasis_eigen (ω n) (hN n) (selector n (ω n)) i) v
    constant_eigenvector := by
      intro n ω v
      exact congrArg (fun x : EuclideanSpace ℝ (Fin (N n)) => x v)
        (selectedGraphBasis_first (ω n) (hN n) (selector n (ω n)))
    measurable_eigenvector := fun n i v =>
      (measurable_of_finite (fun g : RegularGraph (N n) d =>
        selectedGraphBasis g (hN n) (selector n g) i v)).comp (measurable_pi_apply n) }

theorem eigenfamilySpectralData_graph (d : ℕ) (N : ℕ → ℕ) (hN : ∀ n,0 < N n)
    (hlim : Filter.Tendsto N Filter.atTop Filter.atTop)
    (selector : ∀ n,(g : RegularGraph (N n) d) → Option (NontrivialUnitGraphEigenvector g))
    (n : ℕ) (ω : UniformEnsemble d N) :
    (eigenfamilySpectralData d N hN hlim selector).spectralRegularGraph n ω=ω n := by
  apply Subtype.ext
  apply SimpleGraph.ext
  funext v w
  apply propext
  change (ω n).val.adjMatrix ℝ v w=1 ↔ (ω n).val.Adj v w
  simp only [SimpleGraph.adjMatrix_apply]
  by_cases h : (ω n).val.Adj v w <;> simp [h]

theorem eigenfamilySpectralData_contains (d : ℕ) (N : ℕ → ℕ) (hN : ∀ n,0 < N n)
    (hlim : Filter.Tendsto N Filter.atTop Filter.atTop)
    (selector : ∀ n,(g : RegularGraph (N n) d) → Option (NontrivialUnitGraphEigenvector g))
    (n : ℕ) (ω : UniformEnsemble d N) (q : NontrivialUnitGraphEigenvector (ω n))
    (hq : selector n (ω n)=some q) :
    ∃ j : Fin (N n),
      (eigenfamilySpectralData d N hN hlim selector).eigenvalue n ω j=q.energy ∧
      (eigenfamilySpectralData d N hN hlim selector).eigenvector n ω j=⇑q.vector := by
  obtain ⟨j,hj,hvec⟩ := selectedGraphBasis_contains (ω n) (hN n) q
  refine ⟨j,hj,?_⟩
  change ⇑(selectedGraphBasis (ω n) (hN n) (selector n (ω n)) j)=⇑q.vector
  rw [hq,hvec]

end GeneralizedBulk.Graph
