import GeneralizedBulk.Graph.CanonicalEigenbasis
import GeneralizedBulk.Graph.UniformSwitching
import GeneralizedBulk.ExternalInputs

/-! Measurable, complete spectral data for the literal labelled graph ensemble.
All choices are on finite graph spaces. The prescribed constant first mode
is valid without connectedness or a simple-spectrum assumption. -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Matrix
open scoped BigOperators Classical RealInnerProductSpace Topology

namespace GeneralizedBulk.Graph.CanonicalSpectrum

variable {M d : ℕ}

def hermitian (g : RegularGraph M d) : (g.val.adjMatrix ℝ).IsHermitian := by
  simpa only [Matrix.IsHermitian, Matrix.conjTranspose, star_trivial] using
    g.val.isSymm_adjMatrix (α := ℝ)

def constantVector (M : ℕ) : EuclideanSpace ℝ (Fin M) :=
  (WithLp.equiv 2 _).symm (fun _ => (Real.sqrt M)⁻¹)

theorem constantVector_norm (hM : 0 < M) : ‖constantVector M‖ = 1 := by
  have hs : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hM)
  have hsq : ‖constantVector M‖^2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    change (∑ _i : Fin M, (Real.sqrt (M : ℝ))⁻¹ * (Real.sqrt (M : ℝ))⁻¹) = 1
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have he := Real.sq_sqrt (Nat.cast_nonneg M)
    field_simp
  nlinarith [norm_nonneg (constantVector M)]

theorem constantVector_eigen (g : RegularGraph M d) :
    (g.val.adjMatrix ℝ).toEuclideanLin (constantVector M) =
      (d : ℝ) • constantVector M := by
  apply PiLp.ext
  intro v
  change (g.val.adjMatrix ℝ *ᵥ (fun _ => (Real.sqrt (M : ℝ))⁻¹)) v =
    (d : ℝ) * (Real.sqrt (M : ℝ))⁻¹
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  simp only [Finset.sum_const,nsmul_eq_mul,SimpleGraph.card_neighborFinset_eq_degree,
    g.property v]

theorem eigenvalues_le_degree (g : RegularGraph M d) (hM : 0 < M) (i : Fin M) :
    (hermitian g).eigenvalues i ≤ d := by
  letI : Nonempty (Fin M) := ⟨⟨0,hM⟩⟩
  let b := (hermitian g).eigenvectorBasis
  obtain ⟨v,_,hmax⟩ := Finset.exists_max_image Finset.univ
    (fun v => |b i v|) Finset.univ_nonempty
  have hpos : 0 < |b i v| := by
    by_contra hn
    have hzero : b i = 0 := by
      apply PiLp.ext
      intro w
      exact abs_eq_zero.mp (by linarith [hmax w (Finset.mem_univ w),abs_nonneg (b i w)])
    have hu := b.orthonormal.1 i
    simp [hzero] at hu
  have he := congrFun ((hermitian g).mulVec_eigenvectorBasis i) v
  have hb : |(hermitian g).eigenvalues i| * |b i v| ≤ (d : ℝ) * |b i v| := by
    calc
      _ = |(g.val.adjMatrix ℝ *ᵥ (⇑(b i))) v| := by
        rw [he]
        simp only [Pi.smul_apply,smul_eq_mul,abs_mul]
        rfl
      _ = |∑ w ∈ g.val.neighborFinset v,b i w| := by
        rw [SimpleGraph.adjMatrix_mulVec_apply]
        rfl
      _ ≤ ∑ w ∈ g.val.neighborFinset v,|b i w| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _w ∈ g.val.neighborFinset v,|b i v| := by
        exact Finset.sum_le_sum (fun w _ => hmax w (Finset.mem_univ w))
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,
        SimpleGraph.card_neighborFinset_eq_degree,g.property v]
  exact (le_abs_self _).trans ((mul_le_mul_right hpos).mp hb)

def graphValue (g : RegularGraph M d) : Fin M → ℝ := value (hermitian g)

def graphBasis (g : RegularGraph M d) (hM : 0 < M) :
    OrthonormalBasis (Fin M) ℝ (EuclideanSpace ℝ (Fin M)) :=
  pinnedBasis (hermitian g) hM (constantVector M)

theorem graphValue_first (g : RegularGraph M d) (hM : 0 < M) :
    graphValue g ⟨0,hM⟩ = d :=
  top_value (hermitian g) hM _ (constantVector_norm hM) d
    (constantVector_eigen g) (eigenvalues_le_degree g hM)

theorem graphBasis_first (g : RegularGraph M d) (hM : 0 < M) :
    graphBasis g hM ⟨0,hM⟩ = constantVector M :=
  pinnedBasis_first (hermitian g) hM _ (constantVector_norm hM)

theorem graphBasis_eigen (g : RegularGraph M d) (hM : 0 < M) (i : Fin M) :
    g.val.adjMatrix ℝ *ᵥ (⇑(graphBasis g hM i)) =
      graphValue g i • (⇑(graphBasis g hM i)) := by
  have h := pinnedBasis_eigen (hermitian g) hM _ (constantVector_norm hM) d
    (constantVector_eigen g) (eigenvalues_le_degree g hM) i
  exact congrArg (fun x : EuclideanSpace ℝ (Fin M) => ⇑x) h

def neighborEquiv (g : RegularGraph M d) (v : Fin M) : Fin d ≃ g.val.neighborSet v :=
  (Fintype.equivFinOfCardEq (by
    rw [SimpleGraph.card_neighborSet_eq_degree,g.property v])).symm

def graphNeighbor (g : RegularGraph M d) (v : Fin M) (j : Fin d) : Fin M :=
  (neighborEquiv g v j).val

theorem graphNeighbor_injective (g : RegularGraph M d) (v : Fin M) :
    Function.Injective (graphNeighbor g v) :=
  Subtype.val_injective.comp (neighborEquiv g v).injective

theorem graphNeighbor_exact (g : RegularGraph M d) (v w : Fin M) :
    g.val.Adj v w ↔ ∃ j, graphNeighbor g v j = w := by
  constructor
  · intro h
    obtain ⟨j,hj⟩ := (neighborEquiv g v).surjective ⟨w,h⟩
    exact ⟨j,congrArg Subtype.val hj⟩
  · rintro ⟨j,rfl⟩
    exact (neighborEquiv g v j).property

end GeneralizedBulk.Graph.CanonicalSpectrum

namespace GeneralizedBulk.Graph

abbrev UniformEnsemble (d : ℕ) (N : ℕ → ℕ) := ∀ n,RegularGraph (N n) d

open CanonicalSpectrum in
def canonicalSpectralData (d : ℕ) (N : ℕ → ℕ) (hN : ∀ n,0 < N n)
    (hlim : Filter.Tendsto N Filter.atTop Filter.atTop) :
    External.RegularSpectralData d N (UniformEnsemble d N) where
  size_pos := hN
  size_tendsto := hlim
  adjacency := fun n ω => (ω n).val.adjMatrix ℝ
  eigenvalue := fun n ω => graphValue (ω n)
  eigenvector := fun n ω i => ⇑(graphBasis (ω n) (hN n) i)
  neighbor := fun n ω => graphNeighbor (ω n)
  symmetric := by intro n ω v w; exact (ω n).val.isSymm_adjMatrix.apply _ _
  diagonal_zero := by intros; simp
  entry_zero_one := by intros; simp only [SimpleGraph.adjMatrix_apply]; split_ifs <;> simp
  regular := by
    intro n ω v
    have h := SimpleGraph.adjMatrix_mulVec_apply (ω n).val v (fun _ => (1 : ℝ))
    simpa only [Matrix.mulVec,dotProduct,mul_one,Finset.sum_const,nsmul_eq_mul,
      SimpleGraph.card_neighborFinset_eq_degree,(ω n).property v] using h
  neighbor_injective := fun n ω v => graphNeighbor_injective _ _
  neighbor_exact := by
    intro n ω v w
    rw [← graphNeighbor_exact (ω n) v w]
    by_cases h : (ω n).val.Adj v w <;> simp [SimpleGraph.adjMatrix_apply,h]
  orthonormal := by
    intro n ω i j
    have h := orthonormal_iff_ite.mp (graphBasis (ω n) (hN n)).orthonormal i j
    simpa only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Pi.star_apply,
      star_trivial,mul_comm] using h
  eigen_equation := fun n ω i v => congrFun (graphBasis_eigen (ω n) (hN n) i) v
  ordered := fun n ω i j hij => value_antitone (hermitian (ω n)) hij
  constant_eigenvalue := fun n ω => graphValue_first (ω n) (hN n)
  constant_eigenvector := by
    intro n ω v
    have h := congrArg (fun x : EuclideanSpace ℝ (Fin (N n)) => x v)
      (graphBasis_first (ω n) (hN n))
    exact h
  measurable_adjacency := fun n v w =>
    (measurable_of_finite (fun g : RegularGraph (N n) d => g.val.adjMatrix ℝ v w)).comp (measurable_pi_apply n)
  measurable_eigenvalue := fun n i =>
    (measurable_of_finite (fun g : RegularGraph (N n) d => graphValue g i)).comp (measurable_pi_apply n)
  measurable_eigenvector := fun n i v =>
    (measurable_of_finite (fun g : RegularGraph (N n) d => graphBasis g (hN n) i v)).comp (measurable_pi_apply n)
  measurable_neighbor := fun n v j =>
    (measurable_of_finite (fun g : RegularGraph (N n) d => graphNeighbor g v j)).comp (measurable_pi_apply n)

end GeneralizedBulk.Graph
