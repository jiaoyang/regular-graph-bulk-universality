import GaussianWave.BS.EigenBallCoordinates
import GaussianWave.BS.Reused.Graph.ColorSampling

/-!
# Constructive finite uniform tree-cover sampling

The graph is an actual labeled simple regular graph. Each interior vertex
uses a permutation of its unused neighbor ports. The construction allows
collisions between distinct branches, as a graph covering should, and
satisfies every interior eigenrelation pointwise.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GaussianWave.BS
open Reused.Graph Reused.Graph.Configuration

def graphParentPort {N m : ℕ} (G : RegularGraph N (m + 2))
    {parent root : Fin N} (h : G.val.Adj parent root) : Fin (m + 2) :=
  (canonicalPortLabeling G root).symm ⟨parent, h.symm⟩

theorem graphNeighbor_parentPort {N m : ℕ} (G : RegularGraph N (m + 2))
    {parent root : Fin N} (h : G.val.Adj parent root) :
    graphNeighbor G root (graphParentPort G h) = parent := by
  exact congrArg Subtype.val ((canonicalPortLabeling G root).apply_symm_apply ⟨parent, h.symm⟩)

def graphForwardNeighbor {N m : ℕ} (G : RegularGraph N (m + 2))
    {parent root : Fin N} (h : G.val.Adj parent root) (j : Fin (m + 1)) : Fin N :=
  graphNeighbor G root ((graphParentPort G h).succAbove j)

theorem graphForwardNeighbor_adj {N m : ℕ} (G : RegularGraph N (m + 2))
    {parent root : Fin N} (h : G.val.Adj parent root) (j : Fin (m + 1)) :
    G.val.Adj root (graphForwardNeighbor G h j) :=
  (canonicalPortLabeling G root ((graphParentPort G h).succAbove j)).property

theorem graphForwardNeighbor_ne_parent {N m : ℕ} (G : RegularGraph N (m + 2))
    {parent root : Fin N} (h : G.val.Adj parent root) (j : Fin (m + 1)) :
    graphForwardNeighbor G h j ≠ parent := by
  intro he
  have hi : Function.Injective (graphNeighbor G root) := by
    intro a b hab
    exact (canonicalPortLabeling G root).injective (Subtype.ext hab)
  have hp := hi (he.trans (graphNeighbor_parentPort G h).symm)
  exact Fin.succAbove_ne _ _ hp

theorem graphForwardNeighbor_sum {N m : ℕ} (G : RegularGraph N (m + 2))
    {parent root : Fin N} (h : G.val.Adj parent root) (f : Fin N → ℝ) :
    f parent + (∑ j, f (graphForwardNeighbor G h j)) =
      ∑ j, f (graphNeighbor G root j) := by
  rw [Fin.sum_univ_succAbove (fun j => f (graphNeighbor G root j)) (graphParentPort G h)]
  rw [graphNeighbor_parentPort]
  rfl

def BranchCoverOrdering (q : ℕ) : ℕ → Type
  | 0 => Unit
  | k + 1 => Equiv.Perm (Fin q) × (Fin q → BranchCoverOrdering q k)

instance branchCoverOrderingFintype (q k : ℕ) : Fintype (BranchCoverOrdering q k) := by
  induction k with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ k ih =>
      letI := ih
      exact inferInstanceAs (Fintype (Equiv.Perm (Fin q) × (Fin q → BranchCoverOrdering q k)))

instance branchCoverOrderingInhabited (q k : ℕ) : Inhabited (BranchCoverOrdering q k) := by
  induction k with
  | zero => exact ⟨()⟩
  | succ k ih =>
      letI := ih
      exact ⟨(Equiv.refl _, fun _ => default)⟩

def branchGraphCover {N m : ℕ} (G : RegularGraph N (m + 2)) :
    (k : ℕ) → {parent root : Fin N} → G.val.Adj parent root →
      BranchCoverOrdering (m + 1) k → BranchVertex (m + 1) k → Fin N
  | 0, _, root, _, _, _ => root
  | k + 1, _, root, h, orders, Sum.inl _ => root
  | k + 1, _, _, h, orders, Sum.inr (j, v) =>
      branchGraphCover G k (graphForwardNeighbor_adj G h (orders.1 j)) (orders.2 j) v

@[simp] theorem branchGraphCover_root {N m : ℕ} (G : RegularGraph N (m + 2))
    (k : ℕ) {parent root : Fin N} (h : G.val.Adj parent root)
    (orders : BranchCoverOrdering (m + 1) k) :
    branchGraphCover G k h orders (branchRoot (m + 1) k) = root := by
  cases k <;> rfl

def GraphEigenrelation {N d : ℕ} (G : RegularGraph N d) (energy : ℝ) (f : Fin N → ℝ) : Prop :=
  ∀ v, (∑ j, f (graphNeighbor G v j)) = energy * f v

theorem branchGraphCover_eigenrelation {N m : ℕ} (G : RegularGraph N (m + 2))
    (energy : ℝ) (f : Fin N → ℝ) (hf : GraphEigenrelation G energy f)
    (k : ℕ) {parent root : Fin N} (h : G.val.Adj parent root)
    (orders : BranchCoverOrdering (m + 1) k) :
    BranchEigenrelation m k energy (f parent) (fun v => f (branchGraphCover G k h orders v)) := by
  induction k generalizing parent root with
  | zero => trivial
  | succ k ih =>
      constructor
      · change (∑ j, f (branchGraphCover G k
          (graphForwardNeighbor_adj G h (orders.1 j)) (orders.2 j) (branchRoot (m + 1) k))) =
            energy * f root - f parent
        simp only [branchGraphCover_root]
        have hs : f parent + (∑ j, f (graphForwardNeighbor G h (orders.1 j))) = energy * f root := by
          rw [Equiv.sum_comp orders.1 (fun j => f (graphForwardNeighbor G h j)),
            graphForwardNeighbor_sum G h f]
          exact hf root
        linarith
      · intro j
        exact ih (graphForwardNeighbor_adj G h (orders.1 j)) (orders.2 j)

abbrev VertexCoverSeed (N m k : ℕ) :=
  Fin N × Equiv.Perm (Fin (m + 2)) × (Fin (m + 2) → BranchCoverOrdering (m + 1) k)

def vertexGraphCover {N m : ℕ} (G : RegularGraph N (m + 2)) (k : ℕ)
    (seed : VertexCoverSeed N m k) : VertexBallVertex (m + 2) k → Fin N
  | Sum.inl _ => seed.1
  | Sum.inr (a, v) => branchGraphCover G k
      (canonicalPortLabeling G seed.1 (seed.2.1 a)).property (seed.2.2 a) v

@[simp] theorem vertexGraphCover_root {N m : ℕ} (G : RegularGraph N (m + 2)) (k : ℕ)
    (seed : VertexCoverSeed N m k) : vertexGraphCover G k seed (vertexBallRoot (m + 2) k) = seed.1 := rfl

@[simp] theorem vertexGraphCover_neighbor {N m : ℕ} (G : RegularGraph N (m + 2)) (k : ℕ)
    (seed : VertexCoverSeed N m k) (a : Fin (m + 2)) :
    vertexGraphCover G k seed (vertexBallNeighbor (m + 2) k a) = graphNeighbor G seed.1 (seed.2.1 a) :=
  branchGraphCover_root _ _ _ _

theorem vertexGraphCover_eigenrelation {N m : ℕ} (G : RegularGraph N (m + 2))
    (energy : ℝ) (f : Fin N → ℝ) (hf : GraphEigenrelation G energy f) (k : ℕ)
    (seed : VertexCoverSeed N m k) :
    VertexBallEigenrelation m k energy (fun v => f (vertexGraphCover G k seed v)) := by
  constructor
  · change (∑ a, f (vertexGraphCover G k seed (vertexBallNeighbor (m + 2) k a))) = _
    simp only [vertexGraphCover_neighbor, vertexGraphCover_root]
    rw [Equiv.sum_comp seed.2.1 (fun j => f (graphNeighbor G seed.1 j))]
    exact hf seed.1
  · intro a
    exact branchGraphCover_eigenrelation G energy f hf k
      (canonicalPortLabeling G seed.1 (seed.2.1 a)).property (seed.2.2 a)

/-- Literal empirical cover law, including every uniform choice of local
neighbor ordering. No process invariance or Gaussianity is assumed. -/
def finiteVertexCoverLaw {N m r : ℕ} (G : RegularGraph N (m + 2)) (k : ℕ)
    (f : Fin r → Fin N → ℝ) : Measure ((Fin r × VertexBallVertex (m + 2) k) → ℝ) :=
  (Fintype.card (VertexCoverSeed N m k) : ENNReal)⁻¹ •
    ∑ seed : VertexCoverSeed N m k, Measure.dirac (fun av => f av.1 (vertexGraphCover G k seed av.2))

theorem finiteVertexCoverLaw_isProbability {N m r : ℕ} (G : RegularGraph N (m + 2))
    (hN : 0 < N) (k : ℕ) (f : Fin r → Fin N → ℝ) :
    IsProbabilityMeasure (finiteVertexCoverLaw G k f) := by
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  constructor
  simp only [finiteVertexCoverLaw, Measure.smul_apply, Measure.finset_sum_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel
    (by exact_mod_cast (Fintype.card_ne_zero : Fintype.card (VertexCoverSeed N m k) ≠ 0))
    (ENNReal.natCast_ne_top _)

theorem integrable_finiteVertexCoverLaw {N m r : ℕ} (G : RegularGraph N (m + 2))
    (hN : 0 < N) (k : ℕ) (f : Fin r → Fin N → ℝ)
    (F : ((Fin r × VertexBallVertex (m + 2) k) → ℝ) → ℝ) :
    Integrable F (finiteVertexCoverLaw G k f) := by
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  exact (integrable_finset_sum_measure.mpr (fun _ _ => integrable_dirac)).smul_measure
    (ENNReal.inv_ne_top.mpr (by exact_mod_cast
      (Fintype.card_ne_zero : Fintype.card (VertexCoverSeed N m k) ≠ 0)))

theorem integral_finiteVertexCoverLaw {N m r : ℕ} (G : RegularGraph N (m + 2))
    (k : ℕ) (f : Fin r → Fin N → ℝ)
    (F : ((Fin r × VertexBallVertex (m + 2) k) → ℝ) → ℝ) :
    (∫ x, F x ∂finiteVertexCoverLaw G k f) =
      (Fintype.card (VertexCoverSeed N m k) : ℝ)⁻¹ *
        ∑ seed : VertexCoverSeed N m k, F (fun av => f av.1 (vertexGraphCover G k seed av.2)) := by
  rw [finiteVertexCoverLaw, integral_smul_measure,
    integral_finset_sum_measure (fun _ _ => integrable_dirac)]
  simp

theorem integral_finiteVertexCoverLaw_root {N m r : ℕ} (G : RegularGraph N (m + 2))
    (k : ℕ) (f : Fin r → Fin N → ℝ) (F : (Fin r → ℝ) → ℝ) :
    (∫ x, F (fun a => x (a, vertexBallRoot (m + 2) k)) ∂finiteVertexCoverLaw G k f) =
      (N : ℝ)⁻¹ * ∑ v, F (fun a => f a v) := by
  rw [integral_finiteVertexCoverLaw]
  simp only [vertexGraphCover_root, VertexCoverSeed, Fintype.card_prod,
    Fintype.card_fin, Nat.cast_mul, Fintype.sum_prod_type,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  by_cases hN : N = 0
  · subst N
    simp
  have hP : (Fintype.card (Equiv.Perm (Fin (m + 2))) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hB : (Fintype.card (Fin (m + 2) → BranchCoverOrdering (m + 1) k) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp <;> ring

theorem finiteVertexCoverLaw_ae_eigenrelation {N m r : ℕ} (G : RegularGraph N (m + 2))
    (k : ℕ) (energy : Fin r → ℝ) (f : Fin r → Fin N → ℝ)
    (hf : ∀ a, GraphEigenrelation G (energy a) (f a)) :
    ∀ᵐ x ∂finiteVertexCoverLaw G k f, ∀ a,
      VertexBallEigenrelation m k (energy a) (fun v => x (a, v)) := by
  rw [ae_iff]
  have hzero : (∑ seed : VertexCoverSeed N m k,
      Measure.dirac (fun av => f av.1 (vertexGraphCover G k seed av.2)))
      {x | ¬∀ a, VertexBallEigenrelation m k (energy a) (fun v => x (a, v))} = 0 := by
    rw [Measure.finset_sum_apply]
    apply Finset.sum_eq_zero
    intro seed _
    have hnot : (fun av => f av.1 (vertexGraphCover G k seed av.2)) ∉
        {x | ¬∀ a, VertexBallEigenrelation m k (energy a) (fun v => x (a, v))} := by
      intro hbad
      exact hbad (fun a => vertexGraphCover_eigenrelation G (energy a) (f a) (hf a) k seed)
    rw [Measure.dirac_apply, Set.indicator_of_not_mem hnot]
  simpa only [finiteVertexCoverLaw, Measure.smul_apply, hzero, smul_eq_mul, mul_zero]

end GaussianWave.BS
