import GaussianWave.BS.FiniteCoverSampling
import GaussianWave.BS.GaussianBallConsistency

/-! Actual uniform finite cover laws are consistent. Last-layer choices
form a fixed finite product, independently of the retained covering. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GaussianWave.BS
open Reused.Graph Reused.Graph.Configuration

def BranchLayer (q : ℕ) : ℕ → Type
  | 0 => Unit
  | k + 1 => Fin q × BranchLayer q k

instance branchLayerFintype (q k : ℕ) : Fintype (BranchLayer q k) := by
  induction k with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ k ih =>
      letI := ih
      exact inferInstanceAs (Fintype (Fin q × BranchLayer q k))

def branchCoverOrderingDepthEquiv (q : ℕ) : (k : ℕ) →
    BranchCoverOrdering q (k + 1) ≃
      BranchCoverOrdering q k × (BranchLayer q k → Equiv.Perm (Fin q))
  | 0 =>
    { toFun := fun z => ((), fun _ => z.1)
      invFun := fun z => (z.2 (), fun _ => ())
      left_inv := by
        rintro ⟨p, f⟩
        apply Prod.ext
        · rfl
        · funext j; cases f j; rfl
      right_inv := by
        rintro ⟨u, f⟩
        apply Prod.ext
        · cases u; rfl
        · funext i; cases i; rfl }
  | k + 1 =>
    { toFun := fun z =>
        ((z.1, fun j => (branchCoverOrderingDepthEquiv q k (z.2 j)).1),
          fun jl => (branchCoverOrderingDepthEquiv q k (z.2 jl.1)).2 jl.2)
      invFun := fun z =>
        (z.1.1, fun j => (branchCoverOrderingDepthEquiv q k).symm (z.1.2 j, fun l => z.2 (j, l)))
      left_inv := by
        intro z
        dsimp only
        apply Prod.ext
        · rfl
        · funext j
          exact (branchCoverOrderingDepthEquiv q k).symm_apply_apply (z.2 j)
      right_inv := by
        intro z
        dsimp only
        apply Prod.ext
        · apply Prod.ext
          · rfl
          · funext j
            exact congrArg Prod.fst ((branchCoverOrderingDepthEquiv q k).apply_symm_apply
              (z.1.2 j, fun l => z.2 (j, l)))
        · funext jl
          exact congrFun (congrArg Prod.snd ((branchCoverOrderingDepthEquiv q k).apply_symm_apply
            (z.1.2 jl.1, fun l => z.2 (jl.1, l)))) jl.2 }

def branchCoverOrderingTruncate (q k : ℕ) (z : BranchCoverOrdering q (k + 1)) :
    BranchCoverOrdering q k := (branchCoverOrderingDepthEquiv q k z).1

theorem branchGraphCover_restrict {N m : ℕ} (G : RegularGraph N (m + 2))
    (k : ℕ) {parent root : Fin N} (h : G.val.Adj parent root)
    (orders : BranchCoverOrdering (m + 1) (k + 1)) (v : BranchVertex (m + 1) k) :
    branchGraphCover G (k + 1) h orders (branchVertexInclusion (m + 1) k v) =
      branchGraphCover G k h (branchCoverOrderingTruncate (m + 1) k orders) v := by
  induction k generalizing parent root with
  | zero => cases v; rfl
  | succ k ih =>
      cases v with
      | inl u => rfl
      | inr av => exact ih (graphForwardNeighbor_adj G h (orders.1 av.1)) (orders.2 av.1) av.2

abbrev VertexCoverLastLayer (m k : ℕ) :=
  Fin (m + 2) → BranchLayer (m + 1) k → Equiv.Perm (Fin (m + 1))

def vertexCoverSeedDepthEquiv (N m k : ℕ) :
    VertexCoverSeed N m (k + 1) ≃ VertexCoverSeed N m k × VertexCoverLastLayer m k where
  toFun z :=
    ((z.1, z.2.1, fun a => branchCoverOrderingTruncate (m + 1) k (z.2.2 a)),
      fun a => (branchCoverOrderingDepthEquiv (m + 1) k (z.2.2 a)).2)
  invFun z :=
    (z.1.1, z.1.2.1, fun a => (branchCoverOrderingDepthEquiv (m + 1) k).symm (z.1.2.2 a, z.2 a))
  left_inv z := by
    dsimp only [branchCoverOrderingTruncate]
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · funext a
        exact (branchCoverOrderingDepthEquiv (m + 1) k).symm_apply_apply (z.2.2 a)
  right_inv z := by
    dsimp only [branchCoverOrderingTruncate]
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · rfl
        · funext a
          exact congrArg Prod.fst ((branchCoverOrderingDepthEquiv (m + 1) k).apply_symm_apply
            (z.1.2.2 a, z.2 a))
    · funext a
      exact congrArg Prod.snd ((branchCoverOrderingDepthEquiv (m + 1) k).apply_symm_apply
        (z.1.2.2 a, z.2 a))

def vertexCoverSeedTruncate (N m k : ℕ) (z : VertexCoverSeed N m (k + 1)) :
    VertexCoverSeed N m k := (vertexCoverSeedDepthEquiv N m k z).1

theorem vertexGraphCover_restrict {N m : ℕ} (G : RegularGraph N (m + 2))
    (k : ℕ) (z : VertexCoverSeed N m (k + 1)) (v : VertexBallVertex (m + 2) k) :
    vertexGraphCover G (k + 1) z (vertexBallInclusion m k v) =
      vertexGraphCover G k (vertexCoverSeedTruncate N m k z) v := by
  cases v with
  | inl u => rfl
  | inr av =>
      exact branchGraphCover_restrict G k
        (canonicalPortLabeling G z.1 (z.2.1 av.1)).property (z.2.2 av.1) av.2

theorem finiteVertexCoverLaw_consistent {N m r : ℕ} (G : RegularGraph N (m + 2))
    (hN : 0 < N) (k : ℕ) (f : Fin r → Fin N → ℝ) :
    Measure.map (fun x : (Fin r × VertexBallVertex (m + 2) (k + 1)) → ℝ =>
      fun av : Fin r × VertexBallVertex (m + 2) k => x (av.1, vertexBallInclusion m k av.2))
      (finiteVertexCoverLaw G (k + 1) f) = finiteVertexCoverLaw G k f := by
  let T := fun x : (Fin r × VertexBallVertex (m + 2) (k + 1)) → ℝ =>
    fun av : Fin r × VertexBallVertex (m + 2) k => x (av.1, vertexBallInclusion m k av.2)
  have hT : Measurable T := measurable_pi_lambda _ (fun av => measurable_pi_apply _)
  letI := finiteVertexCoverLaw_isProbability G hN k f
  letI := finiteVertexCoverLaw_isProbability G hN (k + 1) f
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro φ
  rw [integral_map hT.aemeasurable φ.continuous.measurable.aestronglyMeasurable,
    integral_finiteVertexCoverLaw, integral_finiteVertexCoverLaw]
  have he := Equiv.sum_comp (vertexCoverSeedDepthEquiv N m k).symm
    (fun z : VertexCoverSeed N m (k + 1) =>
      φ (T (fun av => f av.1 (vertexGraphCover G (k + 1) z av.2))))
  rw [← he, Fintype.sum_prod_type]
  have hvalue (z : VertexCoverSeed N m k × VertexCoverLastLayer m k) :
      T (fun av => f av.1 (vertexGraphCover G (k + 1) ((vertexCoverSeedDepthEquiv N m k).symm z) av.2)) =
        (fun av => f av.1 (vertexGraphCover G k z.1 av.2)) := by
    funext av
    dsimp only [T]
    rw [vertexGraphCover_restrict]
    have hz : vertexCoverSeedTruncate N m k ((vertexCoverSeedDepthEquiv N m k).symm z) = z.1 :=
      congrArg Prod.fst ((vertexCoverSeedDepthEquiv N m k).apply_symm_apply z)
    rw [hz]
  simp_rw [hvalue]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
  have hcard : Fintype.card (VertexCoverSeed N m (k + 1)) =
      Fintype.card (VertexCoverSeed N m k) * Fintype.card (VertexCoverLastLayer m k) :=
    (Fintype.card_congr (vertexCoverSeedDepthEquiv N m k)).trans (Fintype.card_prod _ _)
  rw [hcard, Nat.cast_mul, mul_inv_rev]
  have hL : (Fintype.card (VertexCoverLastLayer m k) : ℝ) ≠ 0 :=
    by exact_mod_cast (Fintype.card_ne_zero : Fintype.card (VertexCoverLastLayer m k) ≠ 0)
  field_simp
  ring

end GaussianWave.BS
