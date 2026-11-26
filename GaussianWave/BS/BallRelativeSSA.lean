import GaussianWave.BS.JointBallInnovationReference

/-!
# The actual finite-ball relative entropy gaps

This is the entropy comparison of source Section 10 in shared innovation
charts, for every finite channel family at one common energy.  The source
inputs are its ordinary positive finite-entropy densities and the actual
local/core marginal laws.  The Gaussian reference and its independent new
layers are constructed, and equality is an actual gluing-law identity.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianWave.BS

def vertexBallRelativeEntropy (κ : Type*) [Fintype κ] (m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ))
    (f : PositiveEntropyDensity (volume : Measure (((κ × VertexBallInnovation (m + 2) k)) → ℝ))) : ℝ :=
  f.entropy - (jointVertexInnovationReference κ m k energy he).entropy

def edgeBallRelativeEntropy (κ : Type*) [Fintype κ] (m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ))
    (f : PositiveEntropyDensity (volume : Measure (((κ × EdgeBallInnovation (m + 2) k)) → ℝ))) : ℝ :=
  f.entropy - (jointEdgeInnovationReference κ m k energy he).entropy

section Vertex
variable (κ : Type*) [Fintype κ] [DecidableEq κ] (m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ))
    (f : PositiveEntropyDensity (volume : Measure ((κ × VertexBallInnovation (m + 2) (k + 1)) → ℝ)))
    (p : PositiveEntropyDensity (volume : Measure ((κ × EdgeBallInnovation (m + 2) (k + 1)) → ℝ)))
    (s : PositiveEntropyDensity (volume : Measure ((κ × VertexBallInnovation (m + 2) k) → ℝ)))
    (hp : ∀ a : Fin (m + 2), Measure.map
      ((coloredLocalEdgeInnovationEquiv κ m k energy (ne_of_lt ((le_abs_self energy).trans_lt he)) a) ∘
        innovationLocalProjection (coloredForestSplit κ (Fin (m + 2)) m k) a) f.law = p.law)
    (hs : Measure.map (innovationCoreProjection (coloredForestSplit κ (Fin (m + 2)) m k)) f.law = s.law)

include hp hs

theorem vertexBall_relative_ssa_nonneg :
    0 ≤ (m + 2 : ℝ) * edgeBallRelativeEntropy κ m (k + 1) energy he p -
      ((m + 2 : ℝ) - 1) * vertexBallRelativeEntropy κ m k energy he s -
      vertexBallRelativeEntropy κ m (k + 1) energy he f := by
  have h := innovationRelativeSSA_nonneg (coloredForestSplit κ (Fin (m + 2)) m k)
    (coloredLocalEdgeInnovationEquiv κ m k energy (ne_of_lt ((le_abs_self energy).trans_lt he)))
    f (fun _ => p) s hp hs (jointVertexInnovationReference κ m k energy he)
      (jointNewInnovationReference κ m k energy he)
  have hlocal (a : Fin (m + 2)) := PositiveEntropyDensity.entropy_eq_of_law_eq _ _
    (vertexReferenceLocal_law κ m k energy he a)
  have hfull := PositiveEntropyDensity.entropy_eq_of_law_eq _ _ (vertexReferenceFull_law κ m k energy he)
  simp only [hlocal, hfull, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_ofNat] at h
  exact h

theorem vertexBall_relative_ssa_equality_iff :
    ((m + 2 : ℝ) * edgeBallRelativeEntropy κ m (k + 1) energy he p -
      ((m + 2 : ℝ) - 1) * vertexBallRelativeEntropy κ m k energy he s -
      vertexBallRelativeEntropy κ m (k + 1) energy he f = 0) ↔
      (innovationSplitDensity (coloredForestSplit κ (Fin (m + 2)) m k) f).law =
        finiteConditionalGluingLaw
          (volume : Measure ((κ × NewBranchInnovation m k) → ℝ))
          (volume : Measure ((κ × VertexBallInnovation (m + 2) k) → ℝ))
          (fun a => innovationLocalDensity
            (coloredLocalEdgeInnovationEquiv κ m k energy (ne_of_lt ((le_abs_self energy).trans_lt he)) a) p) s := by
  have h := innovationRelativeSSA_equality_iff (coloredForestSplit κ (Fin (m + 2)) m k)
    (coloredLocalEdgeInnovationEquiv κ m k energy (ne_of_lt ((le_abs_self energy).trans_lt he)))
    f (fun _ => p) s hp hs (jointVertexInnovationReference κ m k energy he)
      (jointNewInnovationReference κ m k energy he)
  have hlocal (a : Fin (m + 2)) := PositiveEntropyDensity.entropy_eq_of_law_eq _ _
    (vertexReferenceLocal_law κ m k energy he a)
  have hfull := PositiveEntropyDensity.entropy_eq_of_law_eq _ _ (vertexReferenceFull_law κ m k energy he)
  simp only [hlocal, hfull, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_ofNat] at h
  exact h
end Vertex

section Edge
variable (κ : Type*) [Fintype κ] [DecidableEq κ] (m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ))
    (f : PositiveEntropyDensity (volume : Measure ((κ × EdgeBallInnovation (m + 2) (k + 1)) → ℝ)))
    (p : PositiveEntropyDensity (volume : Measure ((κ × VertexBallInnovation (m + 2) k) → ℝ)))
    (s : PositiveEntropyDensity (volume : Measure ((κ × EdgeBallInnovation (m + 2) k) → ℝ)))
    (hp : ∀ b : Bool, Measure.map
      ((coloredLocalVertexInnovationEquiv κ m k energy (ne_of_lt ((le_abs_self energy).trans_lt he)) b) ∘
        innovationLocalProjection (coloredForestSplit κ Bool m k) b) f.law = p.law)
    (hs : Measure.map (innovationCoreProjection (coloredForestSplit κ Bool m k)) f.law = s.law)

include hp hs

theorem edgeBall_relative_ssa_nonneg :
    0 ≤ 2 * vertexBallRelativeEntropy κ m k energy he p -
      edgeBallRelativeEntropy κ m k energy he s - edgeBallRelativeEntropy κ m (k + 1) energy he f := by
  have h := innovationRelativeSSA_nonneg (coloredForestSplit κ Bool m k)
    (coloredLocalVertexInnovationEquiv κ m k energy (ne_of_lt ((le_abs_self energy).trans_lt he)))
    f (fun _ => p) s hp hs (jointEdgeInnovationReference κ m k energy he)
      (jointNewInnovationReference κ m k energy he)
  have hlocal (b : Bool) := PositiveEntropyDensity.entropy_eq_of_law_eq _ _
    (edgeReferenceLocal_law κ m k energy he b)
  have hfull := PositiveEntropyDensity.entropy_eq_of_law_eq _ _ (edgeReferenceFull_law κ m k energy he)
  simp only [hlocal, hfull, Finset.sum_const, Finset.card_univ, Fintype.card_bool,
    nsmul_eq_mul, Nat.cast_ofNat] at h
  norm_num only [sub_self, sub_add_cancel, one_mul, Nat.cast_ofNat] at h
  convert h using 1 <;> unfold vertexBallRelativeEntropy edgeBallRelativeEntropy <;> ring

theorem edgeBall_relative_ssa_equality_iff :
    (2 * vertexBallRelativeEntropy κ m k energy he p - edgeBallRelativeEntropy κ m k energy he s -
      edgeBallRelativeEntropy κ m (k + 1) energy he f = 0) ↔
      (innovationSplitDensity (coloredForestSplit κ Bool m k) f).law =
        finiteConditionalGluingLaw
          (volume : Measure ((κ × NewBranchInnovation m k) → ℝ))
          (volume : Measure ((κ × EdgeBallInnovation (m + 2) k) → ℝ))
          (fun b => innovationLocalDensity
            (coloredLocalVertexInnovationEquiv κ m k energy (ne_of_lt ((le_abs_self energy).trans_lt he)) b) p) s := by
  have h := innovationRelativeSSA_equality_iff (coloredForestSplit κ Bool m k)
    (coloredLocalVertexInnovationEquiv κ m k energy (ne_of_lt ((le_abs_self energy).trans_lt he)))
    f (fun _ => p) s hp hs (jointEdgeInnovationReference κ m k energy he)
      (jointNewInnovationReference κ m k energy he)
  have hlocal (b : Bool) := PositiveEntropyDensity.entropy_eq_of_law_eq _ _
    (edgeReferenceLocal_law κ m k energy he b)
  have hfull := PositiveEntropyDensity.entropy_eq_of_law_eq _ _ (edgeReferenceFull_law κ m k energy he)
  simp only [hlocal, hfull, Finset.sum_const, Finset.card_univ, Fintype.card_bool,
    nsmul_eq_mul, Nat.cast_ofNat] at h
  convert h using 1 <;> unfold vertexBallRelativeEntropy edgeBallRelativeEntropy <;> ring
end Edge

end GaussianWave.BS
