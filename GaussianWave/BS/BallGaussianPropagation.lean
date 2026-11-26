import GaussianWave.BS.BallRelativeSSA
import GaussianWave.BS.InnovationGluingPropagation

/-! Zero proved SSA gaps propagate actual Gaussian laws from the overlapping
balls. This is finite-law gluing, with no Markov or Gaussianity certificate
assumed for the larger source ball. -/
noncomputable section
open MeasureTheory
namespace GaussianWave.BS

theorem vertexBall_eq_gaussian_of_zero_gap (κ : Type*) [Fintype κ] [DecidableEq κ]
    (m k : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ))
    (f : PositiveEntropyDensity (volume : Measure ((κ × VertexBallInnovation (m + 2) (k + 1)) → ℝ)))
    (p : PositiveEntropyDensity (volume : Measure ((κ × EdgeBallInnovation (m + 2) (k + 1)) → ℝ)))
    (s : PositiveEntropyDensity (volume : Measure ((κ × VertexBallInnovation (m + 2) k) → ℝ)))
    (hp : ∀ a : Fin (m + 2), Measure.map
      ((coloredLocalEdgeInnovationEquiv κ m k energy (ne_of_lt ((le_abs_self energy).trans_lt he)) a) ∘
        innovationLocalProjection (coloredForestSplit κ (Fin (m + 2)) m k) a) f.law = p.law)
    (hs : Measure.map (innovationCoreProjection (coloredForestSplit κ (Fin (m + 2)) m k)) f.law = s.law)
    (hpG : p.law = (jointEdgeInnovationReference κ m (k + 1) energy he).law)
    (hsG : s.law = (jointVertexInnovationReference κ m k energy he).law)
    (hzero : (m + 2 : ℝ) * edgeBallRelativeEntropy κ m (k + 1) energy he p -
      ((m + 2 : ℝ) - 1) * vertexBallRelativeEntropy κ m k energy he s -
      vertexBallRelativeEntropy κ m (k + 1) energy he f = 0) :
    f.law = (jointVertexInnovationReference κ m (k + 1) energy he).law := by
  have hglue := (vertexBall_relative_ssa_equality_iff κ m k energy he f p s hp hs).mp hzero
  have h := innovation_eq_reference_of_gluing (coloredForestSplit κ (Fin (m + 2)) m k)
    (coloredLocalEdgeInnovationEquiv κ m k energy (ne_of_lt ((le_abs_self energy).trans_lt he)))
    f (fun _ => p) s (jointVertexInnovationReference κ m k energy he)
      (jointNewInnovationReference κ m k energy he)
    (fun a => hpG.trans (vertexReferenceLocal_law κ m k energy he a).symm) hsG hglue
  exact h.trans (vertexReferenceFull_law κ m k energy he)

theorem edgeBall_eq_gaussian_of_zero_gap (κ : Type*) [Fintype κ] [DecidableEq κ]
    (m k : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ))
    (f : PositiveEntropyDensity (volume : Measure ((κ × EdgeBallInnovation (m + 2) (k + 1)) → ℝ)))
    (p : PositiveEntropyDensity (volume : Measure ((κ × VertexBallInnovation (m + 2) k) → ℝ)))
    (s : PositiveEntropyDensity (volume : Measure ((κ × EdgeBallInnovation (m + 2) k) → ℝ)))
    (hp : ∀ b : Bool, Measure.map
      ((coloredLocalVertexInnovationEquiv κ m k energy (ne_of_lt ((le_abs_self energy).trans_lt he)) b) ∘
        innovationLocalProjection (coloredForestSplit κ Bool m k) b) f.law = p.law)
    (hs : Measure.map (innovationCoreProjection (coloredForestSplit κ Bool m k)) f.law = s.law)
    (hpG : p.law = (jointVertexInnovationReference κ m k energy he).law)
    (hsG : s.law = (jointEdgeInnovationReference κ m k energy he).law)
    (hzero : 2 * vertexBallRelativeEntropy κ m k energy he p -
      edgeBallRelativeEntropy κ m k energy he s - edgeBallRelativeEntropy κ m (k + 1) energy he f = 0) :
    f.law = (jointEdgeInnovationReference κ m (k + 1) energy he).law := by
  have hglue := (edgeBall_relative_ssa_equality_iff κ m k energy he f p s hp hs).mp hzero
  have h := innovation_eq_reference_of_gluing (coloredForestSplit κ Bool m k)
    (coloredLocalVertexInnovationEquiv κ m k energy (ne_of_lt ((le_abs_self energy).trans_lt he)))
    f (fun _ => p) s (jointEdgeInnovationReference κ m k energy he)
      (jointNewInnovationReference κ m k energy he)
    (fun b => hpG.trans (edgeReferenceLocal_law κ m k energy he b).symm) hsG hglue
  exact h.trans (edgeReferenceFull_law κ m k energy he)

theorem all_ball_laws_eq_gaussian_of_zero_gaps (κ : Type*) [Fintype κ] [DecidableEq κ]
    (m : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ))
    (C : ∀ k, PositiveEntropyDensity (volume : Measure ((κ × VertexBallInnovation (m + 2) k) → ℝ)))
    (E : ∀ k, PositiveEntropyDensity (volume : Measure ((κ × EdgeBallInnovation (m + 2) k) → ℝ)))
    (hCL : ∀ k a, Measure.map
      ((coloredLocalEdgeInnovationEquiv κ m k energy (ne_of_lt ((le_abs_self energy).trans_lt he)) a) ∘
        innovationLocalProjection (coloredForestSplit κ (Fin (m + 2)) m k) a) (C (k + 1)).law = (E (k + 1)).law)
    (hCC : ∀ k, Measure.map (innovationCoreProjection (coloredForestSplit κ (Fin (m + 2)) m k))
      (C (k + 1)).law = (C k).law)
    (hEL : ∀ k b, Measure.map
      ((coloredLocalVertexInnovationEquiv κ m k energy (ne_of_lt ((le_abs_self energy).trans_lt he)) b) ∘
        innovationLocalProjection (coloredForestSplit κ Bool m k) b) (E (k + 1)).law = (C k).law)
    (hEC : ∀ k, Measure.map (innovationCoreProjection (coloredForestSplit κ Bool m k))
      (E (k + 1)).law = (E k).law)
    (hC0 : (C 0).law = (jointVertexInnovationReference κ m 0 energy he).law)
    (hE0 : (E 0).law = (jointEdgeInnovationReference κ m 0 energy he).law)
    (hA : ∀ k, (m + 2 : ℝ) * edgeBallRelativeEntropy κ m (k + 1) energy he (E (k + 1)) -
      ((m + 2 : ℝ) - 1) * vertexBallRelativeEntropy κ m k energy he (C k) -
      vertexBallRelativeEntropy κ m (k + 1) energy he (C (k + 1)) = 0)
    (hB : ∀ k, 2 * vertexBallRelativeEntropy κ m k energy he (C k) -
      edgeBallRelativeEntropy κ m k energy he (E k) -
      edgeBallRelativeEntropy κ m (k + 1) energy he (E (k + 1)) = 0) :
    ∀ k, (C k).law = (jointVertexInnovationReference κ m k energy he).law ∧
      (E k).law = (jointEdgeInnovationReference κ m k energy he).law := by
  intro k
  induction k with
  | zero => exact ⟨hC0, hE0⟩
  | succ k ih =>
    have hEnext := edgeBall_eq_gaussian_of_zero_gap κ m k energy he (E (k + 1)) (C k) (E k)
      (hEL k) (hEC k) ih.1 ih.2 (hB k)
    exact ⟨vertexBall_eq_gaussian_of_zero_gap κ m k energy he (C (k + 1)) (E (k + 1)) (C k)
      (hCL k) (hCC k) hEnext ih.1 (hA k), hEnext⟩

end GaussianWave.BS
