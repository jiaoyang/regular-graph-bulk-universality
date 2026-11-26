import GaussianWave.BS.LiftedCoverFiniteWindows
import Mathlib.MeasureTheory.Constructions.Projective

/-! Actual entire tree process laws are determined by their centered finite
ball marginals, jointly in all channels. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GaussianWave.BS

theorem treeProcessLaw_eq_of_ball_marginals (m r : ℕ)
    (P Q : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ))
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (h : ∀ k,Measure.map
      (fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ =>
        fun av : Fin r × VertexBallVertex (m+2) k => z (av.1,vertexBallEmbedding (m+2) k av.2)) P =
      Measure.map
      (fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ =>
        fun av : Fin r × VertexBallVertex (m+2) k => z (av.1,vertexBallEmbedding (m+2) k av.2)) Q) : P=Q := by
  let F := fun S : Finset (Fin r × RegularTreeVertex (m+2)) => Measure.map S.restrict P
  letI (S : Finset (Fin r × RegularTreeVertex (m+2))) : IsProbabilityMeasure (F S) :=
    isProbabilityMeasure_map (Finset.measurable_restrict S).aemeasurable
  have hP : IsProjectiveLimit P F := fun _ => rfl
  have hQ : IsProjectiveLimit Q F := by
    intro S
    let L := ∑ av ∈ S,regularTreeDepth av.2
    have hdepth (av : S) : regularTreeDepth av.val.2 ≤ L+1 := by
      dsimp only [L]
      exact (Finset.single_le_sum (f := fun av : Fin r × RegularTreeVertex (m+2) => regularTreeDepth av.2)
        (fun _ _ => Nat.zero_le _) av.property).trans (Nat.le_succ _)
    have hex (av : S) : ∃ v : VertexBallVertex (m+2) L,vertexBallEmbedding (m+2) L v=av.val.2 := by
      have hh : av.val.2 ∈ Set.range (vertexBallEmbedding (m+2) L) := by
        rw [vertexBallEmbedding_range]
        exact hdepth av
      exact hh
    choose pos hpos using hex
    let R := fun z : (Fin r × VertexBallVertex (m+2) L) → ℝ => fun av : S => z (av.val.1,pos av)
    let B := fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ =>
      fun av : Fin r × VertexBallVertex (m+2) L => z (av.1,vertexBallEmbedding (m+2) L av.2)
    have hR : Measurable R := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
    have hB : Measurable B := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
    have he : (S.restrict : ((Fin r × RegularTreeVertex (m+2)) → ℝ) → S → ℝ)=R ∘ B := by
      funext z av
      simp only [Function.comp_apply,R,B,hpos]
      rfl
    change Measure.map S.restrict Q=Measure.map S.restrict P
    rw [he,← Measure.map_map hR hB,← Measure.map_map hR hB,h L]
  exact hP.unique hQ

end GaussianWave.BS
