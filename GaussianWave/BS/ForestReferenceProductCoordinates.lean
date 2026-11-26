import GaussianWave.BS.FiniteProductPartition

/-!
# The actual innovation reference decoded from a literal product measure
-/
noncomputable section
open MeasureTheory
namespace GaussianWave.BS

def forestNodeDecode (A : Type*) (m k : ℕ)
    (p : (A → ℝ) × ((A × BranchInternalNode (m + 1) k) → Fin m → ℝ)) : ForestInnovation A m k → ℝ :=
  Sum.elim p.1 (fun aj =>
    p.2 (aj.1, (branchInnovationNodeEquiv m k aj.2).1) (branchInnovationNodeEquiv m k aj.2).2)

theorem measurable_forestNodeDecode (A : Type*) (m k : ℕ) : Measurable (forestNodeDecode A m k) := by
  apply measurable_pi_lambda
  intro j
  cases j with
  | inl a => exact (measurable_pi_apply a).comp measurable_fst
  | inr aj =>
      exact (measurable_pi_apply (branchInnovationNodeEquiv m k aj.2).2).comp
        ((measurable_pi_apply (aj.1, (branchInnovationNodeEquiv m k aj.2).1)).comp measurable_snd)

theorem forestNodeDecode_reindex (A : Type*) (m k : ℕ)
    (p : (A → ℝ) × ((A × BranchInternalNode (m + 1) k) → Fin m → ℝ)) :
    (fun j => forestNodeDecode A m k p ((forestNodeEquiv A (branchInnovationNodeEquiv m k)).symm j)) =
      concatenateVector (p.1, flattenChannels p.2) := by
  ext j
  cases j with
  | inl a => rfl
  | inr ani => simp [forestNodeDecode, forestNodeEquiv, flattenChannels, concatenateVector]

theorem forestGaussianInnovationLaw_eq_decoded_product {A : Type*} [Fintype A] [DecidableEq A]
    (m k : ℕ) (scale : ℝ) (R : Matrix A A ℝ) :
    forestGaussianInnovationLaw m k scale R =
      Measure.map (forestNodeDecode A m k)
        ((linearImageGaussian R).prod (Measure.pi (fun _ : A × BranchInternalNode (m + 1) k =>
          siblingInnovationGaussian m scale))) := by
  let e := (LinearEquiv.funCongrLeft ℝ ℝ (forestNodeEquiv A (branchInnovationNodeEquiv m k)).symm).toContinuousLinearEquiv
  apply MeasurableEquiv.map_measurableEquiv_injective e.toHomeomorph.toMeasurableEquiv
  change Measure.map (fun x => fun j => x ((forestNodeEquiv A (branchInnovationNodeEquiv m k)).symm j))
      (forestGaussianInnovationLaw m k scale R) =
    Measure.map (fun x => fun j => x ((forestNodeEquiv A (branchInnovationNodeEquiv m k)).symm j))
      (Measure.map (forestNodeDecode A m k) _)
  rw [forestGaussianInnovation_node_product]
  rw [Measure.map_map (by fun_prop) (measurable_forestNodeDecode A m k)]
  have hf : (fun p : (A → ℝ) × ((A × BranchInternalNode (m + 1) k) → Fin m → ℝ) =>
      fun j => forestNodeDecode A m k p ((forestNodeEquiv A (branchInnovationNodeEquiv m k)).symm j)) =
      concatenateVector ∘ Prod.map id flattenChannels := funext (forestNodeDecode_reindex A m k)
  change sumVectorProductLaw _ _ = Measure.map
    (fun p : (A → ℝ) × ((A × BranchInternalNode (m + 1) k) → Fin m → ℝ) =>
      fun j => forestNodeDecode A m k p ((forestNodeEquiv A (branchInnovationNodeEquiv m k)).symm j)) _
  rw [hf]
  unfold sumVectorProductLaw
  rw [← Measure.map_map measurable_concatenateVector (measurable_id.prodMap measurable_flattenChannels)]
  letI : IsProbabilityMeasure (Measure.pi (fun _ : A × BranchInternalNode (m + 1) k =>
      siblingInnovationGaussian m scale)) := Measure.pi.instIsProbabilityMeasure _
  have hp := Measure.map_prod_map (f := (id : (A → ℝ) → (A → ℝ)))
    (g := flattenChannels (κ := A × BranchInternalNode (m + 1) k) (ι := Fin m)) (linearImageGaussian R)
    (Measure.pi (fun _ : A × BranchInternalNode (m + 1) k => siblingInnovationGaussian m scale))
    measurable_id measurable_flattenChannels
  simpa only [Measure.map_id] using congrArg (Measure.map concatenateVector) hp

end GaussianWave.BS
