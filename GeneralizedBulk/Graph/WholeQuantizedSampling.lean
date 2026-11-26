import GeneralizedBulk.Graph.QuantizedSampling

/-! Exact whole-configuration quantizer entropy under flattening and the
lossless vertex-vector code. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace GeneralizedBulk.Graph.Configuration
open Entropy

variable {k N q : ℕ}

def realWholeLaw (μ : Measure (Fin k × Fin N → ℝ)) (mean : Fin k × Fin N → ℝ) :
    Measure (Fin (k*N) → ℝ) := Measure.map (fun x => (mean+x) ∘ flatSelection (id : Fin N → Fin N)) μ

set_option maxHeartbeats 1000000 in
theorem entropy_quantized_whole_eq {B : Type*} [Fintype B] [DecidableEq B]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    (μ : Measure (Fin k × Fin N → ℝ)) (mean : Fin k × Fin N → ℝ)
    (e : (Fin k → B) ≃ Fin q) (J : ℝ → B) (hJ : Measurable J) :
    Finite.entropy (lawMass μ (fun x => quantizedVertexColor e J (mean+x))) =
      Finite.entropy (lawMass (realWholeLaw μ mean) (fun y i => J (y i))) := by
  let F : (Fin k × Fin N → ℝ) → (Fin (k*N) → ℝ) := fun x => (mean+x) ∘ flatSelection (id : Fin N → Fin N)
  let Q : (Fin (k*N) → ℝ) → (Fin (k*N) → B) := fun y i => J (y i)
  have hF : Measurable F := by fun_prop
  have hQ : Measurable Q := measurable_pi_lambda _ (fun i => hJ.comp (measurable_pi_apply i))
  have hcode : (fun x => quantizedVertexColor e J (mean+x)) = flatBundleColorEquiv e N ∘ Q ∘ F := by
    funext x
    exact (flatBundleColorEquiv_selected e J id (mean+x)).symm
  rw [hcode]
  have h := finite_entropy_law_equiv μ (Q ∘ F) (flatBundleColorEquiv e N)
  change Finite.entropy (lawMass μ (flatBundleColorEquiv e N ∘ Q ∘ F)) =
    Finite.entropy (lawMass μ (Q ∘ F)) at h
  rw [h]
  congr 1
  funext j
  exact (lawMass_map μ F hF Q hQ j).symm

end GeneralizedBulk.Graph.Configuration
