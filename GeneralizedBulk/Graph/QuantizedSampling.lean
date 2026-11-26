import GeneralizedBulk.Graph.RealSampling
import GeneralizedBulk.Entropy.LawMap

/-! Lossless quantizer codes identify actual sampled real-star and real-edge
laws with the mean graph color profiles. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace GeneralizedBulk.Graph.Configuration
open ColorProfiles Entropy

variable {k N d q : ℕ}

def realStarSampleLaw (μ : Measure (Fin k × Fin N → ℝ)) (G : RegularGraph N d)
    (mean : Fin k × Fin N → ℝ) : Measure (Fin (k*(d+1)) → ℝ) :=
  finiteSampleLaw μ (uniformSampleWeight (Fin N × Equiv.Perm (Fin d)))
    (fun z x => (mean+x) ∘ flatSelection (starVertexSelection G z))

def realEdgeSampleLaw (μ : Measure (Fin k × Fin N → ℝ)) (G : RegularGraph N d)
    (mean : Fin k × Fin N → ℝ) : Measure (Fin (k*2) → ℝ) :=
  finiteSampleLaw μ (uniformSampleWeight (Fin N × Fin d))
    (fun z x => (mean+x) ∘ flatSelection (edgeVertexSelection G z))

variable {B : Type*} [Fintype B] [DecidableEq B] [MeasurableSpace B] [MeasurableSingletonClass B]

set_option maxHeartbeats 1500000 in
theorem realStarSampleLaw_coded (μ : Measure (Fin k × Fin N → ℝ)) (G : RegularGraph N d)
    (mean : Fin k × Fin N → ℝ) (e : (Fin k → B) ≃ Fin q) (J : ℝ → B) (hJ : Measurable J) :
    Measure.map (fun y => flatBundleColorEquiv e (d+1) (fun i => J (y i))) (realStarSampleLaw μ G mean) =
      finiteSampleLaw μ (uniformSampleWeight (Fin N × Equiv.Perm (Fin d)))
        (fun z x => sampledStarWord G (quantizedVertexColor e J (mean+x)) z) := by
  have hm : Measurable (fun y : Fin (k*(d+1)) → ℝ => flatBundleColorEquiv e (d+1) (fun i => J (y i))) :=
    (measurable_of_finite (flatBundleColorEquiv e (d+1))).comp (measurable_pi_lambda _ (fun i => hJ.comp (measurable_pi_apply i)))
  rw [realStarSampleLaw,map_finiteSampleLaw _ _ _ (by intro z; fun_prop) _ hm]
  congr 1
  funext z x
  exact flatBundleColorEquiv_star e J G z (mean+x)

set_option maxHeartbeats 1500000 in
theorem realEdgeSampleLaw_coded (μ : Measure (Fin k × Fin N → ℝ)) (G : RegularGraph N d)
    (mean : Fin k × Fin N → ℝ) (e : (Fin k → B) ≃ Fin q) (J : ℝ → B) (hJ : Measurable J) :
    Measure.map (fun y => pairColorEquiv (flatBundleColorEquiv e 2 (fun i => J (y i)))) (realEdgeSampleLaw μ G mean) =
      finiteSampleLaw μ (uniformSampleWeight (Fin N × Fin d))
        (fun z x => sampledEdgeWord G (quantizedVertexColor e J (mean+x)) z) := by
  have hm : Measurable (fun y : Fin (k*2) → ℝ => pairColorEquiv (flatBundleColorEquiv e 2 (fun i => J (y i)))) :=
    (measurable_of_finite (pairColorEquiv ∘ flatBundleColorEquiv e 2)).comp
      (measurable_pi_lambda _ (fun i => hJ.comp (measurable_pi_apply i)))
  rw [realEdgeSampleLaw,map_finiteSampleLaw _ _ _ (by intro z; fun_prop) _ hm]
  congr 1
  funext z x
  exact flatBundleColorEquiv_edge e J G z (mean+x)

set_option maxHeartbeats 1500000 in
theorem entropy_mean_star_eq_quantized_sample (μ : Measure (Fin k × Fin N → ℝ)) [IsProbabilityMeasure μ]
    (G : RegularGraph N d) (mean : Fin k × Fin N → ℝ)
    (e : (Fin k → B) ≃ Fin q) (J : ℝ → B) (hJ : Measurable J) :
    Finite.entropy (meanProfile μ (fun x => graphStarProfile G (quantizedVertexColor e J (mean+x)))) =
      Finite.entropy (lawMass (realStarSampleLaw μ G mean) (fun y i => J (y i))) := by
  let Q : (Fin (k*(d+1)) → ℝ) → (Fin (k*(d+1)) → B) := fun y i => J (y i)
  have hQ : Measurable Q := measurable_pi_lambda _ (fun i => hJ.comp (measurable_pi_apply i))
  have hmean := mean_graphStarProfile_eq_sample_law G μ (fun x => quantizedVertexColor e J (mean+x))
    (measurable_quantizedVertexColor e J hJ mean)
  rw [← realStarSampleLaw_coded μ G mean e J hJ] at hmean
  have he : meanProfile μ (fun x => graphStarProfile G (quantizedVertexColor e J (mean+x))) =
      lawMass (realStarSampleLaw μ G mean) (flatBundleColorEquiv e (d+1) ∘ Q) := by
    rw [hmean]
    funext s
    exact lawMass_map (realStarSampleLaw μ G mean) (flatBundleColorEquiv e (d+1) ∘ Q)
      ((measurable_of_finite (flatBundleColorEquiv e (d+1))).comp hQ) id measurable_id s
  rw [he]
  exact finite_entropy_law_equiv _ Q (flatBundleColorEquiv e (d+1))

set_option maxHeartbeats 1500000 in
theorem entropy_mean_edge_eq_quantized_sample {m : ℕ} (μ : Measure (Fin k × Fin N → ℝ)) [IsProbabilityMeasure μ]
    (G : RegularGraph N d) (hN : 0 < N) (hd : 0 < d) (hNd : N*d = 2*m)
    (mean : Fin k × Fin N → ℝ) (e : (Fin k → B) ≃ Fin q) (J : ℝ → B) (hJ : Measurable J) :
    Finite.entropy (meanProfile μ (fun x => graphEdgeProfile G (quantizedVertexColor e J (mean+x)))) =
      Finite.entropy (lawMass (realEdgeSampleLaw μ G mean) (fun y i => J (y i))) := by
  let Q : (Fin (k*2) → ℝ) → (Fin (k*2) → B) := fun y i => J (y i)
  have hQ : Measurable Q := measurable_pi_lambda _ (fun i => hJ.comp (measurable_pi_apply i))
  have hmean := mean_graphEdgeProfile_eq_sample_law G hN hd hNd μ (fun x => quantizedVertexColor e J (mean+x))
    (measurable_quantizedVertexColor e J hJ mean)
  rw [← realEdgeSampleLaw_coded μ G mean e J hJ] at hmean
  let E := (flatBundleColorEquiv e 2).trans pairColorEquiv
  have he : meanProfile μ (fun x => graphEdgeProfile G (quantizedVertexColor e J (mean+x))) =
      lawMass (realEdgeSampleLaw μ G mean) (E ∘ Q) := by
    rw [hmean]
    funext s
    exact lawMass_map (realEdgeSampleLaw μ G mean) (E ∘ Q)
      ((measurable_of_finite E).comp hQ) id measurable_id s
  rw [he]
  exact finite_entropy_law_equiv _ Q E

end GeneralizedBulk.Graph.Configuration
