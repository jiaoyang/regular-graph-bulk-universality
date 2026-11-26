import GaussianWave.BS.Lower.ProcessRecoloring
import GaussianWave.BS.Lower.PathEdgeComparison
import GaussianWave.BS.Lower.PathRecoloringLimit

/-! Actual process C/E/root marginals and their product-recoloring
consistency. No consistency or marginal-entropy conclusion is an input. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
set_option maxHeartbeats 1200000
namespace GaussianWave.BS.Lower
open GaussianWave.BS GaussianWave.BS.Reused.Entropy GaussianWave.BS.Reused.Entropy.Finite

def vertexProcessWindow {r : ℕ} (m k : ℕ)
    (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) :
    Measure ((Fin r × VertexBallVertex (m+2) k) → ℝ) :=
  Measure.map (processWindowProjection (vertexBallEmbedding (m+2) k)) P

def edgeProcessWindow {r : ℕ} (m k : ℕ)
    (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) :
    Measure ((Fin r × EdgeBallVertex (m+2) k) → ℝ) :=
  Measure.map (processWindowProjection (edgeBallEmbedding m k)) P

def rootProcessWindow {r : ℕ} (m : ℕ)
    (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) : Measure (Fin r → ℝ) :=
  Measure.map (fun z a => z (a,none)) P

instance vertexProcessWindow_probability {r : ℕ} (m k : ℕ)
    (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (vertexProcessWindow m k P) :=
  isProbabilityMeasure_map (measurable_processWindowProjection _).aemeasurable

instance edgeProcessWindow_probability {r : ℕ} (m k : ℕ)
    (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (edgeProcessWindow m k P) :=
  isProbabilityMeasure_map (measurable_processWindowProjection _).aemeasurable

instance rootProcessWindow_probability {r : ℕ} (m : ℕ)
    (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (rootProcessWindow m P) :=
  isProbabilityMeasure_map (measurable_pi_lambda _ (fun a => measurable_pi_apply (a,none))).aemeasurable

theorem edgeProcessWindow_eq_vertex_restrict {r : ℕ} (m k : ℕ)
    (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) :
    edgeProcessWindow m k P=Measure.map (processWindowProjection (edgeToVertexBall m k)) (vertexProcessWindow m k P) := by
  rw [vertexProcessWindow,Measure.map_map (measurable_processWindowProjection _) (measurable_processWindowProjection _)]
  unfold edgeProcessWindow
  congr 1
  funext z av
  simp only [Function.comp_apply,processWindowProjection,edgeToVertexBall_embedding]

theorem rootProcessWindow_eq_vertex_root {r : ℕ} (m k : ℕ)
    (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) :
    rootProcessWindow m P=Measure.map (fun z a => z (a,vertexBallRoot (m+2) k)) (vertexProcessWindow m k P) := by
  rw [vertexProcessWindow,Measure.map_map
    (measurable_pi_lambda _ (fun a => measurable_pi_apply (a,vertexBallRoot (m+2) k)))
    (measurable_processWindowProjection _)]
  rfl

theorem windowRecolorMass_restrict_push {V S : Type*} [Fintype V] [Fintype S] {q r : ℕ}
    (μ : Measure ((Fin r × V) → ℝ)) [IsProbabilityMeasure μ] (site : S ↪ V)
    (φ : (Fin r → ℝ) → Fin q → ℝ)
    (hφ0 : ∀ x b,0 ≤ φ x b) (hφ1 : ∀ x,∑ b,φ x b=1)
    (hφc : ∀ b,Continuous (fun x => φ x b)) :
    pushMass (fun w : V → Fin q => w ∘ site) (windowRecolorMass μ φ)=
      windowRecolorMass (Measure.map (processWindowProjection site) μ) φ := by
  have hi (w : V → Fin q) : Integrable (windowRecolorTest φ w) μ :=
    (windowRecolorBCF φ hφ0 hφ1 hφc w).integrable μ
  funext b
  calc
    _ = ∫ y,∏ i : S,φ (fun a => y (a,site i)) (b i) ∂μ := by
      unfold pushMass windowRecolorMass
      rw [← integral_finset_sum _ (fun w _ => hi w)]
      apply integral_congr_ae
      filter_upwards [] with y
      exact finiteProductMass_restrict_push (fun v => φ (fun a => y (a,v)))
        (fun v => hφ0 _) (fun v => hφ1 _) site b
    _ = _ := by
      have htest : Measurable (windowRecolorTest φ b) :=
        Finset.measurable_prod _ (fun i _ => (hφc (b i)).measurable.comp
          (measurable_pi_lambda _ (fun a => measurable_pi_apply (a,i))))
      rw [windowRecolorMass,integral_map (measurable_processWindowProjection site).aemeasurable htest.aestronglyMeasurable]
      rfl

local instance processCDecidableEq (m k : ℕ) : DecidableEq (VertexBallVertex (m+2) k) := Classical.decEq _
local instance processEDecidableEq (m k : ℕ) : DecidableEq (EdgeBallVertex (m+2) k) := Classical.decEq _

theorem process_recolor_edge_marginal {q r : ℕ} (m k : ℕ)
    (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ)) [IsProbabilityMeasure P]
    (φ : (Fin r → ℝ) → Fin q → ℝ)
    (hφ0 : ∀ x b,0 ≤ φ x b) (hφ1 : ∀ x,∑ b,φ x b=1)
    (hφc : ∀ b,Continuous (fun x => φ x b)) :
    pushMass (fun w : VertexBallVertex (m+2) k → Fin q => w ∘ edgeToVertexBall m k)
      (windowRecolorMass (vertexProcessWindow m k P) φ)=windowRecolorMass (edgeProcessWindow m k P) φ := by
  rw [edgeProcessWindow_eq_vertex_restrict]
  exact windowRecolorMass_restrict_push (vertexProcessWindow m k P) (edgeToVertexBallEmbedding m k) φ hφ0 hφ1 hφc

theorem process_root_entropy_eq_vertex {F : Type*} [Fintype F] {r : ℕ} (m k : ℕ)
    (P : Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ))
    (φ : (Fin r → ℝ) → F → ℝ) (hφc : ∀ b,Continuous (fun x => φ x b)) :
    (∫ x,entropy (φ x) ∂rootProcessWindow m P)=
      ∫ y,windowRootEntropyTest φ (vertexBallRoot (m+2) k) y ∂vertexProcessWindow m k P := by
  have htest : Measurable (fun x : Fin r → ℝ => entropy (φ x)) :=
    Finset.measurable_sum _ (fun b _ => Real.continuous_negMulLog.measurable.comp (hφc b).measurable)
  rw [rootProcessWindow_eq_vertex_root m k P,integral_map
    (measurable_pi_lambda _ (fun a => measurable_pi_apply (a,vertexBallRoot (m+2) k))).aemeasurable htest.aestronglyMeasurable]
  rfl

end GaussianWave.BS.Lower
