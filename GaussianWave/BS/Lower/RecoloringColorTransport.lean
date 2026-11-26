import GaussianWave.BS.Lower.DifferentialEntropyTransfer

/-! Randomized finite-recoloring entropy lower bounds are preserved by any
continuous deterministic change of the whole vector color. All sites use
one common color map; no target entropy inequality is assumed. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GaussianWave.BS.Lower
open Reused.Entropy

variable {V W : Type*} [Fintype V] [Fintype W] {r s : ℕ}

/-- Apply the same vector-color map independently at every spatial site. -/
def sitewiseColorMap (T : (Fin r → ℝ) → (Fin s → ℝ))
    (x : (V × Fin r) → ℝ) : (V × Fin s) → ℝ :=
  fun vb => T (fun a => x (vb.1,a)) vb.2

theorem continuous_sitewiseColorMap (T : (Fin r → ℝ) → (Fin s → ℝ)) (hT : Continuous T) :
    Continuous (sitewiseColorMap (V := V) T) := by
  apply continuous_pi
  intro vb
  exact (continuous_apply vb.2).comp (hT.comp (continuous_pi (fun a => continuous_apply (vb.1,a))))

/-- Actual recolor masses commute with the deterministic color pushforward. -/
theorem recolorMass_map_sitewiseColorMap {F : Type*}
    (μ : Measure ((V × Fin r) → ℝ)) (T : (Fin r → ℝ) → (Fin s → ℝ))
    (hT : Continuous T) (φ : (Fin s → ℝ) → F → ℝ)
    (hφ : ∀ b,Continuous (fun x => φ x b)) :
    recolorMass (Measure.map (sitewiseColorMap T) μ) φ =
      recolorMass μ (fun x b => φ (T x) b) := by
  funext b
  rw [recolorMass,integral_map (continuous_sitewiseColorMap T hT).measurable.aemeasurable]
  · rfl
  · exact (continuous_finset_prod _ (fun v _ =>
      (hφ (b v)).comp (continuous_pi (fun a => continuous_apply (v,a))))).aestronglyMeasurable

/-- Compose every finite probability kernel with the continuous color map.
This derives the target randomized entropy bound from the source bound. -/
theorem HasFiniteRecoloringEntropyLower.map_continuous_color
    (μC : Measure ((V × Fin r) → ℝ)) (μE : Measure ((W × Fin r) → ℝ))
    (μo : Measure (Fin r → ℝ)) (w : ℝ)
    (h : HasFiniteRecoloringEntropyLower μC μE μo w)
    (T : (Fin r → ℝ) → (Fin s → ℝ)) (hT : Continuous T) :
    HasFiniteRecoloringEntropyLower
      (Measure.map (sitewiseColorMap T) μC) (Measure.map (sitewiseColorMap T) μE)
      (Measure.map T μo) w := by
  intro F instF φ hφc hφ0 hφ1
  have hm : AEStronglyMeasurable (fun x => Finite.entropy (φ x)) (Measure.map T μo) := by
    apply Continuous.aestronglyMeasurable
    unfold Finite.entropy
    exact continuous_finset_sum _ (fun b _ => Real.continuous_negMulLog.comp (hφc b))
  rw [integral_map hT.measurable.aemeasurable hm,
    recolorMass_map_sitewiseColorMap μC T hT φ hφc,
    recolorMass_map_sitewiseColorMap μE T hT φ hφc]
  exact h F (fun x b => φ (T x) b) (fun b => (hφc b).comp hT)
    (fun x b => hφ0 (T x) b) (fun x => hφ1 (T x))

end GaussianWave.BS.Lower
