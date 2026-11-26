import GaussianWave.BS.IndependentAdditionMoments
import GaussianWave.BS.ChannelProcessTransform

/-! The literal independent sum of two entire tree processes, its actual
finite-window laws, and its invariant eigenprocess properties. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GaussianWave.BS

def independentTreeSumLaw {r d : ℕ}
    (μ ν : Measure ((Fin r × RegularTreeVertex d) → ℝ)) :=
  Measure.map (fun p : ((Fin r × RegularTreeVertex d) → ℝ) ×
    ((Fin r × RegularTreeVertex d) → ℝ) => p.1+p.2) (μ.prod ν)

theorem measurable_treeSum {r d : ℕ} :
    Measurable (fun p : ((Fin r × RegularTreeVertex d) → ℝ) ×
      ((Fin r × RegularTreeVertex d) → ℝ) => p.1+p.2) :=
  (continuous_fst.add continuous_snd).measurable

instance independentTreeSumLaw_probability {r d : ℕ}
    (μ ν : Measure ((Fin r × RegularTreeVertex d) → ℝ))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (independentTreeSumLaw μ ν) :=
  isProbabilityMeasure_map measurable_treeSum.aemeasurable

theorem independentTreeSumLaw_map {r d : ℕ} {I : Type*} [Fintype I]
    (μ ν : Measure ((Fin r × RegularTreeVertex d) → ℝ))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : ((Fin r × RegularTreeVertex d) → ℝ) → (I → ℝ)) (hF : Measurable F)
    (hadd : ∀ x y,F (x+y)=F x+F y) :
    Measure.map F (independentTreeSumLaw μ ν)=
      independentAddLaw (Measure.map F μ) (Measure.map F ν) 1 := by
  have hA : Measurable (fun p : (I → ℝ) × (I → ℝ) => p.1+(1 : ℝ) • p.2) :=
    (continuous_fst.add (continuous_const.smul continuous_snd)).measurable
  rw [independentTreeSumLaw,Measure.map_map hF measurable_treeSum,independentAddLaw,
    Measure.map_prod_map μ ν hF hF,Measure.map_map hA (hF.prodMap hF)]
  congr 1
  funext p
  exact (hadd p.1 p.2).trans (by simp only [Function.comp_apply,one_smul]; rfl)

theorem independentTreeSumLaw_window {r d : ℕ} {J : Type*} [Fintype J]
    (μ ν : Measure ((Fin r × RegularTreeVertex d) → ℝ))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (site : J → RegularTreeVertex d) :
    Measure.map (fun z : (Fin r × RegularTreeVertex d) → ℝ => fun aj : Fin r × J => z (aj.1,site aj.2))
      (independentTreeSumLaw μ ν)=
        independentAddLaw
          (Measure.map (fun z : (Fin r × RegularTreeVertex d) → ℝ => fun aj : Fin r × J => z (aj.1,site aj.2)) μ)
          (Measure.map (fun z : (Fin r × RegularTreeVertex d) → ℝ => fun aj : Fin r × J => z (aj.1,site aj.2)) ν) 1 :=
  independentTreeSumLaw_map μ ν _ (measurable_pi_lambda _ (fun _ => measurable_pi_apply _)) (fun _ _ => rfl)

theorem rootChannelLaw_independentTreeSum {r d : ℕ}
    (μ ν : Measure ((Fin r × RegularTreeVertex d) → ℝ))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    rootChannelLaw (independentTreeSumLaw μ ν)=
      independentAddLaw (rootChannelLaw μ) (rootChannelLaw ν) 1 :=
  independentTreeSumLaw_map μ ν _ measurable_rootChannel (fun _ _ => rfl)

theorem independentTreeSumLaw_invariant {r d : ℕ}
    (μ ν : Measure ((Fin r × RegularTreeVertex d) → ℝ))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ChannelTreeInvariant μ) (hν : ChannelTreeInvariant ν) :
    ChannelTreeInvariant (independentTreeSumLaw μ ν) := by
  intro e
  let R := channelTreeRelabel (r := r) e
  let A := fun p : ((Fin r × RegularTreeVertex d) → ℝ) ×
      ((Fin r × RegularTreeVertex d) → ℝ) => p.1+p.2
  have hR : Measurable R := measurable_channelTreeRelabel e
  have hprod : Measure.map (Prod.map R R) (μ.prod ν)=μ.prod ν := by
    rw [← Measure.map_prod_map μ ν hR hR,hμ e,hν e]
  change Measure.map R (Measure.map A (μ.prod ν))=Measure.map A (μ.prod ν)
  rw [Measure.map_map hR measurable_treeSum]
  have hc : R ∘ A=A ∘ Prod.map R R := rfl
  rw [hc,← Measure.map_map measurable_treeSum (hR.prodMap hR),hprod]

theorem independentTreeSumLaw_integrable_square {r d : ℕ}
    (μ ν : Measure ((Fin r × RegularTreeVertex d) → ℝ))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ av,Integrable (fun x => x av^2) μ)
    (hν : ∀ av,Integrable (fun x => x av^2) ν) (av : Fin r × RegularTreeVertex d) :
    Integrable (fun x => x av^2) (independentTreeSumLaw μ ν) := by
  apply (integrable_map_measure ((measurable_pi_apply av).pow_const 2).aestronglyMeasurable
    measurable_treeSum.aemeasurable).mpr
  have hl : Integrable (fun p : ((Fin r × RegularTreeVertex d) → ℝ) ×
      ((Fin r × RegularTreeVertex d) → ℝ) => p.1 av^2) (μ.prod ν) := by
    simpa only [mul_one] using (hμ av).mul_prod
      (integrable_const (1 : ℝ) : Integrable (fun _ : (Fin r × RegularTreeVertex d) → ℝ => (1 : ℝ)) ν)
  have hr : Integrable (fun p : ((Fin r × RegularTreeVertex d) → ℝ) ×
      ((Fin r × RegularTreeVertex d) → ℝ) => p.2 av^2) (μ.prod ν) := by
    simpa only [one_mul] using
      (integrable_const (1 : ℝ) : Integrable (fun _ : (Fin r × RegularTreeVertex d) → ℝ => (1 : ℝ)) μ).mul_prod (hν av)
  have hml := (memLp_two_iff_integrable_sq ((measurable_pi_apply av).comp measurable_fst).aestronglyMeasurable).2 hl
  have hmr := (memLp_two_iff_integrable_sq ((measurable_pi_apply av).comp measurable_snd).aestronglyMeasurable).2 hr
  exact (memLp_two_iff_integrable_sq
    ((measurable_pi_apply av).comp measurable_treeSum).aestronglyMeasurable).1 (hml.add hmr)

theorem independentTreeSumLaw_eigenrelations {r d : ℕ}
    (μ ν : Measure ((Fin r × RegularTreeVertex d) → ℝ))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (energy : ℝ)
    (hμ : ∀ a v,∀ᵐ x ∂μ,treeEigenResidual d r (fun _ => energy) a v x=0)
    (hν : ∀ a v,∀ᵐ x ∂ν,treeEigenResidual d r (fun _ => energy) a v x=0)
    (a : Fin r) (v : RegularTreeVertex d) :
    ∀ᵐ x ∂independentTreeSumLaw μ ν,treeEigenResidual d r (fun _ => energy) a v x=0 := by
  let R := treeEigenResidual d r (fun _ => energy) a v
  have hR : Measurable R := (continuous_treeEigenResidual _ _ _ _ _).measurable
  apply (ae_map_iff measurable_treeSum.aemeasurable (measurableSet_eq_fun hR measurable_const)).2
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun (hR.comp measurable_treeSum) measurable_const)).2
  filter_upwards [hμ a v] with x hx
  filter_upwards [hν a v] with y hy
  change treeEigenResidual d r (fun _ => energy) a v (x+y)=0
  change (∑ z : (regularWordTree d).neighborSet v,x (a,z.val))-energy*x (a,v)=0 at hx
  change (∑ z : (regularWordTree d).neighborSet v,y (a,z.val))-energy*y (a,v)=0 at hy
  simp only [treeEigenResidual,Pi.add_apply,Finset.sum_add_distrib]
  linarith

end GaussianWave.BS
