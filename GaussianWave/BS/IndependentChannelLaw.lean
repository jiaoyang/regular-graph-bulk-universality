import GaussianWave.GaussianProduct
import GaussianWave.BS.GaussianTreeWave

/-! Literal finite independent products of whole process laws. Finite-window
marginals and their Gaussian covariances are computed from the actual product. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical Topology
namespace GaussianWave.BS

def independentChannelLaw {κ V : Type*} [Fintype κ]
    (Q : κ → Measure (V → ℝ)) : Measure ((κ × V) → ℝ) :=
  Measure.map flattenChannels (Measure.pi Q)

instance independentChannelLaw_probability {κ V : Type*} [Fintype κ]
    (Q : κ → Measure (V → ℝ)) [∀ a, IsProbabilityMeasure (Q a)] :
    IsProbabilityMeasure (independentChannelLaw Q) :=
  isProbabilityMeasure_map measurable_flattenChannels.aemeasurable

theorem independentChannelLaw_window {κ V J : Type*} [Fintype κ]
    (Q : κ → Measure (V → ℝ)) [∀ a, IsProbabilityMeasure (Q a)] (site : J → V) :
    Measure.map (fun z : (κ × V) → ℝ => fun aj : κ × J => z (aj.1,site aj.2))
      (independentChannelLaw Q) =
        independentChannelLaw (fun a => Measure.map (fun z : V → ℝ => fun j => z (site j)) (Q a)) := by
  let W := fun z : V → ℝ => fun j => z (site j)
  have hW : Measurable W := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  letI (a : κ) : IsProbabilityMeasure (Measure.map W (Q a)) := isProbabilityMeasure_map hW.aemeasurable
  have hp := measurePreserving_pi Q (fun a => Measure.map W (Q a))
    (f := fun _ => W) (fun _ => ⟨hW,rfl⟩)
  rw [independentChannelLaw, Measure.map_map
    (measurable_pi_lambda _ (fun _ => measurable_pi_apply _)) measurable_flattenChannels]
  change Measure.map (flattenChannels ∘ (fun z : κ → V → ℝ => fun a => W (z a))) (Measure.pi Q) = _
  rw [← Measure.map_map measurable_flattenChannels hp.measurable,hp.map_eq]
  rfl

theorem independentChannelLaw_block_map {κ V J : Type*} [Fintype κ]
    (Q : κ → Measure (V → ℝ)) [∀ a,IsProbabilityMeasure (Q a)]
    (F : (V → ℝ) → (J → ℝ)) (hF : Measurable F) :
    Measure.map (fun z : (κ × V) → ℝ => fun a => F (fun v => z (a,v)))
      (independentChannelLaw Q) = Measure.pi (fun a => Measure.map F (Q a)) := by
  letI (a : κ) : IsProbabilityMeasure (Measure.map F (Q a)) := isProbabilityMeasure_map hF.aemeasurable
  have hp := measurePreserving_pi Q (fun a => Measure.map F (Q a)) (f := fun _ => F) (fun _ => ⟨hF,rfl⟩)
  have hT : Measurable (fun z : (κ × V) → ℝ => fun a => F (fun v => z (a,v))) :=
    measurable_pi_lambda _ (fun a => hF.comp (measurable_pi_lambda _ (fun v => measurable_pi_apply (a,v))))
  rw [independentChannelLaw,Measure.map_map hT measurable_flattenChannels]
  exact hp.map_eq

theorem independentChannelLaw_gaussian {κ J : Type*} [Fintype κ] [Fintype J]
    [DecidableEq κ] (Q : κ → Measure (J → ℝ)) [∀ a, IsProbabilityMeasure (Q a)]
    (C : κ → Matrix J J ℝ) (hC : ∀ a, HasGaussianCovariance (Q a) (C a)) :
    HasGaussianCovariance (independentChannelLaw Q) (channelBlockCovariance C) := by
  intro t
  rw [independentChannelLaw, integral_map measurable_flattenChannels.aemeasurable]
  · simp_rw [finiteLinearForm_flatten]
    have hexp (x : κ → J → ℝ) :
        Complex.exp ((↑(∑ a,finiteLinearForm (fun i => t (a,i)) (x a)) : ℂ)*Complex.I) =
          ∏ a,Complex.exp ((↑(finiteLinearForm (fun i => t (a,i)) (x a)) : ℂ)*Complex.I) := by
      simp only [Complex.ofReal_sum,Finset.sum_mul,Complex.exp_sum]
    simp_rw [hexp]
    rw [integral_pi_prod_complex Q
      (fun a x => Complex.exp ((↑(finiteLinearForm (fun i => t (a,i)) x) : ℂ)*Complex.I))]
    have hchar (a : κ) :
        (∫ x,Complex.exp ((↑(finiteLinearForm (fun i => t (a,i)) x) : ℂ)*Complex.I) ∂Q a) =
          Complex.exp (↑(-(1/2 : ℝ)*finiteCovarianceQuadratic (C a) (fun i => t (a,i))) : ℂ) :=
      hC a (fun i => t (a,i))
    simp_rw [hchar]
    rw [← Complex.exp_sum]
    congr 1
    rw [finiteCovarianceQuadratic_channelBlock]
    push_cast
    rw [Finset.mul_sum]
  · exact Complex.continuous_exp.measurable.comp
      ((((continuous_finiteLinearForm t).measurable).complex_ofReal).mul measurable_const)
      |>.aestronglyMeasurable

def jointGaussianTreeProcessLaw (r m : ℕ) (energy : ℝ) :
    Measure ((Fin r × RegularTreeVertex (m+2)) → ℝ) :=
  independentChannelLaw (fun _ : Fin r => (gaussianTreeProcessLaw m energy : Measure _))

instance jointGaussianTreeProcessLaw_probability (r m : ℕ) (energy : ℝ) :
    IsProbabilityMeasure (jointGaussianTreeProcessLaw r m energy) :=
  independentChannelLaw_probability _

theorem jointGaussianTreeProcessLaw_finite_wave_kernel
    (r m : ℕ) (energy : ℝ) (he : |energy| < (m+2 : ℝ))
    {J : Type*} [Fintype J] (site : J → RegularTreeVertex (m+2)) :
    HasGaussianCovariance (Measure.map
      (fun z : (Fin r × RegularTreeVertex (m+2)) → ℝ => fun aj : Fin r × J => z (aj.1,site aj.2))
      (jointGaussianTreeProcessLaw r m energy))
      (channelBlockCovariance (fun _ : Fin r => fun i j : J => sphericalCovariance (m+2) energy
        ((regularWordTree (m+2)).dist (site i) (site j)))) := by
  rw [jointGaussianTreeProcessLaw,independentChannelLaw_window]
  letI : IsProbabilityMeasure (Measure.map (fun z : RegularTreeVertex (m+2) → ℝ => fun j => z (site j))
      (gaussianTreeProcessLaw m energy : Measure _)) :=
    isProbabilityMeasure_map (measurable_pi_lambda _ (fun _ => measurable_pi_apply _)).aemeasurable
  exact independentChannelLaw_gaussian _ _ (fun _ => gaussianTreeProcessLaw_finite_wave_kernel m energy he site)

end GaussianWave.BS
