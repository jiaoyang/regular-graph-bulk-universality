import GeneralizedBulk.Analysis.DensityTransport
import GeneralizedBulk.Analysis.ProductDensityEntropy
import GeneralizedBulk.Entropy.GaussianMixtureEntropy

/-! Lebesgue entropy is invariant under literal finite coordinate permutations;
a density on disjoint coordinate blocks has the actual product entropy. -/
noncomputable section
open MeasureTheory
namespace GeneralizedBulk.Analysis
open GeneralizedBulk.Entropy
variable {I J : Type*} [Fintype I] [Fintype J]

def coordinateDensity (e : I ≃ J) (f : (I → ℝ) → ℝ) (y : J → ℝ) : ℝ :=
  f (fun i => y (e i))

theorem measurable_coordinateDensity (e : I ≃ J) (f : (I → ℝ) → ℝ) (hf : Measurable f) :
    Measurable (coordinateDensity e f) := by
  exact hf.comp (by fun_prop)

theorem coordinate_equiv_apply (e : I ≃ J) (y : J → ℝ) :
    MeasurableEquiv.piCongrLeft (fun _ : I => ℝ) e.symm y = fun i => y (e i) := by
  funext i
  simpa only [Equiv.symm_apply_apply] using
    MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : I => ℝ) e.symm y (e i)

theorem integral_coordinateDensity (e : I ≃ J) (f : (I → ℝ) → ℝ) :
    (∫ y, coordinateDensity e f y) = ∫ x, f x := by
  simpa only [coordinate_equiv_apply, coordinateDensity] using
    (volume_measurePreserving_piCongrLeft (fun _ : I => ℝ) e.symm).integral_comp' f

theorem integrable_coordinateDensity_iff (e : I ≃ J) (f : (I → ℝ) → ℝ) :
    Integrable (coordinateDensity e f) volume ↔ Integrable f volume := by
  have hh := (volume_measurePreserving_piCongrLeft (fun _ : I => ℝ) e.symm).integrable_comp_emb
      (g := f) (MeasurableEquiv.piCongrLeft (fun _ : I => ℝ) e.symm).measurableEmbedding
  simpa only [Function.comp_def, coordinate_equiv_apply, coordinateDensity] using hh

theorem differentialEntropy_coordinateDensity (e : I ≃ J) (f : (I → ℝ) → ℝ) :
    differentialEntropy (coordinateDensity e f) = differentialEntropy f := by
  unfold differentialEntropy
  exact congrArg Neg.neg (integral_coordinateDensity e (fun x => f x * Real.log (f x)))

theorem coordinateDensity_pushforward (e : I ≃ J) (f : (I → ℝ) → ℝ) (hf : Measurable f) :
    (volume.withDensity (fun x => ENNReal.ofReal (f x))).map
        (MeasurableEquiv.piCongrLeft (fun _ : J => ℝ) e) =
      volume.withDensity (fun y => ENNReal.ofReal (coordinateDensity e f y)) := by
  rw [map_withDensity_equiv volume _ _ hf.ennreal_ofReal,
    (volume_measurePreserving_piCongrLeft (fun _ : J => ℝ) e).map_eq]
  rfl

def sumProductDensity (f : (I → ℝ) → ℝ) (g : (J → ℝ) → ℝ) (x : (I ⊕ J) → ℝ) : ℝ :=
  f (fun i => x (Sum.inl i)) * g (fun j => x (Sum.inr j))

theorem integral_sumProductDensity (f : (I → ℝ) → ℝ) (g : (J → ℝ) → ℝ) :
    (∫ x, sumProductDensity f g x) = (∫ x, f x) * ∫ y, g y := by
  have hh := (volume_measurePreserving_sumPiEquivProdPi (fun _ : I ⊕ J => ℝ)).integral_comp'
    (fun xy : (I → ℝ) × (J → ℝ) => f xy.1 * g xy.2)
  rw [Measure.volume_eq_prod, integral_prod_mul] at hh
  exact hh

theorem sumProductDensity_entropy (f : (I → ℝ) → ℝ) (g : (J → ℝ) → ℝ)
    (hf : Integrable f volume) (hg : Integrable g volume)
    (hfp : ∀ x, 0 < f x) (hgp : ∀ y, 0 < g y)
    (hflog : Integrable (fun x => f x * Real.log (f x)) volume)
    (hglog : Integrable (fun y => g y * Real.log (g y)) volume)
    (hfnorm : ∫ x, f x = 1) (hgnorm : ∫ y, g y = 1) :
    Integrable (fun z => sumProductDensity f g z * Real.log (sumProductDensity f g z)) volume ∧
      differentialEntropy (sumProductDensity f g) = differentialEntropy f + differentialEntropy g := by
  have hp := product_density_entropy volume volume f g hf hg hfp hgp hflog hglog hfnorm hgnorm
  let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : I ⊕ J => ℝ)
  have he := volume_measurePreserving_sumPiEquivProdPi (fun _ : I ⊕ J => ℝ)
  refine ⟨(he.integrable_comp_emb e.measurableEmbedding).mpr hp.1, ?_⟩
  have hh := he.integral_comp' (fun xy : (I → ℝ) × (J → ℝ) =>
    f xy.1 * g xy.2 * Real.log (f xy.1 * g xy.2))
  unfold differentialEntropy
  rw [Measure.volume_eq_prod] at hh
  rw [show (∫ z, sumProductDensity f g z * Real.log (sumProductDensity f g z)) = _ from hh, hp.2]
  ring

end GeneralizedBulk.Analysis
