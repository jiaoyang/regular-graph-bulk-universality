import GaussianWave.BS.HeatQuantizerKernel
import GaussianWave.BS.HeatSymmetry
import GaussianWave.GaussianProduct
import GaussianWave.BS.Reused.Entropy.FiniteProduct

/-! Vertexwise independent Gaussian-noise recoloring is the finite quantizer
of the actual ambient Gaussian convolution, including joint vector colors. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Topology Classical
namespace GaussianWave.BS
open Reused.Entropy

/-- Grouping independent coordinate Gaussian noises into arbitrary finite
blocks is an equality of actual probability measures. -/
theorem heatGaussian_eq_flattened_blocks
    (κ ι : Type*) [Fintype κ] [Fintype ι] (t : ℝ) :
    heatGaussian (κ × ι) t =
      Measure.map flattenChannels (Measure.pi (fun _ : κ => heatGaussian ι t)) := by
  letI : ∀ a : κ, IsProbabilityMeasure (heatGaussian ι t) := fun _ => inferInstance
  letI : IsProbabilityMeasure (Measure.pi (fun _ : κ => heatGaussian ι t)) := by
    constructor
    simp only [Measure.pi_univ, measure_univ, Finset.prod_const_one]
  letI : IsProbabilityMeasure (Measure.map flattenChannels
      (Measure.pi (fun _ : κ => heatGaussian ι t))) :=
    isProbabilityMeasure_map measurable_flattenChannels.aemeasurable
  apply measure_eq_of_linear_characteristic
  intro s
  symm
  change (∫ x, (linearCharacteristic s) x
    ∂Measure.map flattenChannels (Measure.pi (fun _ : κ => heatGaussian ι t))) = _
  rw [integral_map measurable_flattenChannels.aemeasurable
    (linearCharacteristic s).continuous.measurable.aestronglyMeasurable]
  change (∫ x : κ → ι → ℝ,
      Complex.exp ((↑(finiteLinearForm s (flattenChannels x)) : ℂ) * Complex.I)
      ∂Measure.pi (fun _ : κ => heatGaussian ι t)) = _
  simp_rw [finiteLinearForm_flatten]
  have he (x : κ → ι → ℝ) :
      Complex.exp ((↑(∑ a, finiteLinearForm (fun i => s (a, i)) (x a)) : ℂ) * Complex.I) =
        ∏ a, Complex.exp ((↑(finiteLinearForm (fun i => s (a, i)) (x a)) : ℂ) * Complex.I) := by
    simp only [Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
  simp_rw [he]
  rw [integral_pi_prod_complex (fun _ : κ => heatGaussian ι t)
    (fun a x => Complex.exp ((↑(finiteLinearForm (fun i => s (a, i)) x) : ℂ) * Complex.I))]
  have hc (a : κ) :
      (∫ x, Complex.exp ((↑(finiteLinearForm (fun i => s (a, i)) x) : ℂ) * Complex.I)
        ∂heatGaussian ι t) =
      Complex.exp (↑(-(1/2 : ℝ)*(heatVariance t : ℝ)*squareMass (fun i => s (a,i))) : ℂ) :=
    heatGaussian_characteristic t _
  simp_rw [hc]
  rw [← Complex.exp_sum]
  change Complex.exp (∑ a, (↑(-(1/2 : ℝ)*(heatVariance t : ℝ)*squareMass (fun i => s (a,i))) : ℂ)) =
    characteristicIntegral (heatGaussian (κ × ι) t) s
  rw [heatGaussian_characteristic]
  congr 1
  simp only [squareMass, Fintype.sum_prod_type]
  push_cast
  simp only [Finset.mul_sum, Complex.ofReal_sum]

def blockQuantizer {κ ι B : Type*} (Q : (ι → ℝ) → B) (x : (κ × ι) → ℝ) : κ → B :=
  fun a => Q (fun i => x (a, i))

theorem measurable_blockQuantizer {κ ι B : Type*} [MeasurableSpace B]
    (Q : (ι → ℝ) → B) (hQ : Measurable Q) : Measurable (blockQuantizer (κ := κ) Q) := by
  apply measurable_pi_lambda
  intro a
  exact hQ.comp (measurable_pi_lambda _ (fun i => measurable_pi_apply (a,i)))

/-- Conditional on a signal, all block recolorings are independent because
this auxiliary Gaussian noise is an actual product. Unknown signal channels
are never assumed independent. -/
theorem heatQuantizerMass_block_product
    {κ ι B : Type*} [Fintype κ] [Fintype ι]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    (Q : (ι → ℝ) → B) (hQ : Measurable Q) (t : ℝ)
    (x : (κ × ι) → ℝ) (b : κ → B) :
    heatQuantizerMass (blockQuantizer Q) t x b =
      ∏ a, heatQuantizerMass Q t (fun i => x (a,i)) (b a) := by
  have hm : MeasurableSet {z : (κ × ι) → ℝ | blockQuantizer Q (x + z) = b} :=
    ((measurable_blockQuantizer Q hQ).comp (measurable_const.add measurable_id)) (measurableSet_singleton b)
  unfold heatQuantizerMass Measure.real
  rw [heatGaussian_eq_flattened_blocks κ ι t, Measure.map_apply measurable_flattenChannels hm]
  have he : flattenChannels ⁻¹' {z : (κ × ι) → ℝ | blockQuantizer Q (x + z) = b} =
      Set.pi Set.univ (fun a : κ => {z : ι → ℝ | Q ((fun i => x (a,i)) + z) = b a}) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_univ_pi, funext_iff, blockQuantizer,
      Pi.add_apply, flattenChannels]
    rfl
  rw [he, Measure.pi_pi, ENNReal.toReal_prod]

/-- The finite-window recolored law is exactly the quantized actual heat
law, expressed by its literal integrated product masses. -/
theorem lawMass_heatedLaw_block_recoloring
    {κ ι B : Type*} [Fintype κ] [Fintype ι]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    (μ : Measure ((κ × ι) → ℝ)) [IsProbabilityMeasure μ]
    (Q : (ι → ℝ) → B) (hQ : Measurable Q) {t : ℝ} (ht : 0 < t) (b : κ → B) :
    lawMass (heatedLaw μ t) (blockQuantizer Q) b =
      ∫ x, ∏ a, heatQuantizerMass Q t (fun i => x (a,i)) (b a) ∂μ := by
  rw [lawMass_heatedLaw_eq_integral_heatQuantizerMass μ _ (measurable_blockQuantizer Q hQ) ht]
  simp_rw [heatQuantizerMass_block_product Q hQ t]
end GaussianWave.BS
