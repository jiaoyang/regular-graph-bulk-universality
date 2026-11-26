import GaussianWave.BS.HeatDeconvolution
import GaussianWave.BS.UpperBound

/-!
# Actual Gaussian attainment of the entropy upper bound

The reference is an actual independent product Gaussian probability measure,
and every edge reference is its actual orthonormal pushforward. Entropy does
not depend on which finite-entropy density witnesses are supplied.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianWave.BS

def FiniteEntropyDensity.cast {I : Type*} [Fintype I]
    {μ ν : Measure (I → ℝ)} (f : FiniteEntropyDensity μ) (hν : ν = μ) : FiniteEntropyDensity ν where
  density := f.density
  measurable := f.measurable
  nonneg := f.nonneg
  integrable := f.integrable
  integral_eq_one := f.integral_eq_one
  integrable_log := f.integrable_log
  measure_eq := hν.trans f.measure_eq

@[simp] theorem FiniteEntropyDensity.cast_entropy {I : Type*} [Fintype I]
    {μ ν : Measure (I → ℝ)} (f : FiniteEntropyDensity μ) (hν : ν = μ) :
    (f.cast hν).entropy = f.entropy := rfl

def heatGaussianEntropyDensity (I : Type*) [Fintype I] {t : ℝ} (ht : 0 < t) :
    FiniteEntropyDensity (heatGaussian I t) where
  density := heatKernel t
  measurable := measurable_heatKernel t
  nonneg := heatKernel_nonneg t
  integrable := integrable_heatKernel t
  integral_eq_one := integral_heatKernel ht
  integrable_log := integrable_heatKernel_log ht
  measure_eq := heatGaussian_eq_withDensity ht

theorem heatGaussianEntropyDensity_entropy (I : Type*) [Fintype I] {t : ℝ} (ht : 0 < t) :
    (heatGaussianEntropyDensity I ht).entropy = gaussianEntropyValue I (heatVariance t) :=
  densityEntropy_heatKernel ht

def standardVectorEntropyDensity (I : Type*) [Fintype I] : FiniteEntropyDensity (standardVector I) :=
  (heatGaussianEntropyDensity I (by norm_num : (0 : ℝ) < 1 / 2)).cast
    (heatGaussian_half_eq_standardVector I).symm

theorem standardVectorEntropyDensity_entropy (I : Type*) [Fintype I] :
    (standardVectorEntropyDensity I).entropy = gaussianEntropyValue I 1 := by
  unfold standardVectorEntropyDensity
  rw [FiniteEntropyDensity.cast_entropy, heatGaussianEntropyDensity_entropy]
  congr 1
  ext
  norm_num [heatVariance]

theorem standardVector_map_orthonormal_rows
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (O : Matrix J I ℝ) (hO : O * O.transpose = 1) :
    Measure.map (fun x => O.mulVec x) (standardVector I) = standardVector J := by
  rw [← heatGaussian_half_eq_standardVector I,
    heatGaussian_map_orthonormal_rows _ hO, heatGaussian_half_eq_standardVector J]

theorem eq_standardVector_of_empty_coordinates
    (I : Type*) [Fintype I] [IsEmpty I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] : μ = standardVector I := by
  apply measure_eq_of_linear_characteristic
  intro s
  simp [finiteLinearForm]

theorem standardVector_starEdgeProjection
    (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1) (i : Fin d) :
    Measure.map (fun x => (starEdgeProjection d c i).mulVec x) (standardVector (Fin d)) =
      standardVector Bool := by
  rw [← heatGaussian_half_eq_standardVector (Fin d),
    heatGaussian_map_orthonormal_rows _ (starEdgeProjection_mul_transpose d hd c hc i),
    heatGaussian_half_eq_standardVector Bool]

/-- The Gaussian reference actually attains equality, for any density
versions representing its star and edge laws. -/
theorem star_initialFrameEntropy_standardVector_eq_zero
    (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1)
    (f : FiniteEntropyDensity (standardVector (Fin d)))
    (g : ∀ i, FiniteEntropyDensity
      (Measure.map (fun x => (starEdgeProjection d c i).mulVec x) (standardVector (Fin d)))) :
    initialFrameEntropy f g = 0 := by
  have hf : f.entropy = gaussianEntropyValue (Fin d) 1 := by
    rw [f.entropy_eq_of_measure_eq (standardVectorEntropyDensity _) rfl,
      standardVectorEntropyDensity_entropy]
  have hg (i : Fin d) : (g i).entropy = gaussianEntropyValue Bool 1 := by
    rw [(g i).entropy_eq_of_measure_eq (standardVectorEntropyDensity Bool)
      (standardVector_starEdgeProjection d hd c hc i), standardVectorEntropyDensity_entropy]
  unfold initialFrameEntropy
  rw [hf]
  simp_rw [hg]
  apply gaussianFrameEntropyValue_eq_zero (Fin d) Bool (Fin d)
  simp only [Fintype.card_fin, Fintype.card_bool]
  ring

end GaussianWave.BS
