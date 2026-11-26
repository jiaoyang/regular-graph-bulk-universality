import GaussianWave.BS.HeatQuantizationLimits
import GaussianWave.BS.HeatSymmetry

/-! Actual coordinate relabeling preserves product volume, Gaussian heat,
quantizer laws, and differential/discrete entropies. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology Classical
namespace GaussianWave.BS
open Reused.Entropy

variable {I J : Type*}

def coordinateReindex {A : Type*} (e : I ≃ J) (x : I → A) : J → A := fun j => x (e.symm j)

def coordinateReindexEquiv (A : Type*) (e : I ≃ J) : (I → A) ≃ (J → A) where
  toFun := coordinateReindex e
  invFun := coordinateReindex e.symm
  left_inv := by intro x; ext i; simp [coordinateReindex]
  right_inv := by intro x; ext j; simp [coordinateReindex]

def coordinateReindexMeasurableEquiv (A : Type*) [MeasurableSpace A] (e : I ≃ J) :
    (I → A) ≃ᵐ (J → A) where
  toEquiv := coordinateReindexEquiv A e
  measurable_toFun := measurable_pi_lambda _ (fun j => measurable_pi_apply _)
  measurable_invFun := measurable_pi_lambda _ (fun i => measurable_pi_apply _)

theorem measurable_coordinateReindex {A : Type*} [MeasurableSpace A] (e : I ≃ J) :
    Measurable (coordinateReindex (A := A) e) := (coordinateReindexMeasurableEquiv A e).measurable

theorem coordinateReindex_eq_piCongrLeft {A : Type*} [MeasurableSpace A] (e : I ≃ J) :
    coordinateReindex (A := A) e = MeasurableEquiv.piCongrLeft (fun _ : J => A) e := by
  funext x j
  obtain ⟨i, rfl⟩ := e.surjective j
  rw [MeasurableEquiv.piCongrLeft_apply_apply]
  simp [coordinateReindex]

@[simp] theorem coordinateReindex_apply_image {A : Type*} (e : I ≃ J) (x : I → A) (i : I) :
    coordinateReindex e x (e i) = x i := by simp [coordinateReindex]

@[simp] theorem coordinateReindex_sub (e : I ≃ J) (x y : I → ℝ) :
    coordinateReindex e (x-y) = coordinateReindex e x - coordinateReindex e y := rfl

@[simp] theorem coordinateReindex_add (e : I ≃ J) (x y : I → ℝ) :
    coordinateReindex e (x+y) = coordinateReindex e x + coordinateReindex e y := rfl

section Finite
variable [Fintype I] [Fintype J]

theorem coordinateReindex_volumePreserving (e : I ≃ J) :
    MeasurePreserving (coordinateReindex (A := ℝ) e) volume volume := by
  rw [coordinateReindex_eq_piCongrLeft]
  exact volume_measurePreserving_piCongrLeft (fun _ : J => ℝ) e

theorem heatGaussian_map_coordinateReindex (e : I ≃ J) (t : ℝ) :
    Measure.map (coordinateReindex e) (heatGaussian I t) = heatGaussian J t := by
  rw [coordinateReindex_eq_piCongrLeft]
  exact (measurePreserving_piCongrLeft (fun _ : J => ProbabilityTheory.gaussianReal 0 (heatVariance t)) e).map_eq

theorem heatKernel_coordinateReindex (e : I ≃ J) (t : ℝ) (x : I → ℝ) :
    heatKernel t (coordinateReindex e x) = heatKernel t x := by
  unfold heatKernel coordinateReindex
  exact e.symm.prod_comp (fun i => ProbabilityTheory.gaussianPDFReal 0 (heatVariance t) (x i))

theorem heatedLaw_map_coordinateReindex
    (μ : Measure (I → ℝ)) [SFinite μ] (e : I ≃ J) (t : ℝ) :
    Measure.map (coordinateReindex e) (heatedLaw μ t) =
      heatedLaw (Measure.map (coordinateReindex e) μ) t := by
  rw [heatedLaw, heatedLaw, map_convolution_of_measurable_additive μ _ _
    (measurable_coordinateReindex e) (fun _ _ => rfl), heatGaussian_map_coordinateReindex]

theorem heatDensity_coordinateReindex
    (μ : Measure (I → ℝ)) [IsFiniteMeasure μ] (e : I ≃ J) (t : ℝ) (x : I → ℝ) :
    heatDensity (Measure.map (coordinateReindex e) μ) t (coordinateReindex e x) = heatDensity μ t x := by
  unfold heatDensity
  have he : (∫ y, heatKernel t (coordinateReindex e x - y)
      ∂Measure.map (coordinateReindex e) μ) =
      ∫ z, heatKernel t (coordinateReindex e x - coordinateReindex e z) ∂μ :=
    integral_map (measurable_coordinateReindex e).aemeasurable
      (((measurable_heatKernel t).comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
  rw [he]
  simp_rw [← coordinateReindex_sub, heatKernel_coordinateReindex]

theorem heatDensity_entropy_coordinateReindex
    (μ : Measure (I → ℝ)) [IsFiniteMeasure μ] (e : I ≃ J) (t : ℝ) :
    densityEntropy volume (heatDensity (Measure.map (coordinateReindex e) μ) t) =
      densityEntropy volume (heatDensity μ t) := by
  have he := (coordinateReindex_volumePreserving e).integral_comp
    (coordinateReindexMeasurableEquiv ℝ e).measurableEmbedding
    (fun x => heatDensity (Measure.map (coordinateReindex e) μ) t x *
      Real.log (heatDensity (Measure.map (coordinateReindex e) μ) t x))
  change (∫ x, heatDensity (Measure.map (coordinateReindex e) μ) t (coordinateReindex e x) *
      Real.log (heatDensity (Measure.map (coordinateReindex e) μ) t (coordinateReindex e x))) = _ at he
  simp_rw [heatDensity_coordinateReindex] at he
  unfold densityEntropy
  exact congrArg Neg.neg he.symm

theorem squareRadius_coordinateReindex (e : I ≃ J) (x : I → ℝ) :
    squareRadius (coordinateReindex e x) = squareRadius x := by
  unfold squareRadius coordinateReindex
  exact e.symm.sum_comp (fun i => x i ^ 2)

theorem integrable_squareRadius_coordinateReindex
    (μ : Measure (I → ℝ)) (e : I ≃ J) (hμ : Integrable (squareRadius (I := I)) μ) :
    Integrable (squareRadius (I := J)) (Measure.map (coordinateReindex e) μ) := by
  apply (integrable_map_measure continuous_squareRadius.measurable.aestronglyMeasurable
    (measurable_coordinateReindex e).aemeasurable).mpr
  change Integrable (fun x => squareRadius (coordinateReindex e x)) μ
  simpa only [squareRadius_coordinateReindex] using hμ
end Finite

def coordinatewiseQuantizer {A B : Type*} (q : A → B) (x : I → A) : I → B := fun i => q (x i)

theorem lawMass_reindex_coordinatewiseQuantizer
    [Fintype I] [Fintype J]
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass B] (μ : Measure (I → A))
    (e : I ≃ J) (q : A → B) (hq : Measurable q) (b : I → B) :
    lawMass (Measure.map (coordinateReindex e) μ) (coordinatewiseQuantizer q)
      (coordinateReindex e b) = lawMass μ (coordinatewiseQuantizer q) b := by
  have hm : Measurable (coordinatewiseQuantizer (I := J) q) := by
    apply measurable_pi_lambda
    intro j
    exact hq.comp (measurable_pi_apply j)
  rw [lawMass, lawMass, measureReal_def, measureReal_def,
    Measure.map_apply (measurable_coordinateReindex e)
      (hm (measurableSet_singleton _))]
  congr 2
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, funext_iff,
    coordinatewiseQuantizer, coordinateReindex]
  constructor
  · intro h i
    simpa only [e.symm_apply_apply] using h (e i)
  · intro h j
    exact h (e.symm j)

section Entropy
variable [Fintype I] [Fintype J]

theorem finite_quantizer_entropy_coordinateReindex
    {A B : Type*} [MeasurableSpace A] [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
    (μ : Measure (I → A)) (e : I ≃ J) (q : A → B) (hq : Measurable q) :
    Finite.entropy (lawMass (Measure.map (coordinateReindex e) μ) (coordinatewiseQuantizer q)) =
      Finite.entropy (lawMass μ (coordinatewiseQuantizer q)) := by
  unfold Finite.entropy
  rw [← (coordinateReindexEquiv B e).sum_comp]
  apply Finset.sum_congr rfl
  intro b _
  exact congrArg Real.negMulLog (lawMass_reindex_coordinatewiseQuantizer μ e q hq b)

theorem countable_quantizer_entropy_coordinateReindex
    {A B : Type*} [MeasurableSpace A] [Countable B] [MeasurableSpace B] [MeasurableSingletonClass B]
    (μ : Measure (I → A)) (e : I ≃ J) (q : A → B) (hq : Measurable q) :
    countableEntropy (lawMass (Measure.map (coordinateReindex e) μ) (coordinatewiseQuantizer q)) =
      countableEntropy (lawMass μ (coordinatewiseQuantizer q)) := by
  unfold countableEntropy
  rw [← (coordinateReindexEquiv B e).tsum_eq]
  apply tsum_congr
  intro b
  exact congrArg Real.negMulLog (lawMass_reindex_coordinatewiseQuantizer μ e q hq b)
end Entropy
end GaussianWave.BS
