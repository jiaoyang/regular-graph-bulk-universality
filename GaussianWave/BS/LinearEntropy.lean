import GaussianWave.BS.EntropyComparison

/-!
# Actual finite-entropy densities under invertible linear coordinates

This is the ordinary differential-entropy Jacobian for arbitrary probability
densities, including densities with zeros. It supplies the coordinate adapter
needed to turn the proved white-coordinate BS inequality into its intrinsic
Gaussian-relative form. No Gaussianity or entropy inequality is assumed.

The density-transport argument is adapted from the user's earlier standalone
Analysis/LinearDensityEntropy proof; no earlier project is imported.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace GaussianWave.BS

theorem map_withDensity_measurableEquiv
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (e : X ≃ᵐ Y) (f : X → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (fun y => f (e.symm y)) := by
  apply Measure.ext_of_lintegral
  intro q hq
  calc
    _ = ∫⁻ x, q (e x) ∂μ.withDensity f := lintegral_map hq e.measurable
    _ = ∫⁻ x, f x * q (e x) ∂μ :=
      lintegral_withDensity_eq_lintegral_mul μ hf (hq.comp e.measurable)
    _ = ∫⁻ y, f (e.symm y) * q y ∂μ.map e := by
      have h := lintegral_map (μ := μ) (f := fun y => f (e.symm y) * q y)
        ((hf.comp e.symm.measurable).mul hq) e.measurable
      simpa only [e.symm_apply_apply] using h.symm
    _ = _ :=
      (lintegral_withDensity_eq_lintegral_mul (μ.map e) (hf.comp e.symm.measurable) hq).symm

theorem map_realDensity_scaled_reference
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (e : X ≃ᵐ X) (s : ℝ) (hs : 0 ≤ s)
    (hmap : μ.map e = ENNReal.ofReal s • μ) (f : X → ℝ) (hf : Measurable f) :
    (μ.withDensity (fun x => ENNReal.ofReal (f x))).map e =
      μ.withDensity (fun y => ENNReal.ofReal (s * f (e.symm y))) := by
  rw [map_withDensity_measurableEquiv μ e _ hf.ennreal_ofReal, hmap, withDensity_smul_measure]
  calc
    _ = μ.withDensity (ENNReal.ofReal s • (fun y => ENNReal.ofReal (f (e.symm y)))) :=
      (withDensity_smul (ENNReal.ofReal s) (hf.comp e.symm.measurable).ennreal_ofReal).symm
    _ = _ := by
      congr 1
      funext y
      exact (ENNReal.ofReal_mul hs).symm

theorem integrable_realDensity_iff
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (f g : X → ℝ)
    (hf : Measurable f) (hpos : ∀ x, 0 ≤ f x) :
    Integrable g (μ.withDensity (fun x => ENNReal.ofReal (f x))) ↔
      Integrable (fun x => f x * g x) μ := by
  simpa only [ENNReal.toReal_ofReal (hpos _), smul_eq_mul] using
    (integrable_withDensity_iff_integrable_smul' hf.ennreal_ofReal
      (ae_of_all μ (fun _ => ENNReal.ofReal_lt_top)) (g := g))

theorem integral_realDensity
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (f g : X → ℝ)
    (hf : Measurable f) (hpos : ∀ x, 0 ≤ f x) :
    (∫ x, g x ∂μ.withDensity (fun x => ENNReal.ofReal (f x))) =
      ∫ x, f x * g x ∂μ := by
  simpa only [ENNReal.toReal_ofReal (hpos _), smul_eq_mul] using
    integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
      (ae_of_all μ (fun _ => ENNReal.ofReal_lt_top)) g

variable {I : Type*} [Fintype I] [DecidableEq I]

def invertibleMatrixEquiv (M : Matrix I I ℝ) (hM : M.det ≠ 0) :
    (I → ℝ) ≃L[ℝ] (I → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
    { Matrix.toLin' M with
      invFun := M⁻¹.mulVec
      left_inv := fun x => by
        change M⁻¹.mulVec (M.mulVec x) = x
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM), Matrix.one_mulVec]
      right_inv := fun x => by
        change M.mulVec (M⁻¹.mulVec x) = x
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hM), Matrix.one_mulVec] }

@[simp] theorem invertibleMatrixEquiv_apply (M : Matrix I I ℝ) (hM : M.det ≠ 0) (x : I → ℝ) :
    invertibleMatrixEquiv M hM x = M.mulVec x := rfl

@[simp] theorem invertibleMatrixEquiv_symm_apply (M : Matrix I I ℝ) (hM : M.det ≠ 0) (x : I → ℝ) :
    (invertibleMatrixEquiv M hM).symm x = M⁻¹.mulVec x := rfl

def invertibleMatrixMeasurableEquiv (M : Matrix I I ℝ) (hM : M.det ≠ 0) :
    (I → ℝ) ≃ᵐ (I → ℝ) := (invertibleMatrixEquiv M hM).toHomeomorph.toMeasurableEquiv

def linearImageDensity (M : Matrix I I ℝ) (f : (I → ℝ) → ℝ) (x : I → ℝ) : ℝ :=
  |M.det|⁻¹ * f (M⁻¹.mulVec x)

theorem measurable_linearImageDensity (M : Matrix I I ℝ) (f : (I → ℝ) → ℝ) (hf : Measurable f) :
    Measurable (linearImageDensity M f) :=
  (hf.comp (measurable_finiteMatrixAction M⁻¹)).const_mul _

theorem linearImageDensity_nonneg (M : Matrix I I ℝ) (f : (I → ℝ) → ℝ)
    (hf : ∀ x, 0 ≤ f x) (x : I → ℝ) : 0 ≤ linearImageDensity M f x :=
  mul_nonneg (by positivity) (hf _)

theorem linearImageDensity_pullback (M : Matrix I I ℝ) (hM : M.det ≠ 0)
    (f : (I → ℝ) → ℝ) (x : I → ℝ) :
    linearImageDensity M f (M.mulVec x) = |M.det|⁻¹ * f x := by
  unfold linearImageDensity
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM), Matrix.one_mulVec]

theorem linearImageDensity_pushforward (M : Matrix I I ℝ) (hM : M.det ≠ 0)
    (f : (I → ℝ) → ℝ) (hf : Measurable f) :
    (volume.withDensity (fun x => ENNReal.ofReal (f x))).map (fun x => M.mulVec x) =
      volume.withDensity (fun x => ENNReal.ofReal (linearImageDensity M f x)) := by
  apply map_realDensity_scaled_reference volume (invertibleMatrixMeasurableEquiv M hM)
    |M.det|⁻¹ (by positivity) _ f hf
  change (volume : Measure (I → ℝ)).map (Matrix.toLin' M) = _
  simpa only [abs_inv] using Real.map_matrix_volume_pi_eq_smul_volume_pi hM

theorem integrable_linearImageDensity_log
    (M : Matrix I I ℝ) (hM : M.det ≠ 0) (f : (I → ℝ) → ℝ)
    (hf : Measurable f) (hpos : ∀ x, 0 ≤ f x)
    (hflog : Integrable (fun x => f x * Real.log (f x)))
    (hprob : IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (f x)))) :
    Integrable (fun x => linearImageDensity M f x * Real.log (linearImageDensity M f x)) := by
  let μ := volume.withDensity (fun x => ENNReal.ofReal (f x))
  let ν := volume.withDensity (fun x => ENNReal.ofReal (linearImageDensity M f x))
  let e := invertibleMatrixMeasurableEquiv M hM
  letI : IsProbabilityMeasure μ := hprob
  have hmap : μ.map e = ν := linearImageDensity_pushforward M hM f hf
  have hlog : Integrable (fun x => Real.log (f x)) μ :=
    (integrable_realDensity_iff volume f _ hf hpos).mpr hflog
  have hposae : ∀ᵐ x ∂μ, 0 < f x := by
    rw [ae_withDensity_iff hf.ennreal_ofReal]
    exact ae_of_all _ (fun x hx => ENNReal.ofReal_ne_zero_iff.mp hx)
  have hlogpull : (fun x => Real.log (linearImageDensity M f (M.mulVec x))) =ᵐ[μ]
      (fun x => -Real.log |M.det| + Real.log (f x)) := by
    filter_upwards [hposae] with x hx
    rw [linearImageDensity_pullback M hM,
      Real.log_mul (inv_ne_zero (abs_ne_zero.mpr hM)) hx.ne', Real.log_inv]
  have hi : Integrable (fun x => Real.log (linearImageDensity M f x)) ν := by
    rw [← hmap]
    apply (integrable_map_equiv e _).mpr
    exact ((integrable_const _).add hlog).congr hlogpull.symm
  exact (integrable_realDensity_iff volume (linearImageDensity M f) _
    (measurable_linearImageDensity M f hf) (linearImageDensity_nonneg M f hpos)).mp hi

/-- Arbitrary nonnegative finite-entropy densities obey the actual linear
Jacobian formula. Density zeros are handled almost everywhere under the law. -/
theorem linearImageDensity_entropy_change
    (M : Matrix I I ℝ) (hM : M.det ≠ 0) (f : (I → ℝ) → ℝ)
    (hf : Measurable f) (hpos : ∀ x, 0 ≤ f x)
    (hflog : Integrable (fun x => f x * Real.log (f x)))
    (hprob : IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (f x)))) :
    densityEntropy volume (linearImageDensity M f) = densityEntropy volume f + Real.log |M.det| := by
  let μ := volume.withDensity (fun x => ENNReal.ofReal (f x))
  let ν := volume.withDensity (fun x => ENNReal.ofReal (linearImageDensity M f x))
  let e := invertibleMatrixMeasurableEquiv M hM
  letI : IsProbabilityMeasure μ := hprob
  have hmap : μ.map e = ν := linearImageDensity_pushforward M hM f hf
  have hlog : Integrable (fun x => Real.log (f x)) μ :=
    (integrable_realDensity_iff volume f _ hf hpos).mpr hflog
  have hposae : ∀ᵐ x ∂μ, 0 < f x := by
    rw [ae_withDensity_iff hf.ennreal_ofReal]
    exact ae_of_all _ (fun x hx => ENNReal.ofReal_ne_zero_iff.mp hx)
  have hlogpull : (fun x => Real.log (linearImageDensity M f (M.mulVec x))) =ᵐ[μ]
      (fun x => -Real.log |M.det| + Real.log (f x)) := by
    filter_upwards [hposae] with x hx
    rw [linearImageDensity_pullback M hM,
      Real.log_mul (inv_ne_zero (abs_ne_zero.mpr hM)) hx.ne', Real.log_inv]
  have hlogν : Integrable (fun x => Real.log (linearImageDensity M f x)) ν := by
    rw [← hmap]
    apply (integrable_map_equiv e _).mpr
    exact ((integrable_const _).add hlog).congr hlogpull.symm
  have hinner : (∫ x, Real.log (linearImageDensity M f x) ∂ν) =
      -Real.log |M.det| + ∫ x, Real.log (f x) ∂μ := by
    rw [← hmap, integral_map e.measurable.aemeasurable]
    · change (∫ x, Real.log (linearImageDensity M f (M.mulVec x)) ∂μ) = _
      rw [integral_congr_ae hlogpull, integral_add (integrable_const _) hlog, integral_const]
      simp only [measureReal_univ_eq_one, smul_eq_mul, one_mul]
    · rw [hmap]
      exact hlogν.aestronglyMeasurable
  have hν := integral_realDensity volume (linearImageDensity M f)
    (fun x => Real.log (linearImageDensity M f x)) (measurable_linearImageDensity M f hf)
    (linearImageDensity_nonneg M f hpos)
  have hμ := integral_realDensity volume f (fun x => Real.log (f x)) hf hpos
  change (∫ x, Real.log (linearImageDensity M f x) ∂ν) = _ at hν
  change (∫ x, Real.log (f x) ∂μ) = _ at hμ
  rw [hν, hμ] at hinner
  unfold densityEntropy
  linarith

/-- The actual finite-entropy density witness transported by a nonsingular
linear map. All density, normalization, and integrability fields are proved. -/
def FiniteEntropyDensity.linearImage
    {μ : Measure (I → ℝ)} [IsProbabilityMeasure μ]
    (f : FiniteEntropyDensity μ) (M : Matrix I I ℝ) (hM : M.det ≠ 0) :
    FiniteEntropyDensity (Measure.map (fun x => M.mulVec x) μ) := by
  let g := linearImageDensity M f.density
  have hgm : Measurable g := measurable_linearImageDensity M f.density f.measurable
  have hgn : ∀ x, 0 ≤ g x := linearImageDensity_nonneg M f.density f.nonneg
  have hmap : Measure.map (fun x => M.mulVec x) μ =
      volume.withDensity (fun x => ENNReal.ofReal (g x)) := by
    rw [f.measure_eq]
    exact linearImageDensity_pushforward M hM f.density f.measurable
  have hprob : IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (g x))) := by
    rw [← hmap]
    exact isProbabilityMeasure_map (measurable_finiteMatrixAction M).aemeasurable
  letI := hprob
  have hmass : (∫⁻ x, ENNReal.ofReal (g x)) = 1 := by
    simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using
      (measure_univ (μ := volume.withDensity (fun x => ENNReal.ofReal (g x))))
  have hgi : Integrable g :=
    (lintegral_ofReal_ne_top_iff_integrable hgm.aestronglyMeasurable
      (ae_of_all _ hgn)).mp (by rw [hmass]; exact ENNReal.one_ne_top)
  have hgone : (∫ x, g x) = 1 := by
    have h := ofReal_integral_eq_lintegral_ofReal hgi (ae_of_all _ hgn)
    rw [hmass] at h
    exact ENNReal.ofReal_eq_one.mp h
  refine ⟨g, hgm, hgn, hgi, hgone, ?_, hmap⟩
  apply integrable_linearImageDensity_log M hM f.density f.measurable f.nonneg f.integrable_log
  rw [← f.measure_eq]
  infer_instance

theorem FiniteEntropyDensity.linearImage_entropy
    {μ : Measure (I → ℝ)} [IsProbabilityMeasure μ]
    (f : FiniteEntropyDensity μ) (M : Matrix I I ℝ) (hM : M.det ≠ 0) :
    (f.linearImage M hM).entropy = f.entropy + Real.log |M.det| := by
  change densityEntropy volume (linearImageDensity M f.density) =
    densityEntropy volume f.density + Real.log |M.det|
  apply linearImageDensity_entropy_change M hM f.density f.measurable f.nonneg f.integrable_log
  rw [← f.measure_eq]
  infer_instance

/-- Gaussian-relative entropy differences are invariant under the same
invertible coordinates. This is the cancellation used by intrinsic whitening. -/
theorem FiniteEntropyDensity.linearImage_entropy_difference
    {μ ν : Measure (I → ℝ)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : FiniteEntropyDensity μ) (g : FiniteEntropyDensity ν)
    (M : Matrix I I ℝ) (hM : M.det ≠ 0) :
    (f.linearImage M hM).entropy - (g.linearImage M hM).entropy = f.entropy - g.entropy := by
  rw [f.linearImage_entropy M hM, g.linearImage_entropy M hM]
  ring

end GaussianWave.BS
