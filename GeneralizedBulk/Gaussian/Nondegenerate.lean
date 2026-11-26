import GeneralizedBulk.Gaussian.Characteristic

/-! # Nondegeneracy of every real linear projection of Gaussian endpoint marks -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace GeneralizedBulk.Gaussian

theorem covarianceQuadratic_pos (p : ℝ) (hp : |p| < 1)
    (t : Fin 4 → ℝ) (ht : t ≠ 0) : 0 < covarianceQuadratic p t := by
  have h := (covarianceMatrix_posDef p hp).2 t ht
  convert h using 1
  simp only [covarianceQuadratic, dotProduct, Matrix.mulVec, star_trivial]
  simp_rw [Finset.mul_sum, mul_assoc]

theorem covarianceQuadratic_nonneg (p : ℝ) (hp : |p| < 1) (t : Fin 4 → ℝ) :
    0 ≤ covarianceQuadratic p t := by
  by_cases ht : t = 0
  · subst t
    simp [covarianceQuadratic]
  · exact (covarianceQuadratic_pos p hp t ht).le

theorem covarianceQuadratic_smul (p s : ℝ) (t : Fin 4 → ℝ) :
    covarianceQuadratic p (fun i => s * t i) = s ^ 2 * covarianceQuadratic p t := by
  simp only [covarianceQuadratic, Fin.sum_univ_four]
  ring

theorem measurable_linearForm (t : Fin 4 → ℝ) : Measurable (linearForm t) := by
  unfold linearForm
  exact Finset.measurable_sum _ (fun i _ => measurable_const.mul (measurable_pi_apply i))

/-- Every linear projection of the constructed Gaussian mark has the actual
one-dimensional Gaussian law with its quadratic-form variance. -/
theorem markLaw_linearProjection (p : ℝ) (hp : |p| < 1) (t : Fin 4 → ℝ) :
    Measure.map (linearForm t) (markLaw p) =
      gaussianReal 0 ⟨covarianceQuadratic p t, covarianceQuadratic_nonneg p hp t⟩ := by
  letI : IsProbabilityMeasure (Measure.map (linearForm t) (markLaw p)) :=
    MeasureTheory.isProbabilityMeasure_map (measurable_linearForm t).aemeasurable
  apply Measure.ext_of_charFun
  funext s
  rw [charFun_apply, charFun_gaussianReal]
  rw [integral_map (measurable_linearForm t).aemeasurable]
  · have h := markLaw_characteristic p hp (fun i => s * t i)
    rw [covarianceQuadratic_smul] at h
    convert h using 1
    · apply integral_congr_ae
      filter_upwards with x
      congr 1
      simp only [linearForm, RCLike.inner_apply, conj_trivial, Fin.sum_univ_four]
      push_cast
      ring
    · congr 1
      push_cast
      ring
  · apply Measurable.aestronglyMeasurable
    fun_prop

theorem markLaw_hyperplane_null (p : ℝ) (hp : |p| < 1)
    (t : Fin 4 → ℝ) (ht : t ≠ 0) :
    markLaw p {y | linearForm t y = 0} = 0 := by
  have hpos := covarianceQuadratic_pos p hp t ht
  have hv : (⟨covarianceQuadratic p t, covarianceQuadratic_nonneg p hp t⟩ : ℝ≥0) ≠ 0 := by
    intro heq
    have := congrArg (fun a : ℝ≥0 => (a : ℝ)) heq
    simpa using hpos.ne' this
  have hz : gaussianReal 0 ⟨covarianceQuadratic p t, covarianceQuadratic_nonneg p hp t⟩ {0} = 0 :=
    gaussianReal_absolutelyContinuous 0 hv (by simp)
  have hm := congrArg (fun μ : Measure ℝ => μ {0}) (markLaw_linearProjection p hp t)
  change Measure.map (linearForm t) (markLaw p) {0} =
    gaussianReal 0 ⟨covarianceQuadratic p t, covarianceQuadratic_nonneg p hp t⟩ {0} at hm
  rw [Measure.map_apply (measurable_linearForm t) (measurableSet_singleton 0), hz] at hm
  exact hm

/-- A proper real linear subspace has zero probability under a nondegenerate
Gaussian mark law. This supplies the fiber step for independent marks spanning. -/
theorem markLaw_properSubmodule_null (p : ℝ) (hp : |p| < 1)
    (S : Submodule ℝ (Fin 4 → ℝ)) (hS : S ≠ ⊤) :
    markLaw p (S : Set (Fin 4 → ℝ)) = 0 := by
  obtain ⟨f, hf, hker⟩ := S.exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hS)
  let t : Fin 4 → ℝ := fun i => f (fun j => if i = j then 1 else 0)
  have hform (y : Fin 4 → ℝ) : linearForm t y = f y := by
    rw [LinearMap.pi_apply_eq_sum_univ f y]
    simp only [linearForm, t, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have ht : t ≠ 0 := by
    intro ht
    apply hf
    apply LinearMap.ext
    intro y
    have hh := hform y
    rw [ht] at hh
    simpa [linearForm] using hh.symm
  refine measure_mono_null ?_ (markLaw_hyperplane_null p hp t ht)
  intro y hy
  change linearForm t y = 0
  rw [hform]
  exact hker hy

end GeneralizedBulk.Gaussian
