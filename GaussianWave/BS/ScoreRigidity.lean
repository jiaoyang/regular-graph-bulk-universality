import GaussianWave.BS.ScoreRotation
import GaussianWave.BS.ThirdDerivativeSymmetry
import GaussianWave.BS.FisherMonotonicity

/-!
# Vanishing actual score residuals imply a mixed log-Hessian kernel

The conditional-score identity is already proved for actual arbitrary heated
laws. Equality of the genuine L2 score projection is upgraded to pointwise
equality using the strictly positive heat density and continuity. Along a
kernel direction of the observation the marginal score is constant, so its
derivative is zero. No score-fiber constancy or Hessian-kernel condition is an
input.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

namespace GaussianWave.BS

theorem heatDirectionalScore_eq_log_fderiv
    {I : Type*} [Fintype I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t)
    (v x : I → ℝ) :
    heatDirectionalScore μ t v x =
      fderiv ℝ (fun y => Real.log (heatDensity μ t y)) x v := by
  have hd := hasFDerivAt_heatDensity μ ht x
  have hl := hd.log (heatDensity_pos μ ht x).ne'
  rw [heatDirectionalScore_eq_fderiv μ ht, hl.fderiv, hd.fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem continuous_heatDirectionalScore
    {I : Type*} [Fintype I] [DecidableEq I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t) (v : I → ℝ) :
    Continuous (heatDirectionalScore μ t v) := by
  have hlog := contDiff_three_log_heatDensity μ ht
  have hD : ContDiff ℝ 2 (fderiv ℝ (fun y => Real.log (heatDensity μ t y))) :=
    hlog.fderiv_right (by norm_num)
  have hc := hD.continuous.clm_apply (continuous_const : Continuous (fun _ : I → ℝ => v))
  simpa only [← heatDirectionalScore_eq_log_fderiv μ ht] using hc

/-- Strict positivity of the actual heat density makes its null sets exactly
the Lebesgue null sets. -/
theorem ae_heatedLaw_iff_ae_volume
    {I : Type*} [Fintype I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t)
    (p : (I → ℝ) → Prop) :
    (∀ᵐ x ∂heatedLaw μ t, p x) ↔ ∀ᵐ x ∂volume, p x := by
  rw [heatedLaw_eq_withDensity μ ht, ae_withDensity_iff (measurable_heatDensity μ t).ennreal_ofReal]
  constructor
  · intro h
    filter_upwards [h] with x hx
    exact hx (ENNReal.ofReal_pos.mpr (heatDensity_pos μ ht x)).ne'
  · intro h
    exact h.mono (fun _ hp _ => hp)

/-- Zero genuine L2 projection residual implies that the actual smooth score
is pointwise a function of the actual orthonormal-row observation. -/
theorem heatDirectionalScore_eq_marginal_of_scores_fixed
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t)
    (O : Matrix J I ℝ) (hO : O * O.transpose = 1) (j : J)
    (hfixed : heatDirectionalScoreL2 μ ht (O j) = conditionalScore (heatedLaw μ t)
      (MeasurableSpace.comap (fun x : I → ℝ => O.mulVec x) inferInstance)
      (measurable_finiteMatrixAction O).comap_le (heatDirectionalScoreL2 μ ht (O j)))
    (x : I → ℝ) :
    heatDirectionalScore μ t (O j) x =
      heatDirectionalScore (Measure.map (fun y : I → ℝ => O.mulVec y) μ)
        t (Pi.single j 1) (O.mulVec x) := by
  let μO := Measure.map (fun y : I → ℝ => O.mulVec y) μ
  letI : IsProbabilityMeasure μO := isProbabilityMeasure_map (measurable_finiteMatrixAction O).aemeasurable
  have hL2 := heatDirectionalScoreL2_ae_eq μ ht (O j)
  rw [hfixed] at hL2
  have hae := hL2.symm.trans (conditionalScore_heatDirectionalScore_orthonormal_rows μ ht O hO j)
  have hvol := (ae_heatedLaw_iff_ae_volume μ ht _).mp hae
  have hcontinuous : Continuous (fun y : I → ℝ =>
      heatDirectionalScore μO t (Pi.single j 1) (O.mulVec y)) :=
    (continuous_heatDirectionalScore μO ht (Pi.single j 1)).comp
      (continuous_const.matrix_mulVec continuous_id)
  exact congrFun (Measure.eq_of_ae_eq hvol (continuous_heatDirectionalScore μ ht (O j)) hcontinuous) x

/-- The concrete U7 mixed-Hessian conclusion from one zero actual score
projection residual. The first direction lies in the kernel of the observed
orthonormal rows, and the second is one observed row. -/
theorem log_heatDensity_hessian_kernel_of_scores_fixed
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t)
    (O : Matrix J I ℝ) (hO : O * O.transpose = 1) (j : J)
    (hfixed : heatDirectionalScoreL2 μ ht (O j) = conditionalScore (heatedLaw μ t)
      (MeasurableSpace.comap (fun x : I → ℝ => O.mulVec x) inferInstance)
      (measurable_finiteMatrixAction O).comap_le (heatDirectionalScoreL2 μ ht (O j)))
    (x u : I → ℝ) (hu : O.mulVec u = 0) :
    fderiv ℝ (fderiv ℝ (fun y => Real.log (heatDensity μ t y))) x u (O j) = 0 := by
  let L : (I → ℝ) → ℝ := fun y => Real.log (heatDensity μ t y)
  have hD : ContDiff ℝ 2 (fderiv ℝ L) :=
    (contDiff_three_log_heatDensity μ ht).fderiv_right (by norm_num)
  have hline := (((hD.differentiable (by norm_num) x).hasFDerivAt).hasLineDerivAt u).clm_apply
    (hasDerivAt_const 0 (O j))
  simp only [zero_smul, add_zero, map_zero] at hline
  have heq : (fun s : ℝ => fderiv ℝ L (x + s • u) (O j)) =
      (fun _ : ℝ => heatDirectionalScore (Measure.map (fun y : I → ℝ => O.mulVec y) μ)
        t (Pi.single j 1) (O.mulVec x)) := by
    funext s
    rw [← heatDirectionalScore_eq_log_fderiv μ ht]
    rw [heatDirectionalScore_eq_marginal_of_scores_fixed μ ht O hO j hfixed]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hu, smul_zero, add_zero]
  rw [heq] at hline
  simpa only [L, map_zero, add_zero] using hline.unique (hasDerivAt_const 0 _)

theorem log_heatDensity_hessian_kernel_of_residual_zero
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t)
    (O : Matrix J I ℝ) (hO : O * O.transpose = 1) (j : J)
    (hres : heatDirectionalScoreL2 μ ht (O j) - conditionalScore (heatedLaw μ t)
      (MeasurableSpace.comap (fun x : I → ℝ => O.mulVec x) inferInstance)
      (measurable_finiteMatrixAction O).comap_le (heatDirectionalScoreL2 μ ht (O j)) = 0)
    (x u : I → ℝ) (hu : O.mulVec u = 0) :
    fderiv ℝ (fderiv ℝ (fun y => Real.log (heatDensity μ t y))) x u (O j) = 0 :=
  log_heatDensity_hessian_kernel_of_scores_fixed μ ht O hO j (sub_eq_zero.mp hres) x u hu

private theorem transpose_mulVec_eq_sum_rows
    {I J : Type*} [Fintype I] [Fintype J]
    (O : Matrix J I ℝ) (w : J → ℝ) :
    O.transpose.mulVec w = ∑ j, w j • O j := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

theorem log_heatDensity_hessian_range_of_scores_fixed
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t)
    (O : Matrix J I ℝ) (hO : O * O.transpose = 1)
    (hfixed : ∀ j, heatDirectionalScoreL2 μ ht (O j) = conditionalScore (heatedLaw μ t)
      (MeasurableSpace.comap (fun x : I → ℝ => O.mulVec x) inferInstance)
      (measurable_finiteMatrixAction O).comap_le (heatDirectionalScoreL2 μ ht (O j)))
    (x u : I → ℝ) (hu : O.mulVec u = 0) (w : J → ℝ) :
    fderiv ℝ (fderiv ℝ (fun y => Real.log (heatDensity μ t y))) x u
      (O.transpose.mulVec w) = 0 := by
  rw [transpose_mulVec_eq_sum_rows, map_sum]
  simp_rw [map_smul, log_heatDensity_hessian_kernel_of_scores_fixed μ ht O hO _ (hfixed _) x u hu,
    smul_zero]
  exact Finset.sum_const_zero

/-- The mixed plane/complement log-Hessian kernel required by the literal
star rigidity algebra. It follows from zero actual score residuals in all
observed rows, with no pointwise score premise. -/
theorem log_heatDensity_hessian_projection_mixed_of_scores_fixed
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t)
    (O : Matrix J I ℝ) (hO : O * O.transpose = 1)
    (hfixed : ∀ j, heatDirectionalScoreL2 μ ht (O j) = conditionalScore (heatedLaw μ t)
      (MeasurableSpace.comap (fun x : I → ℝ => O.mulVec x) inferInstance)
      (measurable_finiteMatrixAction O).comap_le (heatDirectionalScoreL2 μ ht (O j)))
    (x u v : I → ℝ) :
    fderiv ℝ (fderiv ℝ (fun y => Real.log (heatDensity μ t y))) x
      (u - O.transpose.mulVec (O.mulVec u)) (O.transpose.mulVec (O.mulVec v)) = 0 := by
  apply log_heatDensity_hessian_range_of_scores_fixed μ ht O hO hfixed x _ _ (O.mulVec v)
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hO, Matrix.one_mulVec, sub_self]

/-- Zero actual BS Fisher defect in the strict bulk yields the concrete
mixed log-Hessian kernel of every actual edge plane. The conditional-score
equalities are derived internally from the positive weighted residual sum. -/
theorem star_log_heatDensity_hessian_mixed_of_fisherDefect_zero
    (d : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t)
    (hrev : ∀ i, Measure.map binarySwap
      (Measure.map (fun x => (starEdgeProjection d c i).mulVec x) μ) =
        Measure.map (fun x => (starEdgeProjection d c i).mulVec x) μ)
    (hzero : heatFrameFisherDefect μ (starEdgeProjection d c) t = 0)
    (x : Fin d → ℝ) (i : Fin d) (u v : Fin d → ℝ) :
    let O := starEdgeProjection d c i
    fderiv ℝ (fderiv ℝ (fun y => Real.log (heatDensity μ t y))) x
      (u - O.transpose.mulVec (O.mulVec u)) (O.transpose.mulVec (O.mulVec v)) = 0 := by
  apply log_heatDensity_hessian_projection_mixed_of_scores_fixed μ ht (starEdgeProjection d c i)
    (starEdgeProjection_mul_transpose d (by omega) c (bulk_rho_lower d hd c hbulk).1 i)
    (star_heatFrameFisherDefect_eq_zero_scores_fixed d hd c hbulk μ ht hrev hzero i) x u v

end GaussianWave.BS
