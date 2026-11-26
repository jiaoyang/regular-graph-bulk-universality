import GeneralizedBulk.Gaussian.Family
import GeneralizedBulk.Gaussian.MarkFamily
import GeneralizedBulk.Gaussian.SeriesBounds
import GeneralizedBulk.Gaussian.FieldVersion
import GeneralizedBulk.Gaussian.VersionCovariance

/-!
# The actual independent Gaussian marked series

The field is constructed from the independent standard Gaussian coordinates
and the proved covariance of their correlated endpoint marks. There are no
assumed Wick or series-convergence interfaces in its theorem statements.
-/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped Topology BigOperators

namespace GeneralizedBulk.Gaussian

theorem covariance_entry_variance_le_two (p : ℝ) (hp : |p| < 1) (i j : Fin 4) :
    covarianceMatrix p i i * covarianceMatrix p j j +
      covarianceMatrix p i j * covarianceMatrix p j i ≤ 2 := by
  have hp2 : p ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one p).mpr hp
  rw [covarianceMatrix_eq]
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] <;>
    nlinarith

theorem quadraticLp_inner_off (p : ℝ) (hp : |p| < 1)
    {I : Type*} {n m : I} (hnm : n ≠ m) (i j : Fin 4) :
    @inner ℂ (Lp ℂ 2 (iidLaw standardFour I)) _
      (quadraticLp p n i j) (quadraticLp p m i j) = 0 := by
  rw [l2_inner_eq_bilinear_of_ae_real _ _ _ (quadraticFamily p n i j) (quadraticLp_ae p n i j)]
  exact quadraticLp_off_covariance p hp hnm i j i j

theorem quadraticLp_norm_sq_le_two (p : ℝ) (hp : |p| < 1)
    {I : Type*} (n : I) (i j : Fin 4) :
    ‖quadraticLp p n i j‖ ^ 2 ≤ 2 := by
  rw [l2_norm_sq_of_ae_real _ _ (quadraticFamily p n i j) (quadraticLp_ae p n i j)]
  simp_rw [pow_two]
  rw [quadraticFamily_diagonal_covariance p hp n i j i j]
  exact covariance_entry_variance_le_two p hp i j

theorem quadraticLp_integral_norm_le_three (p : ℝ) (hp : |p| < 1)
    {I : Type*} (n : I) (i j : Fin 4) :
    (∫ ω, ‖quadraticLp p n i j ω‖ ∂iidLaw standardFour I) ≤ 3 := by
  have h := integral_norm_L2_le_one_add_sq (iidLaw standardFour I) (quadraticLp p n i j)
  linarith [quadraticLp_norm_sq_le_two p hp n i j]

/-- The centered raw endpoint field constructed from actual Gaussian marks. -/
def standardMarkedSeries (parameters : Parameters) (s : AnchoredCountingState)
    (v : ℂ × Bool) (ω : s.val.1.ParticleLabels → (Fin 4 → ℝ)) : EndpointMatrix :=
  matrixL2Series (iidLaw standardFour s.val.1.ParticleLabels)
    (fun n i j => quadraticLp parameters.p n i j)
    (fun v n => (parameters.scale : ℂ) * particleCoefficient (s.val.1.particleLocation n) v) v ω

/-- No Wick interface is assumed: the actual Gaussian marked series satisfies
it by the proved Gaussian moments and L² convergence. -/
theorem standardMarkedSeries_entryWick (parameters : Parameters) (s : AnchoredCountingState) :
    EntryWickCovariance (iidLaw standardFour s.val.1.ParticleLabels)
      (parameters.p : ℂ) (parameters.scale : ℂ) (particleKernel s)
      (standardMarkedSeries parameters s) := by
  apply entryWickCovariance_particleSeries _ s (fun n i j => quadraticLp parameters.p n i j)
    (parameters.p : ℂ) (parameters.scale : ℂ) 2 (by norm_num)
  · intro n i j
    exact quadraticLp_norm_sq_le_two _ parameters.abs_p_lt_one n i j
  · intro i j n m hnm
    exact quadraticLp_inner_off _ parameters.abs_p_lt_one hnm i j
  · intro n i j
    exact quadraticLp_mean_zero _ parameters.abs_p_lt_one n i j
  · intro n m hnm i j a b
    exact quadraticLp_off_covariance _ parameters.abs_p_lt_one hnm i j a b
  · intro n i j a b
    exact quadraticLp_diagonal_covariance _ parameters.abs_p_lt_one n i j a b

/-- One common full-measure event supports the genuine complex derivative of
all sample values of every actual Gaussian matrix entry. -/
theorem standardMarkedSeries_analytic_version (parameters : Parameters) (s : AnchoredCountingState)
    (i j : Fin 4) :
    ∀ᵐ ω ∂iidLaw standardFour s.val.1.ParticleLabels, ∀ w : ℂ, w.im ≠ 0 →
      DifferentiableAt ℂ (fun z => analyticL2Entry
        (iidLaw standardFour s.val.1.ParticleLabels) s
        (fun n => quadraticLp parameters.p n i j) (parameters.scale : ℂ) z ω) w := by
  apply analyticL2Entry_differentiable_ae _ s _ _ 3
  intro n
  exact quadraticLp_integral_norm_le_three _ parameters.abs_p_lt_one n i j

/-! The equivalent direct mark-space construction supports literal orthogonal
rotations of each endpoint mark; its covariance law was proved from Gaussianity. -/

theorem markQuadraticLp_inner_off (p : ℝ) (hp : |p| < 1)
    {I : Type*} {n m : I} (hnm : n ≠ m) (i j : Fin 4) :
    @inner ℂ (Lp ℂ 2 (iidLaw (markLaw p) I)) _
      (markQuadraticLp p n i j) (markQuadraticLp p m i j) = 0 := by
  rw [l2_inner_eq_bilinear_of_ae_real _ _ _ (markQuadraticFamily p n i j) (markQuadraticLp_ae p n i j)]
  exact markQuadraticLp_off_covariance p hp hnm i j i j

theorem markQuadraticLp_norm_sq_le_two (p : ℝ) (hp : |p| < 1)
    {I : Type*} (n : I) (i j : Fin 4) :
    ‖markQuadraticLp p n i j‖ ^ 2 ≤ 2 := by
  rw [l2_norm_sq_of_ae_real _ _ (markQuadraticFamily p n i j) (markQuadraticLp_ae p n i j)]
  simp_rw [pow_two]
  rw [markQuadraticFamily_diagonal_covariance p hp n i j i j]
  exact covariance_entry_variance_le_two p hp i j

theorem markQuadraticLp_integral_norm_le_three (p : ℝ) (hp : |p| < 1)
    {I : Type*} (n : I) (i j : Fin 4) :
    (∫ ω, ‖markQuadraticLp p n i j ω‖ ∂iidLaw (markLaw p) I) ≤ 3 := by
  have h := integral_norm_L2_le_one_add_sq (iidLaw (markLaw p) I) (markQuadraticLp p n i j)
  linarith [markQuadraticLp_norm_sq_le_two p hp n i j]

/-- The centered raw endpoint field constructed from actual Gaussian marks. -/
def gaussianMarkedSeries (parameters : Parameters) (s : AnchoredCountingState)
    (v : ℂ × Bool) (ω : s.val.1.ParticleLabels → (Fin 4 → ℝ)) : EndpointMatrix :=
  matrixL2Series (iidLaw (markLaw parameters.p) s.val.1.ParticleLabels)
    (fun n i j => markQuadraticLp parameters.p n i j)
    (fun v n => (parameters.scale : ℂ) * particleCoefficient (s.val.1.particleLocation n) v) v ω

/-- No Wick interface is assumed: the actual Gaussian marked series satisfies
it by the proved Gaussian moments and L² convergence. -/
theorem gaussianMarkedSeries_entryWick (parameters : Parameters) (s : AnchoredCountingState) :
    EntryWickCovariance (iidLaw (markLaw parameters.p) s.val.1.ParticleLabels)
      (parameters.p : ℂ) (parameters.scale : ℂ) (particleKernel s)
      (gaussianMarkedSeries parameters s) := by
  apply entryWickCovariance_particleSeries _ s (fun n i j => markQuadraticLp parameters.p n i j)
    (parameters.p : ℂ) (parameters.scale : ℂ) 2 (by norm_num)
  · intro n i j
    exact markQuadraticLp_norm_sq_le_two _ parameters.abs_p_lt_one n i j
  · intro i j n m hnm
    exact markQuadraticLp_inner_off _ parameters.abs_p_lt_one hnm i j
  · intro n i j
    exact markQuadraticLp_mean_zero _ parameters.abs_p_lt_one n i j
  · intro n m hnm i j a b
    exact markQuadraticLp_off_covariance _ parameters.abs_p_lt_one hnm i j a b
  · intro n i j a b
    exact markQuadraticLp_diagonal_covariance _ parameters.abs_p_lt_one n i j a b

/-- One common full-measure event supports the genuine complex derivative of
all sample values of every actual Gaussian matrix entry. -/
theorem gaussianMarkedSeries_analytic_version (parameters : Parameters) (s : AnchoredCountingState)
    (i j : Fin 4) :
    ∀ᵐ ω ∂iidLaw (markLaw parameters.p) s.val.1.ParticleLabels, ∀ w : ℂ, w.im ≠ 0 →
      DifferentiableAt ℂ (fun z => analyticL2Entry
        (iidLaw (markLaw parameters.p) s.val.1.ParticleLabels) s
        (fun n => markQuadraticLp parameters.p n i j) (parameters.scale : ℂ) z ω) w := by
  apply analyticL2Entry_differentiable_ae _ s _ _ 3
  intro n
  exact markQuadraticLp_integral_norm_le_three _ parameters.abs_p_lt_one n i j

/-- The actual quadratic Gaussian marks satisfy the common weighted absolute
summability event needed for a samplewise analytic version. -/
theorem markQuadraticLp_weighted_summable (parameters : Parameters) (s : AnchoredCountingState)
    (i j : Fin 4) :
    ∀ᵐ ω ∂iidLaw (markLaw parameters.p) s.val.1.ParticleLabels,
      Summable (fun n => nevanlinnaWeight (s.val.1.particleLocation n) *
        ‖markQuadraticLp parameters.p n i j ω‖) := by
  apply GeneralizedBulk.Analysis.ae_weighted_summable _ _ _ 3
  · intro n
    exact MemLp.integrable (by norm_num) (Lp.memLp _)
  · intro n
    exact nevanlinnaWeight_nonneg _
  · exact s.summable_particle_weight
  · intro n
    exact markQuadraticLp_integral_norm_le_three _ parameters.abs_p_lt_one n i j

/-- A single samplewise analytic marked field, built from actual Gaussian
endpoint marks. Both slots are actual values/derivatives on one common event. -/
def gaussianAnalyticField (parameters : Parameters) (s : AnchoredCountingState) :
    (ℂ × Bool) → (s.val.1.ParticleLabels → (Fin 4 → ℝ)) → EndpointMatrix :=
  analyticMatrixSeries (iidLaw (markLaw parameters.p) s.val.1.ParticleLabels) s
    (fun n i j => markQuadraticLp parameters.p n i j) (parameters.scale : ℂ)

/-- Wick covariance is proved for the common analytic version itself. -/
theorem gaussianAnalyticField_entryWick (parameters : Parameters) (s : AnchoredCountingState) :
    EntryWickCovariance (iidLaw (markLaw parameters.p) s.val.1.ParticleLabels)
      (parameters.p : ℂ) (parameters.scale : ℂ) (particleKernel s)
      (gaussianAnalyticField parameters s) := by
  apply entryWickCovariance_analyticMatrixSeries _ s
    (fun n i j => markQuadraticLp parameters.p n i j)
    (parameters.p : ℂ) (parameters.scale : ℂ) 2 (by norm_num)
  · intro n i j
    exact markQuadraticLp_norm_sq_le_two _ parameters.abs_p_lt_one n i j
  · intro i j n m hnm
    exact markQuadraticLp_inner_off _ parameters.abs_p_lt_one hnm i j
  · intro n i j
    exact markQuadraticLp_mean_zero _ parameters.abs_p_lt_one n i j
  · intro n m hnm i j a b
    exact markQuadraticLp_off_covariance _ parameters.abs_p_lt_one hnm i j a b
  · intro n i j a b
    exact markQuadraticLp_diagonal_covariance _ parameters.abs_p_lt_one n i j a b
  · exact markQuadraticLp_weighted_summable parameters s

/-- The derivative-slot interpretation is proved simultaneously for every
matrix entry and every nonreal parameter on one full-measure event. -/
theorem gaussianAnalyticField_hasDerivAt_ae (parameters : Parameters) (s : AnchoredCountingState) :
    ∀ᵐ ω ∂iidLaw (markLaw parameters.p) s.val.1.ParticleLabels,
      ∀ i j : Fin 4, ∀ w : ℂ, w.im ≠ 0 →
        HasDerivAt (fun z => gaussianAnalyticField parameters s (z, false) ω i j)
          (gaussianAnalyticField parameters s (w, true) ω i j) w := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  simpa only [gaussianAnalyticField, analyticMatrixSeries, Bool.false_eq_true,
    ↓reduceIte] using
    analyticL2Entry_hasDerivAt_ae (iidLaw (markLaw parameters.p) s.val.1.ParticleLabels) s
      (fun n => markQuadraticLp parameters.p n i j) (parameters.scale : ℂ)
      (markQuadraticLp_weighted_summable parameters s i j)

/-- The common analytic field has the same explicit second-moment bound as
its constructed L² representative. -/
theorem gaussianAnalyticField_second_moment (parameters : Parameters) (s : AnchoredCountingState)
    (v : ℂ × Bool) (i j : Fin 4) :
    (∫ ω, ‖gaussianAnalyticField parameters s v ω i j‖ ^ 2
      ∂iidLaw (markLaw parameters.p) s.val.1.ParticleLabels) ≤
      2 * ∑' n : s.val.1.ParticleLabels,
        ‖(parameters.scale : ℂ) * particleCoefficient (s.val.1.particleLocation n) v‖ ^ 2 := by
  let μ := iidLaw (markLaw parameters.p) s.val.1.ParticleLabels
  let marks := fun n : s.val.1.ParticleLabels => markQuadraticLp parameters.p n i j
  have ho : Pairwise fun n m => @inner ℂ (Lp ℂ 2 μ) _ (marks n) (marks m) = 0 := by
    intro n m hnm
    exact markQuadraticLp_inner_off _ parameters.abs_p_lt_one hnm i j
  have hb (n : s.val.1.ParticleLabels) : ‖marks n‖ ^ 2 ≤ 2 :=
    markQuadraticLp_norm_sq_le_two _ parameters.abs_p_lt_one n i j
  have hae := analytic_slot_eq_L2_ae μ s marks (parameters.scale : ℂ) 2 ho (by norm_num) hb
    (markQuadraticLp_weighted_summable parameters s i j) v
  change (∫ ω, ‖(if v.2 then analyticDerivativeEntry μ s marks (parameters.scale : ℂ) v.1 ω
    else analyticL2Entry μ s marks (parameters.scale : ℂ) v.1 ω)‖ ^ 2 ∂μ) ≤ _
  rw [integral_congr_ae (hae.mono (fun ω hω => congrArg (fun z : ℂ => ‖z‖ ^ 2) hω))]
  apply integral_norm_sq_l2Series_le μ marks _ 2 ho (by norm_num) hb
  simpa only [norm_mul, mul_pow] using (summable_particleCoefficient_sq s v).mul_left (‖(parameters.scale : ℂ)‖ ^ 2)

end GeneralizedBulk.Gaussian
