import GeneralizedBulk.Gaussian.Series
import GeneralizedBulk.Gaussian.AnalyticVersion
import GeneralizedBulk.Analysis.LpSeriesVersion

/-! The common analytic sample version agrees with the constructed L² field. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped Topology BigOperators

namespace GeneralizedBulk.Gaussian

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

def analyticL2Entry (s : AnchoredCountingState)
    (marks : s.val.1.ParticleLabels → Lp ℂ 2 μ) (sigma w : ℂ) (ω : Ω) : ℂ :=
  anchoredMarkedEntry s
    (l2Series μ marks (fun i => sigma * particleCoefficient
      (s.val.1.particleLocation i) (Complex.I, false)) ω)
    sigma (fun i => marks i ω) w

def analyticDerivativeEntry (s : AnchoredCountingState)
    (marks : s.val.1.ParticleLabels → Lp ℂ 2 μ) (sigma w : ℂ) (ω : Ω) : ℂ :=
  if w.im = 0 then 0 else ∑' i,
    sigma * particleCoefficient (s.val.1.particleLocation i) (w, true) * marks i ω

theorem summable_scaled_particle_marks (s : AnchoredCountingState)
    (marks : s.val.1.ParticleLabels → Lp ℂ 2 μ) (sigma : ℂ) (B : ℝ)
    (horth : Pairwise fun i j => @inner ℂ (Lp ℂ 2 μ) _ (marks i) (marks j) = 0)
    (hB : 0 ≤ B) (hbound : ∀ i, ‖marks i‖ ^ 2 ≤ B) (v : ℂ × Bool) :
    Summable (fun i => (sigma * particleCoefficient (s.val.1.particleLocation i) v) • marks i) := by
  apply summable_weighted_orthogonal _ _ B horth hB hbound
  simpa only [norm_mul, mul_pow] using (summable_particleCoefficient_sq s v).mul_left (‖sigma‖ ^ 2)

/-- The analytic field is not an unrelated version: it equals the actual L²
series almost everywhere at every nonreal spectral parameter. -/
theorem analyticL2Entry_eq_ae [IsFiniteMeasure μ]
    (s : AnchoredCountingState) (marks : s.val.1.ParticleLabels → Lp ℂ 2 μ)
    (sigma : ℂ) (B : ℝ)
    (horth : Pairwise fun i j => @inner ℂ (Lp ℂ 2 μ) _ (marks i) (marks j) = 0)
    (hB : 0 ≤ B) (hbound : ∀ i, ‖marks i‖ ^ 2 ≤ B)
    (hweight : ∀ᵐ ω ∂μ, Summable (fun i =>
      nevanlinnaWeight (s.val.1.particleLocation i) * ‖marks i ω‖))
    {w : ℂ} (hw : w.im ≠ 0) :
    analyticL2Entry μ s marks sigma w =ᵐ[μ]
      (fun ω => l2Series μ marks (fun i => sigma * particleCoefficient
        (s.val.1.particleLocation i) (w, false)) ω) := by
  classical
  let f := fun i => (sigma * particleCoefficient (s.val.1.particleLocation i) (w, false)) • marks i
  let a := fun i => (sigma * particleCoefficient (s.val.1.particleLocation i) (Complex.I, false)) • marks i
  let d := fun i => (sigma * anchorCorrection (s.val.1.particleLocation i) w) • marks i
  have hf : Summable f := summable_scaled_particle_marks μ s marks sigma B horth hB hbound _
  have ha : Summable a := summable_scaled_particle_marks μ s marks sigma B horth hB hbound _
  have hdiff (i : s.val.1.ParticleLabels) : d i = f i - a i := by
    simp only [d, f, a, anchorCorrection, hw, ↓reduceIte, mul_sub, sub_smul]
  have hd : Summable d := (hf.sub ha).congr (fun i => (hdiff i).symm)
  have hdSum : (∑' i, d i) = (∑' i, f i) - ∑' i, a i := by
    simp_rw [hdiff]
    exact hf.tsum_sub ha
  have hsmul : ∀ᵐ ω ∂μ, ∀ i : s.val.1.ParticleLabels,
      d i ω = sigma * anchorCorrection (s.val.1.particleLocation i) w * marks i ω :=
    ae_all_iff.mpr (fun i => Lp.coeFn_smul _ _)
  have hp : ∀ᵐ ω ∂μ, HasSum (fun i => d i ω)
      (∑' i, sigma * anchorCorrection (s.val.1.particleLocation i) w * marks i ω) := by
    filter_upwards [hweight, hsmul] with ω hω hm
    simpa only [hm] using (summable_anchorCorrection s sigma (fun i => marks i ω) hω hw).hasSum
  have hv := GeneralizedBulk.Analysis.lp_tsum_eq_ae_of_hasSum μ d _ hd hp
  have hadd : (∑' i, f i) = (∑' i, a i) + ∑' i, d i := by rw [hdSum]; abel
  filter_upwards [hv, Lp.coeFn_add (∑' i, a i) (∑' i, d i)] with ω hω haω
  change anchoredMarkedEntry s ((∑' i, a i) ω) sigma (fun i => marks i ω) w = (∑' i, f i) ω
  rw [hadd, haω]
  simp only [Pi.add_apply] at *
  simp only [anchoredMarkedEntry, hw, ↓reduceIte]
  rw [hω]

theorem summable_derivative_entry (s : AnchoredCountingState)
    (sigma : ℂ) (mark : s.val.1.ParticleLabels → ℂ)
    (hweight : Summable (fun i => nevanlinnaWeight (s.val.1.particleLocation i) * ‖mark i‖))
    {w : ℂ} (hw : w.im ≠ 0) :
    Summable (fun i => sigma * particleCoefficient (s.val.1.particleLocation i) (w, true) * mark i) := by
  let C := ‖sigma‖ * derivativeEnvelope w
  apply Summable.of_norm_bounded _ (hweight.mul_left C)
  intro i
  simp only [norm_mul]
  have hR : 0 < |w.im| / 2 := by positivity
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (particleCoefficient_derivative_ball_bound (s.val.1.particleLocation i) hw (Metric.mem_ball_self hR))
    (norm_nonneg _)) (norm_nonneg _)).trans_eq (by dsimp [C]; ring)

theorem analyticDerivativeEntry_eq_ae [IsFiniteMeasure μ]
    (s : AnchoredCountingState) (marks : s.val.1.ParticleLabels → Lp ℂ 2 μ)
    (sigma : ℂ) (B : ℝ)
    (horth : Pairwise fun i j => @inner ℂ (Lp ℂ 2 μ) _ (marks i) (marks j) = 0)
    (hB : 0 ≤ B) (hbound : ∀ i, ‖marks i‖ ^ 2 ≤ B)
    (hweight : ∀ᵐ ω ∂μ, Summable (fun i =>
      nevanlinnaWeight (s.val.1.particleLocation i) * ‖marks i ω‖))
    {w : ℂ} (hw : w.im ≠ 0) :
    analyticDerivativeEntry μ s marks sigma w =ᵐ[μ]
      (fun ω => l2Series μ marks (fun i => sigma * particleCoefficient
        (s.val.1.particleLocation i) (w, true)) ω) := by
  let f := fun i => (sigma * particleCoefficient (s.val.1.particleLocation i) (w, true)) • marks i
  have hf : Summable f := summable_scaled_particle_marks μ s marks sigma B horth hB hbound _
  have hsmul : ∀ᵐ ω ∂μ, ∀ i : s.val.1.ParticleLabels,
      f i ω = sigma * particleCoefficient (s.val.1.particleLocation i) (w, true) * marks i ω :=
    ae_all_iff.mpr (fun i => Lp.coeFn_smul _ _)
  have hp : ∀ᵐ ω ∂μ, HasSum (fun i => f i ω)
      (analyticDerivativeEntry μ s marks sigma w ω) := by
    filter_upwards [hweight, hsmul] with ω hω hm
    simpa only [hm, analyticDerivativeEntry, hw, ↓reduceIte] using
      (summable_derivative_entry s sigma (fun i => marks i ω) hω hw).hasSum
  exact (GeneralizedBulk.Analysis.lp_tsum_eq_ae_of_hasSum μ f _ hf hp).symm

/-- The true-slot field is the actual sample derivative, on one common event. -/
theorem analyticL2Entry_hasDerivAt_ae [IsFiniteMeasure μ]
    (s : AnchoredCountingState) (marks : s.val.1.ParticleLabels → Lp ℂ 2 μ)
    (sigma : ℂ)
    (hweight : ∀ᵐ ω ∂μ, Summable (fun i =>
      nevanlinnaWeight (s.val.1.particleLocation i) * ‖marks i ω‖)) :
    ∀ᵐ ω ∂μ, ∀ w : ℂ, w.im ≠ 0 →
      HasDerivAt (fun z => analyticL2Entry μ s marks sigma z ω)
        (analyticDerivativeEntry μ s marks sigma w ω) w := by
  filter_upwards [hweight] with ω hω
  intro w hw
  simpa only [analyticL2Entry, analyticDerivativeEntry, hw, ↓reduceIte] using
    hasDerivAt_anchoredMarkedEntry s _ sigma (fun i => marks i ω) hω hw

/-- The L² field admits a version analytic at all nonreal points on one
common full-measure set. -/
theorem analyticL2Entry_differentiable_ae [IsFiniteMeasure μ]
    (s : AnchoredCountingState) (marks : s.val.1.ParticleLabels → Lp ℂ 2 μ)
    (sigma : ℂ) (B : ℝ)
    (hbound : ∀ i, (∫ ω, ‖marks i ω‖ ∂μ) ≤ B) :
    ∀ᵐ ω ∂μ, ∀ w : ℂ, w.im ≠ 0 →
      DifferentiableAt ℂ (fun z => analyticL2Entry μ s marks sigma z ω) w := by
  exact ae_differentiable_anchoredMarkedEntry μ s _ sigma _ B
    (fun i => (Lp.memLp (marks i)).integrable (by norm_num)) hbound

end GeneralizedBulk.Gaussian
