import GeneralizedBulk.Gaussian.Presentation
import GeneralizedBulk.Gaussian.FieldVersion
import GeneralizedBulk.Gaussian.VersionCovariance

/-!
# Common analytic fields on a fixed particle-label space

The correction uses the actual raw mark functions, not a state-dependent
choice of L² representatives. A measurable global anchor can therefore be
inserted without choosing a measurable equivalence to `ParticleLabels`.
-/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped BigOperators Topology

namespace GeneralizedBulk.Gaussian.Presented

variable {I : Type*} [Countable I] {s : AnchoredCountingState}

def anchoredEntry (p : ParticlePresentation s I) (anchor sigma : ℂ)
    (mark : I → ℂ) (w : ℂ) : ℂ :=
  if w.im = 0 then 0 else anchor + ∑' i, sigma * anchorCorrection (p.location i) w * mark i

omit [Countable I] in
theorem summable_correction (p : ParticlePresentation s I) (sigma : ℂ) (mark : I → ℂ)
    (hweight : Summable (fun i => nevanlinnaWeight (p.location i) * ‖mark i‖))
    {w : ℂ} (hw : w.im ≠ 0) :
    Summable (fun i => sigma * anchorCorrection (p.location i) w * mark i) := by
  let C := ‖sigma‖ * correctionEnvelope |w.im| ‖w‖
  apply Summable.of_norm_bounded _ (hweight.mul_left C)
  intro i
  simp only [norm_mul]
  have hb := anchorCorrection_bound (p.location i) (abs_pos.mpr hw) (le_refl _) (le_refl _)
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
    (norm_nonneg _)).trans_eq (by dsimp [C]; ring)

omit [Countable I] in
theorem summable_derivative (p : ParticlePresentation s I) (sigma : ℂ) (mark : I → ℂ)
    (hweight : Summable (fun i => nevanlinnaWeight (p.location i) * ‖mark i‖))
    {w : ℂ} (hw : w.im ≠ 0) :
    Summable (fun i => sigma * particleCoefficient (p.location i) (w, true) * mark i) := by
  let C := ‖sigma‖ * derivativeEnvelope w
  apply Summable.of_norm_bounded _ (hweight.mul_left C)
  intro i
  simp only [norm_mul]
  have hR : 0 < |w.im| / 2 := by positivity
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (particleCoefficient_derivative_ball_bound (p.location i) hw (Metric.mem_ball_self hR))
    (norm_nonneg _)) (norm_nonneg _)).trans_eq (by dsimp [C]; ring)

omit [Countable I] in
/-- The fixed-index sample field has an actual complex derivative everywhere
on the same weighted-summability event. -/
theorem hasDerivAt_anchoredEntry (p : ParticlePresentation s I) (anchor sigma : ℂ)
    (mark : I → ℂ)
    (hweight : Summable (fun i => nevanlinnaWeight (p.location i) * ‖mark i‖))
    {w : ℂ} (hw : w.im ≠ 0) :
    HasDerivAt (anchoredEntry p anchor sigma mark)
      (∑' i, sigma * particleCoefficient (p.location i) (w, true) * mark i) w := by
  let u : I → ℝ := fun i => (‖sigma‖ * derivativeEnvelope w) *
    (nevanlinnaWeight (p.location i) * ‖mark i‖)
  have hu : Summable u := hweight.mul_left _
  have hR : 0 < |w.im| / 2 := by positivity
  have hd (i : I) (z : ℂ) (hz : z ∈ Metric.ball w (|w.im| / 2)) :
      HasDerivAt (fun y => sigma * anchorCorrection (p.location i) y * mark i)
        (sigma * particleCoefficient (p.location i) (z, true) * mark i) z :=
    ((hasDerivAt_anchorCorrection _ (half_imaginary_ball_bound w z hw hz).2).const_mul sigma).mul_const _
  have hb (i : I) (z : ℂ) (hz : z ∈ Metric.ball w (|w.im| / 2)) :
      ‖sigma * particleCoefficient (p.location i) (z, true) * mark i‖ ≤ u i := by
    simp only [norm_mul]
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (particleCoefficient_derivative_ball_bound _ hw hz)
        (norm_nonneg _)) (norm_nonneg _)).trans_eq (by dsimp [u]; ring)
  have h := hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    (convex_ball w _).isPreconnected hd hb (Metric.mem_ball_self hR)
    (summable_correction p sigma mark hweight hw) (Metric.mem_ball_self hR)
  apply (h.const_add anchor).congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds w hR] with z hz
  simp [anchoredEntry, (half_imaginary_ball_bound w z hw hz).2]

omit [Countable I] in
@[simp] theorem anchoredEntry_at_I (p : ParticlePresentation s I) (anchor sigma : ℂ)
    (mark : I → ℂ) : anchoredEntry p anchor sigma mark Complex.I = anchor := by
  simp [anchoredEntry, anchorCorrection]

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

def value (p : ParticlePresentation s I) (anchor : Ω → ℂ) (sigma : ℂ)
    (raw : I → Ω → ℂ) (w : ℂ) (ω : Ω) : ℂ :=
  anchoredEntry p (anchor ω) sigma (fun i => raw i ω) w

def derivative (p : ParticlePresentation s I) (sigma : ℂ)
    (raw : I → Ω → ℂ) (w : ℂ) (ω : Ω) : ℂ :=
  if w.im = 0 then 0 else ∑' i, sigma * particleCoefficient (p.location i) (w, true) * raw i ω

theorem summable_L2 (p : ParticlePresentation s I) (marks : I → Lp ℂ 2 μ)
    (sigma : ℂ) (B : ℝ)
    (horth : Pairwise fun i j => @inner ℂ (Lp ℂ 2 μ) _ (marks i) (marks j) = 0)
    (hB : 0 ≤ B) (hbound : ∀ i, ‖marks i‖ ^ 2 ≤ B) (v : ℂ × Bool) :
    Summable (fun i => (sigma * particleCoefficient (p.location i) v) • marks i) := by
  apply summable_weighted_orthogonal _ _ B horth hB hbound
  simpa only [norm_mul, mul_pow] using (p.summable_coefficient_sq v).mul_left (‖sigma‖ ^ 2)

/-- Any actual anchor agreeing with the conditional L² anchor gives the same
resolvent field, independently of which global measurable version supplied it. -/
theorem value_eq_L2_ae [IsFiniteMeasure μ]
    (p : ParticlePresentation s I) (anchor : Ω → ℂ) (sigma : ℂ)
    (raw : I → Ω → ℂ) (marks : I → Lp ℂ 2 μ) (B : ℝ)
    (hraw : ∀ i, (marks i : Ω → ℂ) =ᵐ[μ] raw i)
    (horth : Pairwise fun i j => @inner ℂ (Lp ℂ 2 μ) _ (marks i) (marks j) = 0)
    (hB : 0 ≤ B) (hbound : ∀ i, ‖marks i‖ ^ 2 ≤ B)
    (hweight : ∀ᵐ ω ∂μ, Summable (fun i => nevanlinnaWeight (p.location i) * ‖raw i ω‖))
    (hanchor : anchor =ᵐ[μ] (fun ω => l2Series μ marks
      (fun i => sigma * particleCoefficient (p.location i) (Complex.I, false)) ω))
    {w : ℂ} (hw : w.im ≠ 0) :
    value p anchor sigma raw w =ᵐ[μ]
      (fun ω => l2Series μ marks (fun i => sigma * particleCoefficient (p.location i) (w, false)) ω) := by
  classical
  let f := fun i => (sigma * particleCoefficient (p.location i) (w, false)) • marks i
  let a := fun i => (sigma * particleCoefficient (p.location i) (Complex.I, false)) • marks i
  let d := fun i => (sigma * anchorCorrection (p.location i) w) • marks i
  have hf : Summable f := summable_L2 μ p marks sigma B horth hB hbound _
  have ha : Summable a := summable_L2 μ p marks sigma B horth hB hbound _
  have hdiff (i : I) : d i = f i - a i := by
    simp only [d, f, a, anchorCorrection, hw, ↓reduceIte, mul_sub, sub_smul]
  have hd : Summable d := (hf.sub ha).congr (fun i => (hdiff i).symm)
  have hdSum : (∑' i, d i) = (∑' i, f i) - ∑' i, a i := by
    simp_rw [hdiff]
    exact hf.tsum_sub ha
  have hsmul : ∀ᵐ ω ∂μ, ∀ i : I, d i ω = sigma * anchorCorrection (p.location i) w * raw i ω :=
    ae_all_iff.mpr (fun i => by
      filter_upwards [Lp.coeFn_smul (sigma * anchorCorrection (p.location i) w) (marks i), hraw i]
        with ω hs hr
      simp only [Pi.smul_apply, smul_eq_mul, hr] at hs
      exact hs)
  have hp : ∀ᵐ ω ∂μ, HasSum (fun i => d i ω)
      (∑' i, sigma * anchorCorrection (p.location i) w * raw i ω) := by
    filter_upwards [hweight, hsmul] with ω hω hm
    simpa only [hm] using (summable_correction p sigma (fun i => raw i ω) hω hw).hasSum
  have hv := GeneralizedBulk.Analysis.lp_tsum_eq_ae_of_hasSum μ d _ hd hp
  have hadd : (∑' i, f i) = (∑' i, a i) + ∑' i, d i := by rw [hdSum]; abel
  filter_upwards [hv, Lp.coeFn_add (∑' i, a i) (∑' i, d i), hanchor] with ω hω haω han
  change anchoredEntry p (anchor ω) sigma (fun i => raw i ω) w = (∑' i, f i) ω
  rw [hadd, haω]
  simp only [Pi.add_apply] at *
  simp only [anchoredEntry, hw, ↓reduceIte]
  rw [han, hω]
  rfl

/-- The raw derivative series equals the conditional derivative L² series. -/
theorem derivative_eq_L2_ae [IsFiniteMeasure μ]
    (p : ParticlePresentation s I) (sigma : ℂ)
    (raw : I → Ω → ℂ) (marks : I → Lp ℂ 2 μ) (B : ℝ)
    (hraw : ∀ i, (marks i : Ω → ℂ) =ᵐ[μ] raw i)
    (horth : Pairwise fun i j => @inner ℂ (Lp ℂ 2 μ) _ (marks i) (marks j) = 0)
    (hB : 0 ≤ B) (hbound : ∀ i, ‖marks i‖ ^ 2 ≤ B)
    (hweight : ∀ᵐ ω ∂μ, Summable (fun i => nevanlinnaWeight (p.location i) * ‖raw i ω‖))
    {w : ℂ} (hw : w.im ≠ 0) :
    derivative p sigma raw w =ᵐ[μ]
      (fun ω => l2Series μ marks (fun i => sigma * particleCoefficient (p.location i) (w, true)) ω) := by
  let f := fun i => (sigma * particleCoefficient (p.location i) (w, true)) • marks i
  have hf : Summable f := summable_L2 μ p marks sigma B horth hB hbound _
  have hsmul : ∀ᵐ ω ∂μ, ∀ i : I,
      f i ω = sigma * particleCoefficient (p.location i) (w, true) * raw i ω :=
    ae_all_iff.mpr (fun i => by
      filter_upwards [Lp.coeFn_smul (sigma * particleCoefficient (p.location i) (w, true)) (marks i), hraw i]
        with ω hs hr
      simp only [Pi.smul_apply, smul_eq_mul, hr] at hs
      exact hs)
  have hp : ∀ᵐ ω ∂μ, HasSum (fun i => f i ω) (derivative p sigma raw w ω) := by
    filter_upwards [hweight, hsmul] with ω hω hm
    simpa only [hm, derivative, hw, ↓reduceIte] using
      (summable_derivative p sigma (fun i => raw i ω) hω hw).hasSum
  exact (GeneralizedBulk.Analysis.lp_tsum_eq_ae_of_hasSum μ f _ hf hp).symm

omit [Countable I] in
/-- All nonreal sample derivatives hold simultaneously for the fixed-index
field, using only the common weighted-summability event. -/
theorem value_hasDerivAt_ae (p : ParticlePresentation s I) (anchor : Ω → ℂ) (sigma : ℂ)
    (raw : I → Ω → ℂ)
    (hweight : ∀ᵐ ω ∂μ, Summable (fun i => nevanlinnaWeight (p.location i) * ‖raw i ω‖)) :
    ∀ᵐ ω ∂μ, ∀ w : ℂ, w.im ≠ 0 →
      HasDerivAt (fun z => value p anchor sigma raw z ω) (derivative p sigma raw w ω) w := by
  filter_upwards [hweight] with ω hω
  intro w hw
  simpa only [value, derivative, hw, ↓reduceIte] using
    hasDerivAt_anchoredEntry p (anchor ω) sigma (fun i => raw i ω) hω hw

/-- Full centered endpoint matrix with a fixed particle-label type and a
single externally constructed measurable anchor matrix. -/
def matrixField (p : ParticlePresentation s I) (anchor : Ω → EndpointMatrix) (sigma : ℂ)
    (raw : I → Ω → EndpointMatrix) (v : ℂ × Bool) (ω : Ω) : EndpointMatrix :=
  fun i j => if v.2 then derivative p sigma (fun n ω => raw n ω i j) v.1 ω
    else value p (fun ω => anchor ω i j) sigma (fun n ω => raw n ω i j) v.1 ω

theorem slot_eq_L2_ae [IsFiniteMeasure μ]
    (p : ParticlePresentation s I) (anchor : Ω → ℂ) (sigma : ℂ)
    (raw : I → Ω → ℂ) (marks : I → Lp ℂ 2 μ) (B : ℝ)
    (hraw : ∀ i, (marks i : Ω → ℂ) =ᵐ[μ] raw i)
    (horth : Pairwise fun i j => @inner ℂ (Lp ℂ 2 μ) _ (marks i) (marks j) = 0)
    (hB : 0 ≤ B) (hbound : ∀ i, ‖marks i‖ ^ 2 ≤ B)
    (hweight : ∀ᵐ ω ∂μ, Summable (fun i => nevanlinnaWeight (p.location i) * ‖raw i ω‖))
    (hanchor : anchor =ᵐ[μ] (fun ω => l2Series μ marks
      (fun i => sigma * particleCoefficient (p.location i) (Complex.I, false)) ω))
    (v : ℂ × Bool) :
    (fun ω => if v.2 then derivative p sigma raw v.1 ω
      else value p anchor sigma raw v.1 ω) =ᵐ[μ]
      (fun ω => l2Series μ marks (fun i => sigma * particleCoefficient (p.location i) v) ω) := by
  rcases v with ⟨w, tag⟩
  by_cases hw : w.im = 0
  · have hz : l2Series μ marks (fun i => sigma * particleCoefficient (p.location i) (w, tag)) = 0 := by
      simp [l2Series, particleCoefficient, hw]
    cases tag <;>
      simpa only [Bool.false_eq_true, ↓reduceIte, value, derivative, anchoredEntry,
        hw, if_pos, hz] using (Lp.coeFn_zero ℂ 2 μ).symm
  · cases tag
    · exact value_eq_L2_ae μ p anchor sigma raw marks B hraw horth hB hbound hweight hanchor hw
    · exact derivative_eq_L2_ae μ p sigma raw marks B hraw horth hB hbound hweight hw

/-- The actual conditional L² Wick calculation transfers to the fixed-label
samplewise analytic field, once its measurable anchor has been identified. -/
theorem matrixField_entryWick_of_L2 [IsFiniteMeasure μ]
    (p : ParticlePresentation s I) (anchor : Ω → EndpointMatrix) (sigma covariance : ℂ)
    (raw : I → Ω → EndpointMatrix)
    (marks : I → Matrix (Fin 4) (Fin 4) (Lp ℂ 2 μ)) (B : ℝ)
    (hraw : ∀ n i j, (marks n i j : Ω → ℂ) =ᵐ[μ] (fun ω => raw n ω i j))
    (horth : ∀ i j, Pairwise fun n m => @inner ℂ (Lp ℂ 2 μ) _ (marks n i j) (marks m i j) = 0)
    (hB : 0 ≤ B) (hbound : ∀ n i j, ‖marks n i j‖ ^ 2 ≤ B)
    (hweight : ∀ i j, ∀ᵐ ω ∂μ, Summable (fun n => nevanlinnaWeight (p.location n) * ‖raw n ω i j‖))
    (hanchor : ∀ i j, (fun ω => anchor ω i j) =ᵐ[μ] (fun ω => l2Series μ
      (fun n => marks n i j) (fun n => sigma * particleCoefficient (p.location n) (Complex.I, false)) ω))
    (hL2 : EntryWickCovariance μ covariance sigma (particleKernel s)
      (matrixL2Series μ marks (fun v n => sigma * particleCoefficient (p.location n) v))) :
    EntryWickCovariance μ covariance sigma (particleKernel s) (matrixField p anchor sigma raw) := by
  apply hL2.congr_ae
  intro v i j
  exact (slot_eq_L2_ae μ p (fun ω => anchor ω i j) sigma (fun n ω => raw n ω i j)
    (fun n => marks n i j) B (fun n => hraw n i j) (horth i j) hB
      (fun n => hbound n i j) (hweight i j) (hanchor i j) v).symm

omit [Countable I] in
/-- All entries and nonreal spectral parameters have actual derivatives on
one common full-measure event for a presented particle configuration. -/
theorem matrixField_hasDerivAt_ae (p : ParticlePresentation s I)
    (anchor : Ω → EndpointMatrix) (sigma : ℂ) (raw : I → Ω → EndpointMatrix)
    (hweight : ∀ i j, ∀ᵐ ω ∂μ, Summable (fun n => nevanlinnaWeight (p.location n) * ‖raw n ω i j‖)) :
    ∀ᵐ ω ∂μ, ∀ i j : Fin 4, ∀ w : ℂ, w.im ≠ 0 →
      HasDerivAt (fun z => matrixField p anchor sigma raw (z, false) ω i j)
        (matrixField p anchor sigma raw (w, true) ω i j) w := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  simpa only [matrixField, Bool.false_eq_true, ↓reduceIte] using
    value_hasDerivAt_ae μ p (fun ω => anchor ω i j) sigma (fun n ω => raw n ω i j) (hweight i j)

end GeneralizedBulk.Gaussian.Presented
