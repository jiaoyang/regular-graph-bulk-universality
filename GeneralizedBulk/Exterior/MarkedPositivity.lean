import GeneralizedBulk.Exterior.IndependentMarks
import GeneralizedBulk.Gaussian.PresentedAnalytic
import GeneralizedBulk.Gaussian.SeriesActual

/-!
# Imaginary parts of the actual anchored Gaussian marked field

The imaginary part at the L² anchor is identified with its absolutely
convergent imaginary series. The analytic correction then gives the positive
uncentered marked series simultaneously at all upper-half-plane parameters.
-/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped Topology BigOperators ComplexOrder
namespace GeneralizedBulk.Exterior
open Gaussian

/-- Imaginary part embedded back into the complex plane, as a real CLM. -/
def imaginaryEmbedding : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.imCLM

@[simp] theorem imaginaryEmbedding_apply (z : ℂ) : imaginaryEmbedding z = (z.im : ℂ) := rfl

/-- Taking imaginary parts of a genuine L² sum agrees with the absolutely
convergent sample imaginary series. This does not assume convergence of the
original complex series at individual samples. -/
theorem imaginary_anchor_eq_tsum
    {I Ω : Type*} [Countable I] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (terms : I → Lp ℂ 2 μ) (raw : I → Ω → ℂ) (anchor : Ω → ℂ)
    (hterms : ∀ i, (terms i : Ω → ℂ) =ᵐ[μ] raw i)
    (hs : Summable terms)
    (ha : anchor =ᵐ[μ] (fun ω => (∑' i, terms i) ω))
    (him : ∀ᵐ ω ∂μ, Summable (fun i => (raw i ω).im)) :
    (fun ω => (anchor ω).im) =ᵐ[μ] (fun ω => ∑' i, (raw i ω).im) := by
  let T : Lp ℂ 2 μ →L[ℝ] Lp ℂ 2 μ := imaginaryEmbedding.compLpL 2 μ
  let g : I → Lp ℂ 2 μ := fun i => T (terms i)
  have hg : Summable g := T.summable hs
  have hcoe : ∀ᵐ ω ∂μ, ∀ i : I, g i ω = ((raw i ω).im : ℂ) := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [imaginaryEmbedding.coeFn_compLpL (terms i), hterms i] with ω hc hr
    change g i ω = _ at hc
    simpa only [imaginaryEmbedding_apply, hr] using hc
  have hpoint : ∀ᵐ ω ∂μ, HasSum (fun i => g i ω) ((∑' i, (raw i ω).im : ℝ) : ℂ) := by
    filter_upwards [him, hcoe] with ω hi hc
    simpa only [hc] using Complex.ofRealCLM.hasSum hi.hasSum
  have hv := GeneralizedBulk.Analysis.lp_tsum_eq_ae_of_hasSum μ g _ hg hpoint
  have hsum : (∑' i, g i) = T (∑' i, terms i) := (T.map_tsum hs).symm
  filter_upwards [hv, imaginaryEmbedding.coeFn_compLpL (∑' i, terms i), ha] with ω hv hc ha
  rw [hsum, hc, ← ha] at hv
  exact Complex.ofReal_injective (by simpa only [imaginaryEmbedding_apply] using hv)

/-- Real Poisson weight of a particle. -/
def poissonWeight (x : ℝ) (w : ℂ) : ℝ := w.im / Complex.normSq ((x : ℂ) - w)

theorem particleCoefficient_im (x : ℝ) {w : ℂ} (hw : w.im ≠ 0) :
    (particleCoefficient x (w, false)).im = poissonWeight x w := by
  simp [particleCoefficient, hw, poissonWeight, Complex.inv_im]

@[simp] theorem particleCoefficient_im_I (x : ℝ) :
    (particleCoefficient x (Complex.I, false)).im = nevanlinnaWeight x := by
  simp [particleCoefficient, Complex.inv_im, Complex.normSq_apply, nevanlinnaWeight, pow_two, add_comm]

theorem poissonWeight_pos (x : ℝ) {w : ℂ} (hw : 0 < w.im) : 0 < poissonWeight x w := by
  exact div_pos hw (Complex.normSq_pos.mpr (real_sub_ne_zero x (ne_of_gt hw)))

/-- Scalar weighted local finiteness gives exactly the sum of Poisson weights
when no linear Nevanlinna term is present. -/
theorem hasSum_poissonWeight
    {I : Type*} [Countable I] {s : AnchoredCountingState}
    (p : ParticlePresentation s I) (hlinear : anchoredLinearCoefficient s = 0)
    {w : ℂ} (hw : w.im ≠ 0) :
    HasSum (fun i => poissonWeight (p.location i) w) (anchoredNevanlinna s w).im := by
  have hi := (integrable_regularizedResolventKernel s hw).im
  have he := p.hasSum_observable hi
  have hscalar := anchoredNevanlinna_im_eq s hw
  rw [hlinear, mul_zero, zero_add] at hscalar
  change HasSum (fun i => (regularizedResolventKernel w (p.location i)).im)
    (∫ x, (regularizedResolventKernel w x).im ∂s.val.1.measure) at he
  simp_rw [regularizedResolventKernel_im] at he
  rw [← hscalar] at he
  exact he

/-- A matrix with symmetric entries has Hermitian imaginary part equal to
its entrywise imaginary part. -/
theorem imaginaryPart_of_symmetric (M : EndpointMatrix)
    (hM : M.transpose = M) : imaginaryPart M = fun i j => ((M i j).im : ℂ) := by
  ext i j
  have hsym : M j i = M i j := congrFun (congrFun hM i) j
  simp only [imaginaryPart, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.conjTranspose_apply, hsym, smul_eq_mul]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.div_re,
    Complex.div_im] <;> ring

/-- The scalar Poisson series times one fixed real coefficient. -/
theorem summable_poissonWeight_mul_const
    {I : Type*} [Countable I] {s : AnchoredCountingState}
    (p : ParticlePresentation s I) (hlinear : anchoredLinearCoefficient s = 0)
    {w : ℂ} (hw : w.im ≠ 0) (a : ℝ) :
    Summable (fun i => poissonWeight (p.location i) w * a) :=
  (hasSum_poissonWeight p hlinear hw).summable.mul_right a

/-- The imaginary correction is absolutely summable and precisely changes
the anchor Poisson weight to the weight at the new parameter. -/
theorem imaginary_anchoredEntry
    {I : Type*} [Countable I] {s : AnchoredCountingState}
    (p : ParticlePresentation s I) (anchor : ℂ) (sigma : ℝ) (q : I → ℝ)
    (hweight : Summable (fun i => nevanlinnaWeight (p.location i) * ‖(q i : ℂ)‖))
    (ha : anchor.im = ∑' i, sigma * nevanlinnaWeight (p.location i) * q i)
    {w : ℂ} (hw : w.im ≠ 0) :
    (Presented.anchoredEntry p anchor sigma (fun i => (q i : ℂ)) w).im =
      ∑' i, sigma * poissonWeight (p.location i) w * q i := by
  have hwq : Summable (fun i => nevanlinnaWeight (p.location i) * q i) := by
    apply Summable.of_norm_bounded _ hweight
    intro i
    simp [Real.norm_eq_abs, abs_mul, abs_of_nonneg (nevanlinnaWeight_nonneg _)]
  have haSum : Summable (fun i => sigma * nevanlinnaWeight (p.location i) * q i) := by
    simpa only [mul_assoc] using hwq.mul_left sigma
  have hc := Presented.summable_correction p (sigma : ℂ) (fun i => (q i : ℂ)) hweight hw
  have him : Summable (fun i => ((sigma : ℂ) * anchorCorrection (p.location i) w * (q i : ℂ)).im) :=
    (Complex.imCLM.hasSum hc.hasSum).summable
  have hi : Summable (fun i =>
      sigma * (poissonWeight (p.location i) w - nevanlinnaWeight (p.location i)) * q i) := by
    simpa only [anchorCorrection, hw, ↓reduceIte, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, zero_add, add_zero, Complex.sub_im,
      particleCoefficient_im _ hw, particleCoefficient_im_I] using him
  have hs : Summable (fun i => sigma * poissonWeight (p.location i) w * q i) := by
    convert haSum.add hi using 1
    funext i
    ring
  simp only [Presented.anchoredEntry, hw, ↓reduceIte, Complex.add_im, ha]
  have hci := Complex.imCLM.map_tsum hc
  change (∑' i, ((sigma : ℂ) * anchorCorrection (p.location i) w * (q i : ℂ))).im =
    ∑' i, ((sigma : ℂ) * anchorCorrection (p.location i) w * (q i : ℂ)).im at hci
  rw [hci]
  have hexpr : (fun i => ((sigma : ℂ) * anchorCorrection (p.location i) w * (q i : ℂ)).im) =
      (fun i => sigma * poissonWeight (p.location i) w * q i -
        sigma * nevanlinnaWeight (p.location i) * q i) := by
    funext i
    simp only [anchorCorrection, hw, ↓reduceIte, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, zero_add, add_zero, Complex.sub_im,
      particleCoefficient_im _ hw, particleCoefficient_im_I]
    ring
  rw [hexpr, hs.tsum_sub haSum]
  ring

/-- Weighted local finiteness also controls the uncentered Poisson series. -/
theorem summable_poissonWeight_mul_raw
    {I : Type*} [Countable I] {s : AnchoredCountingState}
    (p : ParticlePresentation s I) (sigma : ℝ) (q : I → ℝ)
    (hweight : Summable (fun i => nevanlinnaWeight (p.location i) * ‖(q i : ℂ)‖))
    {w : ℂ} (hw : w.im ≠ 0) :
    Summable (fun i => sigma * poissonWeight (p.location i) w * q i) := by
  have hwq : Summable (fun i => nevanlinnaWeight (p.location i) * q i) := by
    apply Summable.of_norm_bounded _ hweight
    intro i
    simp [Real.norm_eq_abs, abs_mul, abs_of_nonneg (nevanlinnaWeight_nonneg _)]
  have ha : Summable (fun i => sigma * nevanlinnaWeight (p.location i) * q i) := by
    simpa only [mul_assoc] using hwq.mul_left sigma
  have hc := Presented.summable_correction p (sigma : ℂ) (fun i => (q i : ℂ)) hweight hw
  have him : Summable (fun i => ((sigma : ℂ) * anchorCorrection (p.location i) w * (q i : ℂ)).im) :=
    (Complex.imCLM.hasSum hc.hasSum).summable
  have hi : Summable (fun i =>
      sigma * (poissonWeight (p.location i) w - nevanlinnaWeight (p.location i)) * q i) := by
    simpa only [anchorCorrection, hw, ↓reduceIte, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, zero_add, add_zero, Complex.sub_im,
      particleCoefficient_im _ hw, particleCoefficient_im_I] using him
  convert ha.add hi using 1
  funext i
  ring

@[simp] theorem covarianceMatrix_complex_entry (p : ℝ) (i j : Fin 4) :
    covarianceMatrix (p : ℂ) i j = ((covarianceMatrix p i j : ℝ) : ℂ) := by
  rw [covarianceMatrix_eq, covarianceMatrix_eq]
  fin_cases i <;> fin_cases j <;> simp

@[simp] theorem edgeMatrix_complex_entry (i j : Fin 4) :
    (GeneralizedSwitching.edgeMatrix : EndpointMatrix) i j =
      (((GeneralizedSwitching.edgeMatrix : Matrix (Fin 4) (Fin 4) ℝ) i j) : ℂ) := by
  fin_cases i <;> fin_cases j <;> rfl

/-- Actual conditional L² anchors have their absolutely convergent imaginary
parts, with every endpoint entry valid on a single event. -/
theorem anchor_imaginary_ae
    {I : Type*} [Countable I] {s : AnchoredCountingState}
    (p : ParticlePresentation s I) (rho : ℝ) (hrho : |rho| < 1) (sigma : ℝ)
    (anchor : (I → (Fin 4 → ℝ)) → EndpointMatrix)
    (hweight : ∀ᵐ ω ∂iidLaw (markLaw rho) I, ∀ i j : Fin 4,
      Summable (fun n => nevanlinnaWeight (p.location n) * ‖(rawQuadratic rho i j (ω n) : ℂ)‖))
    (ha : ∀ i j : Fin 4, (fun ω => anchor ω i j) =ᵐ[iidLaw (markLaw rho) I]
      (fun ω => l2Series (iidLaw (markLaw rho) I)
        (fun n => markQuadraticLp rho n i j)
        (fun n => (sigma : ℂ) * particleCoefficient (p.location n) (Complex.I, false)) ω)) :
    ∀ᵐ ω ∂iidLaw (markLaw rho) I, ∀ i j : Fin 4,
      (anchor ω i j).im = ∑' n, sigma * nevanlinnaWeight (p.location n) * rawQuadratic rho i j (ω n) := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  let μ := iidLaw (markLaw rho) I
  let terms : I → Lp ℂ 2 μ := fun n =>
    ((sigma : ℂ) * particleCoefficient (p.location n) (Complex.I, false)) • markQuadraticLp rho n i j
  let raw : I → (I → (Fin 4 → ℝ)) → ℂ := fun n ω =>
    (sigma : ℂ) * particleCoefficient (p.location n) (Complex.I, false) * (rawQuadratic rho i j (ω n) : ℂ)
  have hs : Summable terms := Presented.summable_L2 μ p _ (sigma : ℂ) 2
    (fun n m hnm => markQuadraticLp_inner_off rho hrho hnm i j) (by norm_num)
    (fun n => markQuadraticLp_norm_sq_le_two rho hrho n i j) _
  have ht (n : I) : (terms n : (I → (Fin 4 → ℝ)) → ℂ) =ᵐ[μ] raw n := by
    filter_upwards [Lp.coeFn_smul ((sigma : ℂ) * particleCoefficient (p.location n) (Complex.I, false))
      (markQuadraticLp rho n i j), markQuadraticLp_ae rho n i j] with ω he hq
    simpa only [Pi.smul_apply, smul_eq_mul, hq, markQuadraticFamily] using he
  have hi : ∀ᵐ ω ∂μ, Summable (fun n => (raw n ω).im) := by
    filter_upwards [hweight] with ω hω
    have hq : Summable (fun n => nevanlinnaWeight (p.location n) * rawQuadratic rho i j (ω n)) := by
      apply Summable.of_norm_bounded _ (hω i j)
      intro n
      simp [Real.norm_eq_abs, abs_mul, abs_of_nonneg (nevanlinnaWeight_nonneg _)]
    simpa only [raw, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, mul_zero, zero_add, add_zero, particleCoefficient_im_I, mul_assoc] using hq.mul_left sigma
  have hh := imaginary_anchor_eq_tsum μ terms raw (fun ω => anchor ω i j) ht hs (ha i j) hi
  simpa only [raw, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, zero_add, add_zero, particleCoefficient_im_I] using hh

/-- Symmetry of the covariance matrix and centered quadratic entries. -/
theorem rawQuadratic_symm (rho : ℝ) (i j : Fin 4) (y : Fin 4 → ℝ) :
    rawQuadratic rho i j y = rawQuadratic rho j i y := by
  have hc : covarianceMatrix rho i j = covarianceMatrix rho j i := by
    rw [covarianceMatrix_eq]
    fin_cases i <;> fin_cases j <;> simp
  simp only [rawQuadratic, hc, mul_comm]

theorem markQuadraticLp_symm (rho : ℝ) {I : Type*} (n : I) (i j : Fin 4) :
    markQuadraticLp rho n i j = markQuadraticLp rho n j i := by
  apply Lp.ext
  filter_upwards [markQuadraticLp_ae rho n i j, markQuadraticLp_ae rho n j i] with ω hi hj
  rw [hi, hj]
  exact congrArg Complex.ofReal (rawQuadratic_symm rho i j (ω n))

/-- A conditional L² anchor is a complex symmetric endpoint matrix. -/
theorem anchor_symmetric_ae
    {I : Type*} (rho : ℝ) (sigma : ℂ) {s : AnchoredCountingState}
    (p : ParticlePresentation s I) (anchor : (I → (Fin 4 → ℝ)) → EndpointMatrix)
    (ha : ∀ i j : Fin 4, (fun ω => anchor ω i j) =ᵐ[iidLaw (markLaw rho) I]
      (fun ω => l2Series (iidLaw (markLaw rho) I)
        (fun n => markQuadraticLp rho n i j)
        (fun n => sigma * particleCoefficient (p.location n) (Complex.I, false)) ω)) :
    ∀ᵐ ω ∂iidLaw (markLaw rho) I, (anchor ω).transpose = anchor ω := by
  have hall : ∀ᵐ ω ∂iidLaw (markLaw rho) I, ∀ i j : Fin 4,
      anchor ω i j = l2Series (iidLaw (markLaw rho) I)
        (fun n => markQuadraticLp rho n i j)
        (fun n => sigma * particleCoefficient (p.location n) (Complex.I, false)) ω :=
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => ha i j))
  filter_upwards [hall] with ω hω
  ext i j
  change anchor ω j i = anchor ω i j
  rw [hω j i, hω i j]
  rw [show (fun n : I => markQuadraticLp rho n j i) = (fun n => markQuadraticLp rho n i j) by
    funext n
    exact markQuadraticLp_symm rho n j i]

/-- The raw matrix associated with a fixed presented scalar state and its
actual analytic centered marked field. -/
def presentedRawMatrix
    {I : Type*} [Countable I] {s : AnchoredCountingState}
    (p : ParticlePresentation s I) (rho sigma center r : ℝ)
    (anchor : (I → (Fin 4 → ℝ)) → EndpointMatrix)
    (w : ℂ) (ω : I → (Fin 4 → ℝ)) : EndpointMatrix :=
  ((center : ℂ) + (sigma : ℂ) * anchoredNevanlinna s w) • covarianceMatrix (rho : ℂ) +
    (r : ℂ) • GeneralizedSwitching.edgeMatrix +
    Presented.matrixField p anchor (sigma : ℂ)
      (fun n γ i j => (rawQuadratic rho i j (γ n) : ℂ)) (w, false) ω

theorem presentedRawMatrix_symmetric
    {I : Type*} [Countable I] {s : AnchoredCountingState}
    (p : ParticlePresentation s I) (rho sigma center r : ℝ)
    (anchor : (I → (Fin 4 → ℝ)) → EndpointMatrix)
    (ω : I → (Fin 4 → ℝ)) (ha : (anchor ω).transpose = anchor ω) (w : ℂ) :
    (presentedRawMatrix p rho sigma center r anchor w ω).transpose =
      presentedRawMatrix p rho sigma center r anchor w ω := by
  ext i j
  have hcov : covarianceMatrix (rho : ℂ) j i = covarianceMatrix (rho : ℂ) i j := by
    rw [covarianceMatrix_eq]
    fin_cases i <;> fin_cases j <;> simp
  have hJ : (GeneralizedSwitching.edgeMatrix : EndpointMatrix) j i =
      GeneralizedSwitching.edgeMatrix i j := by
    fin_cases i <;> fin_cases j <;> rfl
  have hA : anchor ω j i = anchor ω i j := congrFun (congrFun ha i) j
  have hq : (fun n => (rawQuadratic rho j i (ω n) : ℂ)) =
      (fun n => (rawQuadratic rho i j (ω n) : ℂ)) := by
    funext n
    exact congrArg Complex.ofReal (rawQuadratic_symm rho j i (ω n))
  simp only [presentedRawMatrix, Matrix.transpose_apply, Matrix.add_apply,
    Matrix.smul_apply, Presented.matrixField, Bool.false_eq_true, ↓reduceIte,
    Presented.value, hcov, hJ]
  change _ + _ + Presented.anchoredEntry p (anchor ω j i) (sigma : ℂ) _ w =
    _ + _ + Presented.anchoredEntry p (anchor ω i j) (sigma : ℂ) _ w
  rw [hA, hq]

/-- The actual raw matrix has the uncentered Poisson marked imaginary part.
Every identity here is a samplewise consequence of the constructed anchor
and correction series. -/
theorem imaginaryPart_presentedRawMatrix
    {I : Type*} [Countable I] {s : AnchoredCountingState}
    (p : ParticlePresentation s I) (rho sigma center r : ℝ)
    (anchor : (I → (Fin 4 → ℝ)) → EndpointMatrix)
    (hlinear : anchoredLinearCoefficient s = 0)
    (ω : I → (Fin 4 → ℝ)) (hsym : (anchor ω).transpose = anchor ω)
    (ha : ∀ i j, (anchor ω i j).im =
      ∑' n, sigma * nevanlinnaWeight (p.location n) * rawQuadratic rho i j (ω n))
    (hweight : ∀ i j, Summable (fun n => nevanlinnaWeight (p.location n) *
      ‖(rawQuadratic rho i j (ω n) : ℂ)‖))
    {w : ℂ} (hw : w.im ≠ 0) :
    imaginaryPart (presentedRawMatrix p rho sigma center r anchor w ω) =
      ∑' n, ((sigma * poissonWeight (p.location n) w : ℝ) : ℂ) •
        outerMatrix (fun k => (ω n k : ℂ)) := by
  have hentry (i j : Fin 4) : HasSum
      (fun n => sigma * poissonWeight (p.location n) w * (ω n i * ω n j))
      (sigma * (anchoredNevanlinna s w).im * covarianceMatrix rho i j +
        ∑' n, sigma * poissonWeight (p.location n) w * rawQuadratic rho i j (ω n)) := by
    have hc := (hasSum_poissonWeight p hlinear hw).mul_left sigma
    have hd := hc.mul_right (covarianceMatrix rho i j)
    have hz := (summable_poissonWeight_mul_raw p sigma
      (fun n => rawQuadratic rho i j (ω n)) (hweight i j) hw).hasSum
    convert hd.add hz using 1
    funext n
    dsimp [rawQuadratic]
    ring
  have hmatrix : Summable (fun n => ((sigma * poissonWeight (p.location n) w : ℝ) : ℂ) •
      outerMatrix (fun k => (ω n k : ℂ))) := by
    apply Pi.summable.mpr
    intro i
    apply Pi.summable.mpr
    intro j
    simpa only [Matrix.smul_apply, outerMatrix, smul_eq_mul,
      Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul] using
      (Complex.ofRealCLM.hasSum (hentry i j)).summable
  rw [imaginaryPart_of_symmetric _ (presentedRawMatrix_symmetric p rho sigma center r anchor ω hsym w)]
  ext i j
  rw [tsum_apply hmatrix, tsum_apply (Pi.summable.mp hmatrix i)]
  have hs := (Complex.ofRealCLM.hasSum (hentry i j)).tsum_eq
  change (∑' n, ((sigma * poissonWeight (p.location n) w * (ω n i * ω n j) : ℝ) : ℂ)) =
    ((sigma * (anchoredNevanlinna s w).im * covarianceMatrix rho i j +
      ∑' n, sigma * poissonWeight (p.location n) w * rawQuadratic rho i j (ω n) : ℝ) : ℂ) at hs
  simp only [Matrix.smul_apply, outerMatrix, smul_eq_mul,
    Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul] at hs ⊢
  rw [hs]
  apply congrArg Complex.ofReal
  have hz := imaginary_anchoredEntry p (anchor ω i j) sigma
    (fun n => rawQuadratic rho i j (ω n)) (hweight i j) (ha i j) hw
  change ((presentedRawMatrix p rho sigma center r anchor w ω) i j).im = _
  simp only [presentedRawMatrix, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, covarianceMatrix_complex_entry, edgeMatrix_complex_entry,
    Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, add_zero, zero_add, Presented.matrixField,
    Bool.false_eq_true, ↓reduceIte, Presented.value, hz]

/-- Absolute convergence of the uncentered imaginary matrix series follows
from the centered weighted event and the deterministic scalar Poisson sum. -/
theorem summable_uncentered_poissonMatrix
    {I : Type*} [Countable I] {s : AnchoredCountingState}
    (p : ParticlePresentation s I) (rho sigma : ℝ)
    (hlinear : anchoredLinearCoefficient s = 0) (ω : I → (Fin 4 → ℝ))
    (hweight : ∀ i j, Summable (fun n => nevanlinnaWeight (p.location n) *
      ‖(rawQuadratic rho i j (ω n) : ℂ)‖))
    {w : ℂ} (hw : w.im ≠ 0) :
    Summable (fun n => ((sigma * poissonWeight (p.location n) w : ℝ) : ℂ) •
      outerMatrix (fun k => (ω n k : ℂ))) := by
  apply Pi.summable.mpr
  intro i
  apply Pi.summable.mpr
  intro j
  have hc := (hasSum_poissonWeight p hlinear hw).mul_left sigma
  have hd := hc.mul_right (covarianceMatrix rho i j)
  have hz := (summable_poissonWeight_mul_raw p sigma
    (fun n => rawQuadratic rho i j (ω n)) (hweight i j) hw).hasSum
  have hr : Summable (fun n => sigma * poissonWeight (p.location n) w * (ω n i * ω n j)) := by
    convert (hd.add hz).summable using 1
    funext n
    dsimp [rawQuadratic]
    ring
  simpa only [Matrix.smul_apply, outerMatrix, smul_eq_mul,
    Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul] using
    (Complex.ofRealCLM.hasSum hr.hasSum).summable

/-- The actual conditional analytic marked matrix is sign definite at every
nonreal spectral parameter, on one probability-one event. Four selected
particle occurrences and nondegenerate Gaussian marks supply strictness. -/
theorem presentedRawMatrix_ae_signDefinite
    {I : Type*} [Countable I] {s : AnchoredCountingState}
    (p : ParticlePresentation s I) (rho sigma center r : ℝ)
    (hrho : |rho| < 1) (hsigma : 0 < sigma)
    (anchor : (I → (Fin 4 → ℝ)) → EndpointMatrix)
    (hlinear : anchoredLinearCoefficient s = 0)
    (e : Fin 4 → I) (he : Function.Injective e)
    (hweight : ∀ᵐ ω ∂iidLaw (markLaw rho) I, ∀ i j : Fin 4,
      Summable (fun n => nevanlinnaWeight (p.location n) * ‖(rawQuadratic rho i j (ω n) : ℂ)‖))
    (ha : ∀ i j : Fin 4, (fun ω => anchor ω i j) =ᵐ[iidLaw (markLaw rho) I]
      (fun ω => l2Series (iidLaw (markLaw rho) I)
        (fun n => markQuadraticLp rho n i j)
        (fun n => (sigma : ℂ) * particleCoefficient (p.location n) (Complex.I, false)) ω)) :
    ∀ᵐ ω ∂iidLaw (markLaw rho) I, ∀ w : ℂ, w.im ≠ 0 →
      ImaginarySignDefinite (presentedRawMatrix p rho sigma center r anchor w ω) := by
  filter_upwards [anchor_imaginary_ae p rho hrho sigma anchor hweight ha,
    anchor_symmetric_ae rho (sigma : ℂ) p anchor ha, hweight,
    gaussianMarks_ae_posDef_all_weighted_tsum_selection rho hrho I e he]
    with ω him hsym hweight hspan
  intro w hw
  have hid := imaginaryPart_presentedRawMatrix p rho sigma center r anchor hlinear ω hsym him hweight hw
  have hs := summable_uncentered_poissonMatrix p rho sigma hlinear ω hweight hw
  by_cases hupper : 0 < w.im
  · apply Or.inl
    rw [hid]
    exact hspan _ (fun n => mul_pos hsigma (poissonWeight_pos _ hupper)) hs
  · apply Or.inr
    have hlower : w.im < 0 := lt_of_le_of_ne (le_of_not_gt hupper) hw
    have hpneg (n : I) : 0 < -(sigma * poissonWeight (p.location n) w) := by
      have hwneg : poissonWeight (p.location n) w < 0 :=
        div_neg_of_neg_of_pos hlower (Complex.normSq_pos.mpr (real_sub_ne_zero _ hw))
      exact neg_pos.mpr (mul_neg_of_pos_of_neg hsigma hwneg)
    have hn : Summable (fun n => ((-(sigma * poissonWeight (p.location n) w) : ℝ) : ℂ) •
        outerMatrix (fun k => (ω n k : ℂ))) := by
      simpa only [Complex.ofReal_neg, neg_smul] using hs.neg
    rw [hid]
    have heq : -(∑' n, ((sigma * poissonWeight (p.location n) w : ℝ) : ℂ) •
        outerMatrix (fun k => (ω n k : ℂ))) =
      ∑' n, ((-(sigma * poissonWeight (p.location n) w) : ℝ) : ℂ) •
        outerMatrix (fun k => (ω n k : ℂ)) := by
      simpa only [Complex.ofReal_neg, neg_smul] using (tsum_neg (f := fun n => ((sigma * poissonWeight (p.location n) w : ℝ) : ℂ) •
        outerMatrix (fun k => (ω n k : ℂ)))).symm
    rw [heq]
    exact hspan _ hpneg hn

end GeneralizedBulk.Exterior
