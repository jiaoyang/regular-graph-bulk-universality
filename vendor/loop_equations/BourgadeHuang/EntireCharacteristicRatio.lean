import BourgadeHuang.CanonicalProductFactor
import BourgadeHuang.CharacteristicRatioAnalytic

/-! The genuine canonical entire numerator of an anchored counting state.
The product uses its actual particles, with their integer multiplicities; its
logarithmic derivative is the reconstructed Nevanlinna function. -/
noncomputable section
open scoped Topology BigOperators
open MeasureTheory Filter
namespace BourgadeHuang

/-- The convergent genus-one product over the actual particle labels. -/
def canonicalParticleProduct (s : AnchoredCountingState) (z : ℂ) : ℂ :=
  ∏' i : s.val.1.ParticleLabels, canonicalParticleFactor (s.val.1.particleLocation i) z

theorem differentiable_canonicalParticleProduct (s : AnchoredCountingState) :
    Differentiable ℂ (canonicalParticleProduct s) :=
  (locallySummable_canonicalParticleFactors s).differentiable
    (fun i => differentiable_canonicalParticleFactor (s.val.1.particleLocation i))

@[simp] theorem canonicalParticleProduct_I (s : AnchoredCountingState) :
    canonicalParticleProduct s Complex.I = 1 := by simp [canonicalParticleProduct]

theorem canonicalParticleProduct_ne_zero (s : AnchoredCountingState) {z : ℂ} (hz : z.im ≠ 0) :
    canonicalParticleProduct s z ≠ 0 :=
  (locallySummable_canonicalParticleFactors s).ne_zero (fun i => canonicalParticleFactor_ne_zero (s.val.1.particleLocation i) hz)

/-- The summed logarithmic derivative is an absolutely convergent reciprocal difference. -/
theorem hasSum_canonical_logDerivative (s : AnchoredCountingState) {z : ℂ} (hz : z.im ≠ 0) :
    HasSum (fun i : s.val.1.ParticleLabels =>
      (((s.val.1.particleLocation i:ℂ)-Complex.I)⁻¹-((s.val.1.particleLocation i:ℂ)-z)⁻¹))
      (s.val.2-anchoredNevanlinna s z+(anchoredLinearCoefficient s:ℂ)*(z-Complex.I)) := by
  have hI : Complex.I.im ≠ 0 := by simp
  have hi := (integrable_regularizedResolventKernel s hI).sub (integrable_regularizedResolventKernel s hz)
  have he (x : ℝ) : regularizedResolventKernel Complex.I x-regularizedResolventKernel z x =
      ((x:ℂ)-Complex.I)⁻¹-((x:ℂ)-z)⁻¹ := by
    unfold regularizedResolventKernel
    ring
  have hs := s.val.1.hasSum_particleLocations hi
  change HasSum (fun i : s.val.1.ParticleLabels =>
    regularizedResolventKernel Complex.I (s.val.1.particleLocation i)-
      regularizedResolventKernel z (s.val.1.particleLocation i))
    (∫ x, regularizedResolventKernel Complex.I x-regularizedResolventKernel z x ∂s.val.1.measure) at hs
  simp_rw [he] at hs
  convert hs using 1
  have hrepI := anchoredNevanlinna_eq_regularized s hI
  rw [anchoredNevanlinna_I] at hrepI
  rw [← integral_congr_ae (Filter.Eventually.of_forall he)]
  rw [integral_sub (integrable_regularizedResolventKernel s hI)
    (integrable_regularizedResolventKernel s hz),hrepI,anchoredNevanlinna_eq_regularized s hz]
  ring

theorem hasDerivAt_canonicalParticleProduct (s : AnchoredCountingState) {z : ℂ} (hz : z.im ≠ 0) :
    HasDerivAt (canonicalParticleProduct s)
      ((s.val.2-anchoredNevanlinna s z+(anchoredLinearCoefficient s:ℂ)*(z-Complex.I))*
        canonicalParticleProduct s z) z := by
  have h := (locallySummable_canonicalParticleFactors s).hasDerivAt
    (fun i => differentiable_canonicalParticleFactor (s.val.1.particleLocation i)) z _
    (hasSum_canonical_logDerivative s hz).summable
    (fun i => hasDerivAt_canonicalParticleFactor _ hz)
  simpa only [(hasSum_canonical_logDerivative s hz).tsum_eq] using h

/-- The anchor and the nonnegative linear drift fix the normalization of the
canonical entire numerator, with F(i)=1. -/
def anchoredEntireNumerator (s : AnchoredCountingState) (z : ℂ) : ℂ :=
  Complex.exp (-s.val.2*(z-Complex.I)-(anchoredLinearCoefficient s:ℂ)*(z-Complex.I)^2/2)*
    canonicalParticleProduct s z

theorem differentiable_anchoredEntireNumerator (s : AnchoredCountingState) :
    Differentiable ℂ (anchoredEntireNumerator s) := by
  apply Differentiable.mul _ (differentiable_canonicalParticleProduct s)
  apply Differentiable.cexp
  fun_prop

theorem analyticAt_anchoredEntireNumerator (s : AnchoredCountingState) (z : ℂ) :
    AnalyticAt ℂ (anchoredEntireNumerator s) z :=
  (differentiable_anchoredEntireNumerator s).analyticAt z

@[simp] theorem anchoredEntireNumerator_I (s : AnchoredCountingState) :
    anchoredEntireNumerator s Complex.I = 1 := by simp [anchoredEntireNumerator]

theorem anchoredEntireNumerator_ne_zero (s : AnchoredCountingState) {z : ℂ} (hz : z.im ≠ 0) :
    anchoredEntireNumerator s z ≠ 0 :=
  mul_ne_zero (Complex.exp_ne_zero _) (canonicalParticleProduct_ne_zero s hz)

/-- The entire numerator has exactly the prescribed logarithmic derivative. -/
theorem hasDerivAt_anchoredEntireNumerator (s : AnchoredCountingState) {z : ℂ} (hz : z.im ≠ 0) :
    HasDerivAt (anchoredEntireNumerator s)
      (-anchoredNevanlinna s z*anchoredEntireNumerator s z) z := by
  have hQ : HasDerivAt
      (fun w : ℂ => -s.val.2*(w-Complex.I)-(anchoredLinearCoefficient s:ℂ)*(w-Complex.I)^2/2)
      (-s.val.2-(anchoredLinearCoefficient s:ℂ)*(z-Complex.I)) z := by
    convert ((((hasDerivAt_id z).sub_const Complex.I).const_mul (-s.val.2)).sub
      (((((hasDerivAt_id z).sub_const Complex.I).pow 2).const_mul
        (anchoredLinearCoefficient s:ℂ)).div_const 2)) using 1
    simp only [id_eq]
    ring
  have h := hQ.cexp.mul (hasDerivAt_canonicalParticleProduct s hz)
  convert h using 1
  unfold anchoredEntireNumerator
  ring

/-- The numerator may be anywhere in the complex plane; every off-real
 denominator gives the actual normalized characteristic ratio. -/
def entireCharacteristicRatio (s : AnchoredCountingState) (u v : ℂ) : ℂ :=
  anchoredEntireNumerator s u / anchoredEntireNumerator s v

theorem differentiable_entireCharacteristicRatio_numerator (s : AnchoredCountingState) (v : ℂ) :
    Differentiable ℂ (fun u => entireCharacteristicRatio s u v) :=
  (differentiable_anchoredEntireNumerator s).div_const _

theorem entireCharacteristicRatio_ne_zero (s : AnchoredCountingState) {u v : ℂ}
    (hu : u.im ≠ 0) (hv : v.im ≠ 0) : entireCharacteristicRatio s u v ≠ 0 :=
  div_ne_zero (anchoredEntireNumerator_ne_zero s hu) (anchoredEntireNumerator_ne_zero s hv)

@[simp] theorem entireCharacteristicRatio_self (s : AnchoredCountingState) {v : ℂ} (hv : v.im ≠ 0) :
    entireCharacteristicRatio s v v = 1 := div_self (anchoredEntireNumerator_ne_zero s hv)

theorem hasDerivAt_entireCharacteristicRatio_numerator (s : AnchoredCountingState) {u v : ℂ}
    (hu : u.im ≠ 0) : HasDerivAt (fun z => entireCharacteristicRatio s z v)
      (-anchoredNevanlinna s u*entireCharacteristicRatio s u v) u := by
  simpa only [entireCharacteristicRatio,mul_div_assoc] using
    (hasDerivAt_anchoredEntireNumerator s hu).div_const (anchoredEntireNumerator s v)

/-- The canonical entire ratio agrees with the original path-integral ratio
where both arguments are in one open half-plane. -/
theorem entireCharacteristicRatio_eq_anchored (s : AnchoredCountingState) {u v : ℂ}
    (huv : SameOpenHalfPlane u v) :
    entireCharacteristicRatio s u v = anchoredCharacteristicRatio s u v := by
  let A := fun z => anchoredEntireNumerator s z*anchoredCharacteristicRatio s v z
  have hd (z : ℂ) (hz : SameOpenHalfPlane z v) : HasDerivAt A 0 z := by
    have h := (hasDerivAt_anchoredEntireNumerator s hz.left_offReal).mul
      (hasDerivAt_anchoredCharacteristicRatio_denominator s hz.symm)
    convert h using 1
    ring
  have hc (z : ℂ) : HasDerivAt (fun _ : ℂ => anchoredEntireNumerator s v) 0 z := hasDerivAt_const _ _
  have heq := (isOpen_sameOpenHalfPlane v).eqOn_of_deriv_eq
    (convex_sameOpenHalfPlane huv.right_offReal).isPreconnected
    (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)
    (fun z _ => (hc z).differentiableAt.differentiableWithinAt)
    (fun z hz => (hd z hz).deriv.trans (hc z).deriv.symm)
    (sameOpenHalfPlane_self_of_offReal huv.right_offReal)
    (show A v = anchoredEntireNumerator s v by simp [A,anchoredCharacteristicRatio_self])
  have he := heq huv
  change anchoredEntireNumerator s u*anchoredCharacteristicRatio s v u = anchoredEntireNumerator s v at he
  rw [anchoredCharacteristicRatio_swap] at he
  apply (div_eq_iff (anchoredEntireNumerator_ne_zero s huv.right_offReal)).mpr
  calc
    anchoredEntireNumerator s u = anchoredEntireNumerator s v*anchoredCharacteristicRatio s u v :=
      (div_eq_iff (anchoredCharacteristicRatio_ne_zero s u v)).mp he
    _ = _ := mul_comm _ _

end BourgadeHuang
