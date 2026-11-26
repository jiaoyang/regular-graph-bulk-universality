import GaussianWave.BS.LogDensityFactorization
import GaussianWave.BS.UpperStrictness
import GaussianWave.BS.LogDensityRigidity

/-!
# Actual characteristic factorization from a linear transverse heat score

The Gaussian factor is derived from integration by parts and a scalar
characteristic-function differential equation. Independence is a conclusion.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators

namespace GaussianWave.BS
variable {I : Type*} [Fintype I]

private def phase (q x : I → ℝ) : ℂ :=
  Complex.exp ((finiteLinearForm q x : ℂ) * Complex.I)

private theorem norm_phase (q x : I → ℝ) : ‖phase q x‖ = 1 := by
  simp [phase, Complex.norm_exp]

private theorem continuous_phase (q : I → ℝ) : Continuous (phase q) := by
  unfold phase
  exact (((Complex.continuous_ofReal.comp (continuous_finiteLinearForm q)).mul continuous_const)).cexp

private theorem integrable_phase (P : Measure (I → ℝ)) [IsFiniteMeasure P] (q : I → ℝ) :
    Integrable (phase q) P := by
  apply (integrable_const (1 : ℝ)).mono' (continuous_phase q).measurable.aestronglyMeasurable
  exact ae_of_all _ (fun x => (norm_phase q x).le)

private theorem integrable_real_mul_phase (P : Measure (I → ℝ))
    (g : (I → ℝ) → ℝ) (hg : Integrable g P) (q : I → ℝ) :
    Integrable (fun x => (g x : ℂ) * phase q x) P := by
  apply hg.norm.mono' ((Complex.continuous_ofReal.comp_aestronglyMeasurable hg.aestronglyMeasurable).mul
    (continuous_phase q).measurable.aestronglyMeasurable)
  exact ae_of_all _ (fun x => by simp [norm_mul, Complex.norm_real, norm_phase])

private theorem hasDerivAt_cexp_affine (a b s : ℝ) :
    HasDerivAt (fun u : ℝ => Complex.exp (((a + u * b : ℝ) : ℂ) * Complex.I))
      (((b : ℂ) * Complex.I) * Complex.exp (((a + s * b : ℝ) : ℂ) * Complex.I)) s := by
  convert ((((hasDerivAt_const s a).add ((hasDerivAt_id s).mul_const b)).ofReal_comp).mul_const
    Complex.I).cexp using 1
  simp only [zero_add, one_mul, id_eq]
  ring

private theorem finiteLinearForm_line_coeff (q w x : I → ℝ) (s : ℝ) :
    finiteLinearForm (q + s • w) x = finiteLinearForm q x + s * finiteLinearForm w x := by
  simp only [finiteLinearForm, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => by ring)

private theorem finiteLinearForm_line_point (q x w : I → ℝ) (s : ℝ) :
    finiteLinearForm q (x + s • w) = finiteLinearForm q x + s * finiteLinearForm q w := by
  simp only [finiteLinearForm, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => by ring)

private theorem hasDerivAt_phase_line_coeff (q w x : I → ℝ) (s : ℝ) :
    HasDerivAt (fun u : ℝ => phase (q + u • w) x)
      (((finiteLinearForm w x : ℂ) * Complex.I) * phase (q + s • w) x) s := by
  simpa only [phase, finiteLinearForm_line_coeff] using
    hasDerivAt_cexp_affine (finiteLinearForm q x) (finiteLinearForm w x) s

private theorem hasLineDerivAt_phase (q x w : I → ℝ) :
    HasLineDerivAt ℝ (phase q)
      (((finiteLinearForm q w : ℂ) * Complex.I) * phase q x) x w := by
  change HasDerivAt (fun s : ℝ => phase q (x + s • w)) _ 0
  simpa only [phase, finiteLinearForm_line_point, zero_mul, add_zero] using
    hasDerivAt_cexp_affine (finiteLinearForm q x) (finiteLinearForm q w) 0

/-- The directional derivative of an actual characteristic integral, from
integrable first moment in the chosen direction. -/
theorem hasDerivAt_characteristicIntegral_line
    (P : Measure (I → ℝ)) [IsProbabilityMeasure P]
    (w : I → ℝ) (hw : Integrable (finiteLinearForm w) P) (q : I → ℝ) (s : ℝ) :
    HasDerivAt (fun u : ℝ => characteristicIntegral P (q + u • w))
      (Complex.I * ∫ x, (finiteLinearForm w x : ℂ) * phase (q + s • w) x ∂P) s := by
  have hm (u : ℝ) : AEStronglyMeasurable (fun x => phase (q + u • w) x) P :=
    (continuous_phase _).measurable.aestronglyMeasurable
  have hgm (u : ℝ) : AEStronglyMeasurable
      (fun x => ((finiteLinearForm w x : ℂ) * Complex.I) * phase (q + u • w) x) P :=
    (((Complex.continuous_ofReal.comp (continuous_finiteLinearForm w)).mul continuous_const).mul
      (continuous_phase _)).measurable.aestronglyMeasurable
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := P) (x₀ := s) (ε := 1)
    (F := fun u x => phase (q + u • w) x)
    (F' := fun u x => ((finiteLinearForm w x : ℂ) * Complex.I) * phase (q + u • w) x)
    (bound := fun x => ‖finiteLinearForm w x‖)
    zero_lt_one (Eventually.of_forall hm) (integrable_phase P _) (hgm s)
    (ae_of_all _ (fun x u _ => by simp [norm_mul, Complex.norm_real,
      Complex.norm_I, norm_phase])) hw.norm
    (ae_of_all _ (fun x u _ => hasDerivAt_phase_line_coeff q w x u))
  convert hd.2 using 1
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by ring)

/-- The actual Stein identity supplied by a linear transverse heat score.
Every integral is genuinely integrable, by finite input second moment. -/
theorem heat_linear_score_stein
    [DecidableEq I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) {t : ℝ} (ht : 0 < t)
    (w : I → ℝ) (κ : ℝ)
    (hscore : ∀ x, heatDirectionalScore μ t w x = κ * finiteLinearForm w x)
    (q : I → ℝ) :
    (κ : ℂ) * (∫ x, (finiteLinearForm w x : ℂ) * phase q x ∂heatedLaw μ t) =
      -((finiteLinearForm q w : ℂ) * Complex.I) * characteristicIntegral (heatedLaw μ t) q := by
  have h2 := integrable_heatDensity_mul_linearForm_sq μ hμ ht w
  have h1 : Integrable (fun x => finiteLinearForm w x * heatDensity μ t x) := by
    apply ((integrable_heatDensity μ ht).add h2).mono'
      (((continuous_finiteLinearForm w).measurable.mul (measurable_heatDensity μ t)).aestronglyMeasurable)
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatDensity_nonneg _ _ _)]
    change |finiteLinearForm w x| * heatDensity μ t x ≤
      heatDensity μ t x + heatDensity μ t x * finiteLinearForm w x ^ 2
    have habs : |finiteLinearForm w x| ≤ 1 + finiteLinearForm w x ^ 2 := by
      nlinarith [sq_nonneg (|finiteLinearForm w x| - 1), sq_abs (finiteLinearForm w x)]
    nlinarith [mul_le_mul_of_nonneg_right habs (heatDensity_nonneg μ t x)]
  have hg (x : I → ℝ) : HasLineDerivAt ℝ (heatDensity μ t)
      (κ * finiteLinearForm w x * heatDensity μ t x) x w := by
    have hs := hscore x
    unfold heatDirectionalScore at hs
    have hn := (div_eq_iff (heatDensity_pos μ ht x).ne').mp hs
    have hd := hasDerivAt_heatDensity_line μ ht x w 0
    simp only [zero_smul, add_zero] at hd
    exact hn ▸ hd
  have hfg : Integrable (fun x => heatDensity μ t x • phase q x) := by
    simpa only [Complex.real_smul] using
      integrable_real_mul_phase volume (heatDensity μ t) (integrable_heatDensity μ ht) q
  have hf'g : Integrable (fun x => (κ * finiteLinearForm w x * heatDensity μ t x) • phase q x) := by
    simpa only [Complex.real_smul, mul_assoc] using integrable_real_mul_phase volume _ (h1.const_mul κ) q
  have hfg' : Integrable (fun x => heatDensity μ t x •
      (((finiteLinearForm q w : ℂ) * Complex.I) * phase q x)) := by
    convert (integrable_real_mul_phase volume (heatDensity μ t) (integrable_heatDensity μ ht) q).const_mul
      ((finiteLinearForm q w : ℂ) * Complex.I) using 1
    funext x
    simp only [Complex.real_smul]
    ring
  have hparts := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.lsmul ℝ ℝ) hf'g hfg' hfg hg (fun x => hasLineDerivAt_phase q x w)
  simp only [ContinuousLinearMap.lsmul_apply, Complex.real_smul] at hparts
  have hchar : characteristicIntegral (heatedLaw μ t) q =
      ∫ x, (heatDensity μ t x : ℂ) * phase q x := by
    rw [characteristicIntegral, heatedLaw_eq_withDensity μ ht,
      integral_withDensity_eq_integral_toReal_smul (measurable_heatDensity μ t).ennreal_ofReal
        (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (heatDensity_nonneg _ _ _), Complex.real_smul]
    rfl
  have hmoment : (∫ x, (finiteLinearForm w x : ℂ) * phase q x ∂heatedLaw μ t) =
      ∫ x, ((finiteLinearForm w x * heatDensity μ t x : ℝ) : ℂ) * phase q x := by
    rw [heatedLaw_eq_withDensity μ ht,
      integral_withDensity_eq_integral_toReal_smul (measurable_heatDensity μ t).ennreal_ofReal
        (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (heatDensity_nonneg _ _ _), Complex.real_smul]
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by push_cast; ring)
  rw [hchar, hmoment, ← integral_const_mul, ← integral_const_mul]
  have heqL : (fun x => (heatDensity μ t x : ℂ) *
      (((finiteLinearForm q w : ℂ) * Complex.I) * phase q x)) =
      (fun x => ((finiteLinearForm q w : ℂ) * Complex.I) *
        ((heatDensity μ t x : ℂ) * phase q x)) := by funext x; ring
  have heqR : (fun x => ((κ * finiteLinearForm w x * heatDensity μ t x : ℝ) : ℂ) * phase q x) =
      (fun x => (κ : ℂ) * (((finiteLinearForm w x * heatDensity μ t x : ℝ) : ℂ) * phase q x)) := by
    funext x
    push_cast
    ring
  rw [heqL, heqR, integral_const_mul, integral_const_mul] at hparts
  rw [integral_const_mul, integral_const_mul]
  linear_combination hparts

theorem integrable_heatedLaw_linearForm
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) (t : ℝ) (w : I → ℝ) :
    Integrable (finiteLinearForm w) (heatedLaw μ t) := by
  apply ((integrable_const (1 : ℝ)).add (integrable_heatedLaw_linearForm_sq μ hμ t w)).mono'
    (continuous_finiteLinearForm w).measurable.aestronglyMeasurable
  filter_upwards [] with x
  change |finiteLinearForm w x| ≤ 1 + finiteLinearForm w x ^ 2
  nlinarith [sq_nonneg (|finiteLinearForm w x| - 1), sq_abs (finiteLinearForm w x)]

theorem hasDerivAt_characteristicIntegral_transverse
    [DecidableEq I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) {t : ℝ} (ht : 0 < t)
    (w : I → ℝ) (hunit : squareRadius w = 1) (V : ℝ) (hV : 0 < V)
    (hscore : ∀ x, heatDirectionalScore μ t w x = -(1 / V) * finiteLinearForm w x)
    (q : I → ℝ) (hq : finiteLinearForm q w = 0) (s : ℝ) :
    HasDerivAt (fun u : ℝ => characteristicIntegral (heatedLaw μ t) (q + u • w))
      (-((V * s : ℝ) : ℂ) * characteristicIntegral (heatedLaw μ t) (q + s • w)) s := by
  let M : ℂ := ∫ x, (finiteLinearForm w x : ℂ) * phase (q + s • w) x ∂heatedLaw μ t
  let C : ℂ := characteristicIntegral (heatedLaw μ t) (q + s • w)
  have hdot : finiteLinearForm (q + s • w) w = s := by
    rw [finiteLinearForm_line_coeff, hq]
    have hw : finiteLinearForm w w = 1 := by simpa only [finiteLinearForm, squareRadius, pow_two] using hunit
    rw [hw, mul_one, zero_add]
  have hstein := heat_linear_score_stein μ hμ ht w (-(1 / V)) hscore (q + s • w)
  rw [hdot] at hstein
  change ((-(1 / V) : ℝ) : ℂ) * M = -((s : ℂ) * Complex.I) * C at hstein
  push_cast at hstein
  have hV0 : (V : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hV.ne'
  have hκ0 : -(1 / (V : ℂ)) ≠ 0 := by simp [hV0]
  have hM : M = (V : ℂ) * (s : ℂ) * Complex.I * C := by
    apply mul_left_cancel₀ hκ0
    rw [hstein]
    field_simp
    ring
  have hd := hasDerivAt_characteristicIntegral_line (heatedLaw μ t) w
    (integrable_heatedLaw_linearForm μ hμ t w) q s
  apply hd.congr_deriv
  change Complex.I * M = -((V * s : ℝ) : ℂ) * C
  rw [hM]
  calc
    _ = (V : ℂ) * (s : ℂ) * Complex.I ^ 2 * C := by ring
    _ = _ := by rw [Complex.I_sq]; push_cast; ring

/-- The actual Gaussian characteristic factor in every unit transverse
direction. This solves the derived scalar ODE; factorization is a conclusion. -/
theorem characteristicIntegral_transverse_factorization
    [DecidableEq I]
    (μ : Measure (I → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := I)) μ) {t : ℝ} (ht : 0 < t)
    (w : I → ℝ) (hunit : squareRadius w = 1) (V : ℝ) (hV : 0 < V)
    (hscore : ∀ x, heatDirectionalScore μ t w x = -(1 / V) * finiteLinearForm w x)
    (q : I → ℝ) (hq : finiteLinearForm q w = 0) (s : ℝ) :
    characteristicIntegral (heatedLaw μ t) (q + s • w) =
      characteristicIntegral (heatedLaw μ t) q * Complex.exp (-((V * s ^ 2 : ℝ) : ℂ) / 2) := by
  let C : ℝ → ℂ := fun u => characteristicIntegral (heatedLaw μ t) (q + u • w)
  let A : ℝ → ℂ := fun u => Complex.exp (((V * u ^ 2 : ℝ) : ℂ) / 2)
  have hA (u : ℝ) : HasDerivAt A (A u * ((V * u : ℝ) : ℂ)) u := by
    convert (((((hasDerivAt_id u).pow 2).const_mul V).ofReal_comp).div_const (2 : ℂ)).cexp using 1
    dsimp [A]
    push_cast
    ring
  have hC (u : ℝ) : HasDerivAt C (-((V * u : ℝ) : ℂ) * C u) u :=
    hasDerivAt_characteristicIntegral_transverse μ hμ ht w hunit V hV hscore q hq u
  have hzero (u : ℝ) : HasDerivAt (fun z => A z * C z) 0 u := by
    convert (hA u).mul (hC u) using 1
    ring
  have hconst := is_const_of_deriv_eq_zero (fun u => (hzero u).differentiableAt)
    (fun u => (hzero u).deriv) s 0
  have hc0 : A 0 * C 0 = characteristicIntegral (heatedLaw μ t) q := by simp [A, C]
  rw [hc0] at hconst
  change C s = _
  calc
    _ = Complex.exp (-((V * s ^ 2 : ℝ) : ℂ) / 2) * (A s * C s) := by
      dsimp [A]
      rw [← mul_assoc, ← Complex.exp_add, neg_div, neg_add_cancel, Complex.exp_zero, one_mul]
    _ = _ := by rw [hconst]; ring

/-- The actual all-transverse characteristic factorization forced by zero
strict-bulk BS Fisher defect. The log shape, transverse Gaussian coefficient,
linear score, Stein identity, and characteristic ODE are all conclusions of
the preceding proofs. -/
theorem star_characteristic_transverse_factorization_of_fisherDefect_zero
    (d : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hμ : Integrable (squareRadius (I := Fin d)) μ) (hmom : HasIdentitySecondMoments μ)
    {t : ℝ} (ht : 0 < t)
    (hrev : ∀ i, Measure.map binarySwap
      (Measure.map (fun x => (starEdgeProjection d c i).mulVec x) μ) =
        Measure.map (fun x => (starEdgeProjection d c i).mulVec x) μ)
    (hzero : heatFrameFisherDefect μ (starEdgeProjection d c) t = 0)
    (hperm : ∀ p : Equiv.Perm (Fin d),
      Measure.map (fun x : Fin d → ℝ => fun j => x (p j)) μ = μ)
    (w : Fin d → ℝ) (hw : ∑ j, w j = 0) (hunit : squareRadius w = 1) (a s : ℝ) :
    characteristicIntegral (heatedLaw μ t) (a • starRootDirection d + s • w) =
      (∫ r : ℝ, Complex.exp (((a * r : ℝ) : ℂ) * Complex.I)
        ∂Measure.map starRootForm (heatedLaw μ t)) *
        Complex.exp (-(((1 + 2 * t) * s ^ 2 : ℝ) : ℂ) / 2) := by
  let i₀ : Fin d := ⟨0, by omega⟩
  let L := fun y : Fin d → ℝ => Real.log (heatDensity μ t y)
  let κ := fderiv ℝ (fderiv ℝ L) 0 (starSimplexDirection d i₀) (starSimplexDirection d i₀)
  have hshape : ∀ x, Real.log (heatDensity μ t x) =
      Real.log (heatDensity μ t (starRootPart d x)) + (κ / 2) * squareMass (x - starRootPart d x) := by
    intro x
    simpa only [κ, L, starTransversePart, LinearMap.sub_apply, LinearMap.id_apply, squareMass, squareRadius]
      using log_heatDensity_root_plus_isotropic_quadratic_of_fisherDefect_zero
        d hd c hbulk μ ht hrev hzero hperm i₀ x
  have hwP : starRootPart d w = 0 := starRootPart_of_sum_zero w hw
  have hperp (x : Fin d → ℝ) : finiteLinearForm w (starRootPart d x) = 0 := by
    simp only [finiteLinearForm, starRootPart_apply, ← Finset.sum_mul, hw, zero_mul]
  have hκ := quadratic_logshape_coefficient_of_identitySecondMoments μ hμ hmom ht
    (starRootPart d) κ hshape w hwP hperp hunit
  have hscore (x : Fin d → ℝ) : heatDirectionalScore μ t w x =
      -(1 / (1 + 2 * t)) * finiteLinearForm w x := by
    rw [heatDirectionalScore_of_quadratic_logshape μ ht (starRootPart d) κ hshape w hwP hperp x, hκ]
  have hq : finiteLinearForm (a • starRootDirection d) w = 0 := by
    simp only [finiteLinearForm, Pi.smul_apply, smul_eq_mul, starRootDirection, ← Finset.mul_sum, hw, mul_zero]
  have hrootform (x : Fin d → ℝ) :
      finiteLinearForm (a • starRootDirection d) x = a * starRootForm x := by
    simp only [finiteLinearForm, Pi.smul_apply, smul_eq_mul, starRootDirection, starRootForm, ← Finset.mul_sum]
    ring
  have hrootchar : characteristicIntegral (heatedLaw μ t) (a • starRootDirection d) =
      ∫ r : ℝ, Complex.exp (((a * r : ℝ) : ℂ) * Complex.I)
        ∂Measure.map starRootForm (heatedLaw μ t) := by
    rw [integral_map (by unfold starRootForm; fun_prop : Measurable
      (starRootForm : (Fin d → ℝ) → ℝ)).aemeasurable
      (show Continuous (fun r : ℝ => Complex.exp (((a * r : ℝ) : ℂ) * Complex.I)) by
        fun_prop).measurable.aestronglyMeasurable]
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by
      change Complex.exp ((finiteLinearForm (a • starRootDirection d) x : ℂ) * Complex.I) = _
      rw [hrootform])
  rw [← hrootchar]
  exact characteristicIntegral_transverse_factorization μ hμ ht w hunit (1 + 2 * t)
    (by positivity) hscore (a • starRootDirection d) hq s

end GaussianWave.BS
