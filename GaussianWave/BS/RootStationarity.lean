import GaussianWave.BS.LogDensityRigidity

/-!
# Actual root OU stationarity from independent transverse noise and reversal

The pair factorization is equality with a genuine product probability law.
Combined with reversal of the actual two-coordinate edge observation it
produces equality of actual scalar OU laws. Characteristic iteration then
identifies the root Gaussian, without a moment or Gaussianity assumption on
the unknown root law.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal
namespace GaussianWave.BS

/-- Scalar characteristic integral in the same real coordinates as the root. -/
def scalarCharacteristic (ν : Measure ℝ) (s : ℝ) : ℂ :=
  ∫ x : ℝ, Complex.exp ((↑(s * x) : ℂ) * Complex.I) ∂ν

lemma continuous_scalarCharacteristicIntegrand (s : ℝ) :
    Continuous (fun x : ℝ => Complex.exp ((↑(s * x) : ℂ) * Complex.I)) := by fun_prop

lemma scalarCharacteristic_eq_charFun (ν : Measure ℝ) (s : ℝ) :
    scalarCharacteristic ν s = charFun ν s := by
  simp only [scalarCharacteristic, charFun_apply_real, Complex.ofReal_mul]

/-- The literal scalar OU step with independent Gaussian noise. -/
def scalarOULaw (ν : Measure ℝ) (v : ℝ≥0) (c : ℝ) : Measure ℝ :=
  Measure.map (fun z : ℝ × ℝ => c * z.1 + rho c * z.2) (ν.prod (gaussianReal 0 v))

lemma measurable_scalarOUMap (c : ℝ) :
    Measurable (fun z : ℝ × ℝ => c * z.1 + rho c * z.2) := by fun_prop

instance scalarOULaw_isProbability (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (v : ℝ≥0) (c : ℝ) : IsProbabilityMeasure (scalarOULaw ν v c) :=
  isProbabilityMeasure_map (measurable_scalarOUMap c).aemeasurable

lemma scalarOULaw_characteristic (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (v : ℝ≥0) (c s : ℝ) :
    scalarCharacteristic (scalarOULaw ν v c) s =
      scalarCharacteristic ν (c * s) *
        Complex.exp (Complex.ofReal (-(1 / 2 : ℝ) * (v : ℝ) * (rho c) ^ 2 * s ^ 2)) := by
  rw [scalarCharacteristic, scalarOULaw,
    integral_map (measurable_scalarOUMap c).aemeasurable
      (continuous_scalarCharacteristicIntegrand s).measurable.aestronglyMeasurable]
  have heq (z : ℝ × ℝ) :
      Complex.exp ((↑(s * (c * z.1 + rho c * z.2)) : ℂ) * Complex.I) =
        Complex.exp ((↑((c * s) * z.1) : ℂ) * Complex.I) *
          Complex.exp ((↑((rho c * s) * z.2) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [heq]
  rw [integral_prod_mul
    (fun x : ℝ => Complex.exp ((↑((c * s) * x) : ℂ) * Complex.I))
    (fun x : ℝ => Complex.exp ((↑((rho c * s) * x) : ℂ) * Complex.I)),
    centeredGaussian_characteristic_integral]
  congr 2
  push_cast
  ring

lemma scalarCharacteristic_scale_tendsto_one (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (a : ℕ → ℝ) (ha : Tendsto a atTop (𝓝 0)) (s : ℝ) :
    Tendsto (fun n => scalarCharacteristic ν (a n * s)) atTop (𝓝 1) := by
  have h := tendsto_integral_of_dominated_convergence (μ := ν)
    (F := fun (n : ℕ) (x : ℝ) => Complex.exp ((↑((a n * s) * x) : ℂ) * Complex.I))
    (f := fun _ => (1 : ℂ)) (fun _ => (1 : ℝ))
    (fun n => (continuous_scalarCharacteristicIntegrand (a n * s)).measurable.aestronglyMeasurable)
    (integrable_const 1)
    (fun _ => Eventually.of_forall (fun _ => by simp [Complex.norm_exp]))
    (Eventually.of_forall (fun x => by
      have hr : Tendsto (fun n => (a n * s) * x) atTop (𝓝 0) := by
        simpa using (ha.mul_const s).mul_const x
      have hc := (Complex.continuous_ofReal.tendsto 0).comp hr
      simpa using Complex.continuous_exp.continuousAt.tendsto.comp (hc.mul_const Complex.I)))
  simpa only [scalarCharacteristic, integral_const, measureReal_univ_eq_one, one_smul] using h

/-- Scalar version of the proved finite-channel OU uniqueness argument.
The contracting characteristic iteration needs no moments of the root law. -/
theorem eq_gaussianReal_of_scalarOU_stationary (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (v : ℝ≥0) (c : ℝ) (hc : |c| < 1) (hstationary : scalarOULaw ν v c = ν) :
    ν = gaussianReal 0 v := by
  have hrec (s : ℝ) : scalarCharacteristic ν s =
      scalarCharacteristic ν (c * s) *
        Complex.exp (Complex.ofReal (-(1 / 2 : ℝ) * (v : ℝ) * (1 - c ^ 2) * s ^ 2)) := by
    calc
      _ = scalarCharacteristic (scalarOULaw ν v c) s := by rw [hstationary]
      _ = _ := by rw [scalarOULaw_characteristic, rho_sq c hc]
  have hchar (s : ℝ) : scalarCharacteristic ν s =
      Complex.exp (Complex.ofReal (-(1 / 2 : ℝ) * (v : ℝ) * s ^ 2)) := by
    have hiter (n : ℕ) : scalarCharacteristic ν s =
        scalarCharacteristic ν (c ^ n * s) *
          Complex.exp (Complex.ofReal (-(1 / 2 : ℝ) * (v : ℝ) * (1 - (c ^ n) ^ 2) * s ^ 2)) := by
      induction n with
      | zero => simp
      | succ n ih =>
        have hr := hrec (c ^ n * s)
        have heq : c * (c ^ n * s) = c ^ (n + 1) * s := by rw [pow_succ]; ring
        rw [heq] at hr
        rw [ih, hr, mul_assoc, ← Complex.exp_add]
        congr 2
        rw [pow_succ]
        push_cast
        ring
    have hpow : Tendsto (fun n : ℕ => c ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_iff.mpr hc
    have hp := scalarCharacteristic_scale_tendsto_one ν _ hpow s
    have hex : Tendsto (fun n : ℕ =>
        Complex.exp (Complex.ofReal (-(1 / 2 : ℝ) * (v : ℝ) * (1 - (c ^ n) ^ 2) * s ^ 2))) atTop
        (𝓝 (Complex.exp (Complex.ofReal (-(1 / 2 : ℝ) * (v : ℝ) * s ^ 2)))) := by
      have hb : Tendsto (fun n : ℕ => (1 : ℝ) - (c ^ n) ^ 2) atTop (𝓝 1) := by
        simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
          (hpow.pow 2)
      have hr := (hb.const_mul (-(1 / 2 : ℝ) * (v : ℝ))).mul_const (s ^ 2)
      simpa only [Function.comp_def, mul_one] using
        Complex.continuous_exp.continuousAt.tendsto.comp
          ((Complex.continuous_ofReal.continuousAt.tendsto).comp hr)
    have hh := hp.mul hex
    have heq : (fun n : ℕ => scalarCharacteristic ν (c ^ n * s) *
        Complex.exp (Complex.ofReal (-(1 / 2 : ℝ) * (v : ℝ) * (1 - (c ^ n) ^ 2) * s ^ 2))) =
        (fun _ : ℕ => scalarCharacteristic ν s) := funext (fun n => (hiter n).symm)
    rw [heq] at hh
    simpa only [one_mul] using tendsto_nhds_unique tendsto_const_nhds hh
  apply Measure.ext_of_charFun
  funext s
  rw [← scalarCharacteristic_eq_charFun, hchar, charFun_gaussianReal]
  congr 1
  push_cast
  ring

lemma continuous_starRootForm (d : ℕ) : Continuous (@starRootForm d) := by
  unfold starRootForm
  fun_prop

/-- Root and its i-th independent transverse coordinate. -/
def starRootSimplexPair {d : ℕ} (i : Fin d) (x : Fin d → ℝ) : ℝ × ℝ :=
  (starRootForm x, finiteLinearForm (starSimplexDirection d i) x)

lemma measurable_starRootSimplexPair {d : ℕ} (i : Fin d) :
    Measurable (starRootSimplexPair i) :=
  (continuous_starRootForm d).measurable.prodMk
    (continuous_finiteLinearForm _).measurable

/-- Recover the actual root from the two orthonormal edge observations. -/
lemma starRootForm_from_edge {d : ℕ} (c : ℝ) (hc : |c| < 1)
    (i : Fin d) (x : Fin d → ℝ) :
    alpha c * (starEdgeProjection d c i).mulVec x false +
      beta c * (starEdgeProjection d c i).mulVec x true = starRootForm x := by
  rw [starEdgeProjection_apply_false, starEdgeProjection_apply_true]
  simp only [scoreA, scoreB, smul_eq_mul]
  calc
    _ = (alpha c ^ 2 + beta c ^ 2) * starRootForm x := by ring
    _ = _ := by rw [alpha_sq_add_beta_sq c hc, one_mul]

/-- After endpoint reversal the recovered root becomes its contracting
root-plus-transverse-noise combination. -/
lemma starRootForm_from_reversed_edge {d : ℕ} (c : ℝ) (hc : |c| < 1)
    (i : Fin d) (x : Fin d → ℝ) :
    beta c * (starEdgeProjection d c i).mulVec x false +
      alpha c * (starEdgeProjection d c i).mulVec x true =
        c * starRootForm x + rho c * finiteLinearForm (starSimplexDirection d i) x := by
  rw [starEdgeProjection_apply_false, starEdgeProjection_apply_true]
  have hq : finiteLinearForm (starSimplexDirection d i) x =
      transverseScale d * starCenteredCoordinate x i := starSimplexDirection_apply x i
  rw [hq]
  simp only [scoreA, scoreB, smul_eq_mul]
  calc
    _ = (2 * alpha c * beta c) * starRootForm x +
        (alpha c ^ 2 - beta c ^ 2) * (transverseScale d * starCenteredCoordinate x i) := by ring
    _ = _ := by rw [two_alpha_mul_beta c hc, alpha_sq_sub_beta_sq c hc]

/-- Genuine independent root/transverse noise and actual edge reversal imply
stationarity of the actual scalar root law under the Gaussian OU step. -/
theorem star_root_stationary_of_pair_and_reversal
    {d : ℕ} (P : Measure (Fin d → ℝ)) [IsProbabilityMeasure P]
    (c : ℝ) (hc : |c| < 1) (i : Fin d) (v : ℝ≥0)
    (hpair : Measure.map (starRootSimplexPair i) P =
      (Measure.map starRootForm P).prod (gaussianReal 0 v))
    (hrev : Measure.map binarySwap
      (Measure.map (fun x => (starEdgeProjection d c i).mulVec x) P) =
        Measure.map (fun x => (starEdgeProjection d c i).mulVec x) P) :
    scalarOULaw (Measure.map starRootForm P) v c = Measure.map starRootForm P := by
  let O := starEdgeProjection d c i
  let R : (Bool → ℝ) → ℝ := fun z => alpha c * z false + beta c * z true
  have hR : Measurable R := by fun_prop
  have hO : Measurable (fun x => O.mulVec x) := measurable_finiteMatrixAction O
  have hcompose : (fun z : ℝ × ℝ => c * z.1 + rho c * z.2) ∘ starRootSimplexPair i =
      R ∘ binarySwap ∘ (fun x => O.mulVec x) := by
    funext x
    simp only [Function.comp_apply, R, binarySwap, coordinatePermutation_apply,
      Equiv.swap_apply_left, Equiv.swap_apply_right]
    exact (starRootForm_from_reversed_edge c hc i x).symm.trans (by ring)
  calc
    _ = Measure.map (fun z : ℝ × ℝ => c * z.1 + rho c * z.2)
        (Measure.map (starRootSimplexPair i) P) := by rw [hpair]; rfl
    _ = Measure.map (R ∘ binarySwap ∘ (fun x => O.mulVec x)) P := by
      rw [Measure.map_map (measurable_scalarOUMap c) (measurable_starRootSimplexPair i), hcompose]
    _ = Measure.map R (Measure.map binarySwap (Measure.map (fun x => O.mulVec x) P)) := by
      rw [Measure.map_map binarySwap.continuous.measurable hO,
        Measure.map_map hR (binarySwap.continuous.measurable.comp hO)]
    _ = Measure.map R (Measure.map (fun x => O.mulVec x) P) := by rw [hrev]
    _ = _ := by
      rw [Measure.map_map hR hO]
      congr 1
      funext x
      exact starRootForm_from_edge c hc i x

/-- The actual scalar root is Gaussian once its independent transverse pair
and the endpoint reversal have been established. -/
theorem star_root_gaussian_of_pair_and_reversal
    {d : ℕ} (P : Measure (Fin d → ℝ)) [IsProbabilityMeasure P]
    (c : ℝ) (hc : |c| < 1) (i : Fin d) (v : ℝ≥0)
    (hpair : Measure.map (starRootSimplexPair i) P =
      (Measure.map starRootForm P).prod (gaussianReal 0 v))
    (hrev : Measure.map binarySwap
      (Measure.map (fun x => (starEdgeProjection d c i).mulVec x) P) =
        Measure.map (fun x => (starEdgeProjection d c i).mulVec x) P) :
    Measure.map starRootForm P = gaussianReal 0 v := by
  letI : IsProbabilityMeasure (Measure.map (@starRootForm d) P) :=
    isProbabilityMeasure_map (continuous_starRootForm d).measurable.aemeasurable
  exact eq_gaussianReal_of_scalarOU_stationary _ v c hc
    (star_root_stationary_of_pair_and_reversal P c hc i v hpair hrev)


private def pairToBool (z : ℝ × ℝ) : Bool → ℝ := fun b => if b then z.2 else z.1
private def boolToPair (z : Bool → ℝ) : ℝ × ℝ := (z false, z true)
private lemma measurable_pairToBool : Measurable pairToBool := by
  apply measurable_pi_lambda
  intro b
  cases b
  · exact measurable_fst
  · exact measurable_snd
private lemma measurable_boolToPair : Measurable boolToPair :=
  (measurable_pi_apply false).prodMk (measurable_pi_apply true)

/-- Characteristic uniqueness for ordinary pairs, obtained by using literal
Bool coordinates rather than changing the norm on the product space. -/
theorem measure_eq_of_pair_characteristic (Q R : Measure (ℝ × ℝ))
    [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
    (h : ∀ a b : ℝ,
      (∫ z : ℝ × ℝ, Complex.exp ((↑(a * z.1 + b * z.2) : ℂ) * Complex.I) ∂ Q) =
        (∫ z : ℝ × ℝ, Complex.exp ((↑(a * z.1 + b * z.2) : ℂ) * Complex.I) ∂ R)) : Q = R := by
  letI : IsProbabilityMeasure (Measure.map pairToBool Q) :=
    isProbabilityMeasure_map measurable_pairToBool.aemeasurable
  letI : IsProbabilityMeasure (Measure.map pairToBool R) :=
    isProbabilityMeasure_map measurable_pairToBool.aemeasurable
  have hm : Measure.map pairToBool Q = Measure.map pairToBool R := by
    apply measure_eq_of_linear_characteristic
    intro t
    change (∫ x, (linearCharacteristic t) x ∂Measure.map pairToBool Q) =
      ∫ x, (linearCharacteristic t) x ∂Measure.map pairToBool R
    rw [integral_map measurable_pairToBool.aemeasurable
        (linearCharacteristic t).continuous.measurable.aestronglyMeasurable,
      integral_map measurable_pairToBool.aemeasurable
        (linearCharacteristic t).continuous.measurable.aestronglyMeasurable]
    simpa only [linearCharacteristic, finiteLinearForm, Fintype.sum_bool, pairToBool,
      Bool.false_eq_true, ↓reduceIte, add_comm] using h (t false) (t true)
  have hi := congrArg (Measure.map boolToPair) hm
  rw [Measure.map_map measurable_boolToPair measurable_pairToBool,
    Measure.map_map measurable_boolToPair measurable_pairToBool] at hi
  change Measure.map id Q = Measure.map id R at hi
  simpa only [Measure.map_id] using hi

lemma finiteLinearForm_root_transverse {d : ℕ} (a s : ℝ) (w x : Fin d → ℝ) :
    finiteLinearForm (a • starRootDirection d + s • w) x =
      a * starRootForm x + s * finiteLinearForm w x := by
  simp only [finiteLinearForm, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum,
    starRootDirection_apply]

/-- A root/transverse characteristic factorization is upgraded to equality
with the actual product measure. -/
theorem root_transverse_pair_eq_prod_of_characteristic {d : ℕ}
    (P : Measure (Fin d → ℝ)) [IsProbabilityMeasure P] (w : Fin d → ℝ) (v : ℝ≥0)
    (hfactor : ∀ a s : ℝ,
      characteristicIntegral P (a • starRootDirection d + s • w) =
        scalarCharacteristic (Measure.map starRootForm P) a *
          Complex.exp (Complex.ofReal (-(1 / 2 : ℝ) * (v : ℝ) * s ^ 2))) :
    Measure.map (fun x => (starRootForm x, finiteLinearForm w x)) P =
      (Measure.map starRootForm P).prod (gaussianReal 0 v) := by
  have hp : Measurable (fun x : Fin d → ℝ => (starRootForm x, finiteLinearForm w x)) :=
    (continuous_starRootForm d).measurable.prodMk (continuous_finiteLinearForm w).measurable
  letI : IsProbabilityMeasure (Measure.map (fun x => (starRootForm x, finiteLinearForm w x)) P) :=
    isProbabilityMeasure_map hp.aemeasurable
  letI : IsProbabilityMeasure (Measure.map (@starRootForm d) P) :=
    isProbabilityMeasure_map (continuous_starRootForm d).measurable.aemeasurable
  apply measure_eq_of_pair_characteristic
  intro a s
  rw [integral_map hp.aemeasurable
    (by exact (show Continuous (fun z : ℝ × ℝ =>
      Complex.exp ((↑(a * z.1 + s * z.2) : ℂ) * Complex.I)) by fun_prop).measurable.aestronglyMeasurable)]
  have hleft : (∫ x, Complex.exp ((↑(a * starRootForm x + s * finiteLinearForm w x) : ℂ) *
      Complex.I) ∂P) = characteristicIntegral P (a • starRootDirection d + s • w) := by
    simp only [characteristicIntegral, finiteLinearForm_root_transverse]
  rw [hleft, hfactor]
  have heq (z : ℝ × ℝ) :
      Complex.exp ((↑(a * z.1 + s * z.2) : ℂ) * Complex.I) =
        Complex.exp ((↑(a * z.1) : ℂ) * Complex.I) *
          Complex.exp ((↑(s * z.2) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [heq]
  rw [integral_prod_mul
    (fun r : ℝ => Complex.exp ((↑(a * r) : ℂ) * Complex.I))
    (fun z : ℝ => Complex.exp ((↑(s * z) : ℂ) * Complex.I)),
    centeredGaussian_characteristic_integral]
  rfl

/-- Every coefficient vector splits into its root coordinate and a scalar
multiple of an actual centered unit transverse vector. The zero transverse
case is handled explicitly by selecting one simplex unit direction. -/
theorem exists_unit_transverse_decomposition (d : ℕ) (hd : 2 ≤ d) (t : Fin d → ℝ) :
    ∃ (w : Fin d → ℝ) (s : ℝ), (∑ j, w j = 0) ∧ squareRadius w = 1 ∧
      t = starRootForm t • starRootDirection d + s • w ∧
      starRootForm t ^ 2 + s ^ 2 = squareRadius t := by
  have hdpos : 0 < d := by omega
  let q := starTransversePart d t
  have hqsum : ∑ j, q j = 0 := sum_starTransversePart hdpos t
  have hdecomp : t = starRootForm t • starRootDirection d + q := by
    rw [← starRootPart_eq_rootForm_smul hdpos]
    exact (starRootPart_add_transversePart d t).symm
  have henergy : starRootForm t ^ 2 + squareRadius q = squareRadius t :=
    starRoot_centered_energy hdpos t
  by_cases hzero : squareRadius q = 0
  · let i₀ : Fin d := ⟨0, hdpos⟩
    have hqzero : q = 0 := by
      ext j
      have hj : q j ^ 2 ≤ squareRadius q :=
        Finset.single_le_sum (fun l _ => sq_nonneg (q l)) (Finset.mem_univ j)
      change q j = 0
      nlinarith [sq_nonneg (q j)]
    refine ⟨starSimplexDirection d i₀, 0, sum_starSimplexDirection d hdpos i₀,
      starSimplexDirection_norm_sq d hd i₀, ?_, ?_⟩
    · simpa [hqzero] using hdecomp
    · simpa [hzero] using henergy
  · let s := Real.sqrt (squareRadius q)
    have hs : 0 < s := Real.sqrt_pos.mpr
      (lt_of_le_of_ne (squareRadius_nonneg q) (Ne.symm hzero))
    have hs2 : s ^ 2 = squareRadius q := Real.sq_sqrt (squareRadius_nonneg q)
    let w : Fin d → ℝ := fun j => q j / s
    have hw : ∑ j, w j = 0 := by simp [w, ← Finset.sum_div, hqsum]
    have hwnorm : squareRadius w = 1 := by
      simp only [squareRadius, w, div_pow, ← Finset.sum_div]
      change squareRadius q / s ^ 2 = 1
      rw [hs2, div_self hzero]
    have hsw : s • w = q := by
      ext j
      change s * (q j / s) = q j
      field_simp
    refine ⟨w, s, hw, hwnorm, ?_, ?_⟩
    · rw [hsw]
      exact hdecomp
    · rw [hs2]
      exact henergy

/-- The full ambient law is Gaussian once the root is Gaussian and every
actual unit transverse direction factors from it. This uses arbitrary
coefficient vectors, rather than only finitely many simplex marginals. -/
theorem eq_heatGaussian_of_root_and_transverse_characteristics
    (d : ℕ) (hd : 2 ≤ d) (P : Measure (Fin d → ℝ)) [IsProbabilityMeasure P] (v : ℝ≥0)
    (hroot : Measure.map starRootForm P = gaussianReal 0 v)
    (hfactor : ∀ w : Fin d → ℝ, (∑ j, w j = 0) → squareRadius w = 1 → ∀ a s : ℝ,
      characteristicIntegral P (a • starRootDirection d + s • w) =
        scalarCharacteristic (Measure.map starRootForm P) a *
          Complex.exp (Complex.ofReal (-(1 / 2 : ℝ) * (v : ℝ) * s ^ 2))) :
    P = heatGaussian (Fin d) ((v : ℝ) / 2) := by
  apply measure_eq_of_linear_characteristic
  intro t
  change characteristicIntegral P t = characteristicIntegral (heatGaussian (Fin d) ((v : ℝ) / 2)) t
  obtain ⟨w, s, hwsum, hwnorm, ht, henergy⟩ := exists_unit_transverse_decomposition d hd t
  rw [ht, hfactor w hwsum hwnorm, hroot, scalarCharacteristic,
    centeredGaussian_characteristic_integral]
  rw [← Complex.exp_add, heatGaussian_characteristic]
  have hv : (heatVariance ((v : ℝ) / 2) : ℝ) = v := by
    change max (2 * ((v : ℝ) / 2)) 0 = v
    rw [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0), max_eq_left v.coe_nonneg]
  rw [hv]
  have hmass : squareMass (starRootForm t • starRootDirection d + s • w) = squareRadius t := by
    rw [← ht]
    rfl
  rw [hmass]
  congr 1
  rw [← henergy]
  push_cast
  ring


/-- Actual full Gaussian reconstruction from the all-transverse characteristic
factorization and one reversed edge. Both the product pair and the Gaussian
root law are proved inside this theorem. -/
theorem star_gaussian_of_transverse_characteristics_and_reversal
    (d : ℕ) (hd : 2 ≤ d) (P : Measure (Fin d → ℝ)) [IsProbabilityMeasure P]
    (v : ℝ≥0) (c : ℝ) (hc : |c| < 1) (i₀ : Fin d)
    (hfactor : ∀ w : Fin d → ℝ, (∑ j, w j = 0) → squareRadius w = 1 → ∀ a s : ℝ,
      characteristicIntegral P (a • starRootDirection d + s • w) =
        scalarCharacteristic (Measure.map starRootForm P) a *
          Complex.exp (Complex.ofReal (-(1 / 2 : ℝ) * (v : ℝ) * s ^ 2)))
    (hrev : Measure.map binarySwap
      (Measure.map (fun x => (starEdgeProjection d c i₀).mulVec x) P) =
        Measure.map (fun x => (starEdgeProjection d c i₀).mulVec x) P) :
    P = heatGaussian (Fin d) ((v : ℝ) / 2) := by
  have hpair : Measure.map (starRootSimplexPair i₀) P =
      (Measure.map starRootForm P).prod (gaussianReal 0 v) :=
    root_transverse_pair_eq_prod_of_characteristic P (starSimplexDirection d i₀) v
      (hfactor _ (sum_starSimplexDirection d (by omega) i₀)
        (starSimplexDirection_norm_sq d hd i₀))
  have hroot := star_root_gaussian_of_pair_and_reversal P c hc i₀ v hpair hrev
  exact eq_heatGaussian_of_root_and_transverse_characteristics d hd P v hroot hfactor

/-- Original-edge reversal supplies actual reversal of the heated edge law. -/
theorem star_heated_edge_reversal {d : ℕ} (hd : 2 ≤ d)
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : |c| < 1) (i : Fin d)
    (hrev : Measure.map binarySwap
      (Measure.map (fun x => (starEdgeProjection d c i).mulVec x) μ) =
        Measure.map (fun x => (starEdgeProjection d c i).mulVec x) μ) (t : ℝ) :
    Measure.map binarySwap
      (Measure.map (fun x => (starEdgeProjection d c i).mulVec x) (heatedLaw μ t)) =
        Measure.map (fun x => (starEdgeProjection d c i).mulVec x) (heatedLaw μ t) := by
  let O := starEdgeProjection d c i
  let ν := Measure.map (fun x => O.mulVec x) μ
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_map
    (measurable_finiteMatrixAction O).aemeasurable
  have h := heatedLaw_binarySwap_invariant ν hrev t
  rw [← heatedLaw_map_orthonormal_rows μ O (starEdgeProjection_mul_transpose d hd c hc i) t] at h
  exact h

/-- The complete root-stationarity and characteristic reconstruction step for
an actual heated law. Only the derived transverse factorization and the
original edge-reversal law enter this intermediate analytic component. -/
theorem star_heated_gaussian_of_transverse_characteristics_and_reversal
    (d : ℕ) (hd : 2 ≤ d) (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (t : ℝ) (v : ℝ≥0) (c : ℝ) (hc : |c| < 1) (i₀ : Fin d)
    (hfactor : ∀ w : Fin d → ℝ, (∑ j, w j = 0) → squareRadius w = 1 → ∀ a s : ℝ,
      characteristicIntegral (heatedLaw μ t) (a • starRootDirection d + s • w) =
        scalarCharacteristic (Measure.map starRootForm (heatedLaw μ t)) a *
          Complex.exp (Complex.ofReal (-(1 / 2 : ℝ) * (v : ℝ) * s ^ 2)))
    (hrev : Measure.map binarySwap
      (Measure.map (fun x => (starEdgeProjection d c i₀).mulVec x) μ) =
        Measure.map (fun x => (starEdgeProjection d c i₀).mulVec x) μ) :
    heatedLaw μ t = heatGaussian (Fin d) ((v : ℝ) / 2) :=
  star_gaussian_of_transverse_characteristics_and_reversal d hd (heatedLaw μ t) v c hc i₀ hfactor
    (star_heated_edge_reversal hd μ c hc i₀ hrev t)


/-- Convert the root-only ambient characteristic coefficient to the ordinary
scalar root marginal, for the Stein-factorization interface. -/
lemma characteristicIntegral_root_eq_scalarCharacteristic {d : ℕ}
    (P : Measure (Fin d → ℝ)) (a : ℝ) :
    characteristicIntegral P (a • starRootDirection d) =
      scalarCharacteristic (Measure.map starRootForm P) a := by
  rw [scalarCharacteristic, integral_map (continuous_starRootForm d).measurable.aemeasurable
    (continuous_scalarCharacteristicIntegrand a).measurable.aestronglyMeasurable]
  simp only [characteristicIntegral, finiteLinearForm, Pi.smul_apply, smul_eq_mul,
    mul_assoc, ← Finset.mul_sum, starRootDirection_apply]

end GaussianWave.BS
