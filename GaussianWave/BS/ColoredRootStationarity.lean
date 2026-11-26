import GaussianWave.BS.RootStationarity
import GaussianWave.BS.ColoredGeometry
import GaussianWave.BS.ColoredFisherMonotonicity

/-!
# Genuine multichannel root OU stationarity and full Gaussian reconstruction

The root is the whole channel vector. Pair laws and independence are equalities
of actual product measures; all characteristic directions in the channel and
transverse spaces are used. No rank-one channel test is substituted for the
full joint law.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators NNReal
namespace GaussianWave.BS

/-- Isotropic covariance in an actual finite channel coordinate space. -/
def isotropicCovariance (J : Type*) [Fintype J] [DecidableEq J] (v : ℝ≥0) : Matrix J J ℝ :=
  Matrix.diagonal (fun _ => (v : ℝ))

lemma isotropicCovariance_posSemidef (J : Type*) [Fintype J] [DecidableEq J] (v : ℝ≥0) :
    (isotropicCovariance J v).PosSemidef :=
  Matrix.posSemidef_diagonal_iff.mpr (fun _ => v.coe_nonneg)

lemma finiteCovarianceQuadratic_isotropic {J : Type*} [Fintype J] [DecidableEq J]
    (v : ℝ≥0) (a : J → ℝ) :
    finiteCovarianceQuadratic (isotropicCovariance J v) a = (v : ℝ) * squareMass a := by
  simp [finiteCovarianceQuadratic, isotropicCovariance, Matrix.diagonal_apply,
    squareMass, pow_two, Finset.mul_sum, mul_assoc, mul_left_comm]

lemma coe_heatVariance_half_nnreal (v : ℝ≥0) :
    (heatVariance ((v : ℝ) / 2) : ℝ) = v := by
  change max (2 * ((v : ℝ) / 2)) 0 = v
  rw [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0), max_eq_left v.coe_nonneg]

/-- The constructed Gaussian covariance law equals the actual finite product
of real normals represented by heatGaussian. -/
theorem gaussianCovarianceLaw_isotropic_eq_heatGaussian
    (J : Type*) [Fintype J] [DecidableEq J] (v : ℝ≥0) :
    gaussianCovarianceLaw (isotropicCovariance J v) (isotropicCovariance_posSemidef J v) =
      heatGaussian J ((v : ℝ) / 2) := by
  apply measure_eq_of_linear_characteristic
  intro a
  change characteristicIntegral (gaussianCovarianceLaw (isotropicCovariance J v)
    (isotropicCovariance_posSemidef J v)) a = characteristicIntegral (heatGaussian J ((v : ℝ) / 2)) a
  have hg := gaussianCovarianceLaw_characteristic (isotropicCovariance J v)
    (isotropicCovariance_posSemidef J v) a
  change characteristicIntegral _ a = _ at hg
  rw [hg, finiteCovarianceQuadratic_isotropic]
  rw [heatGaussian_characteristic, coe_heatVariance_half_nnreal]
  congr 1
  push_cast
  ring

/-- Actual vector OU step with independent isotropic Gaussian noise. -/
def vectorHeatOULaw {J : Type*} [Fintype J]
    (ν : Measure (J → ℝ)) (v : ℝ≥0) (c : ℝ) : Measure (J → ℝ) :=
  Measure.map (affineGaussianMap c (rho c)) (ν.prod (heatGaussian J ((v : ℝ) / 2)))

/-- Genuine vector-root uniqueness, reusing the proved finite-channel OU
stationary uniqueness with covariance vI. -/
theorem eq_heatGaussian_of_vectorHeatOU_stationary
    {J : Type*} [Fintype J] [DecidableEq J]
    (ν : Measure (J → ℝ)) [IsProbabilityMeasure ν] (v : ℝ≥0) (c : ℝ) (hc : |c| < 1)
    (hstationary : vectorHeatOULaw ν v c = ν) : ν = heatGaussian J ((v : ℝ) / 2) := by
  have hOU : ouLaw ν (isotropicCovariance J v) (isotropicCovariance_posSemidef J v) c = ν := by
    rw [ouLaw, affineGaussianLaw, gaussianCovarianceLaw_isotropic_eq_heatGaussian]
    exact hstationary
  exact (eq_gaussian_of_ou_stationary ν _ (isotropicCovariance_posSemidef J v) c hc hOU).trans
    (gaussianCovarianceLaw_isotropic_eq_heatGaussian J v)

/-- Lift a channel coefficient vector into the i-th simplex directions. -/
def coloredSimplexLift (d r : ℕ) (i : Fin d) (b : Fin r → ℝ) : (Fin r × Fin d) → ℝ :=
  fun p => b p.1 * starSimplexDirection d i p.2

/-- Simultaneous transverse simplex observations in every channel. -/
def coloredSimplexForm (d r : ℕ) (i : Fin d) (x : (Fin r × Fin d) → ℝ) : Fin r → ℝ :=
  fun a => finiteLinearForm (starSimplexDirection d i) (fun j => x (a, j))

lemma continuous_coloredStarRootForm (d r : ℕ) : Continuous (coloredStarRootForm d r) :=
  (coloredStarRootForm d r).continuous_of_finiteDimensional

lemma continuous_coloredSimplexForm (d r : ℕ) (i : Fin d) :
    Continuous (coloredSimplexForm d r i) := by
  apply continuous_pi
  intro a
  exact (continuous_finiteLinearForm _).comp (continuous_pi (fun j => continuous_apply (a, j)))

lemma finiteLinearForm_coloredRootLift (d r : ℕ) (a : Fin r → ℝ)
    (x : (Fin r × Fin d) → ℝ) :
    finiteLinearForm (coloredRootLift d r a) x = finiteLinearForm a (coloredStarRootForm d r x) := by
  simp only [finiteLinearForm, Fintype.sum_prod_type, coloredRootLift_apply,
    coloredStarRootForm_apply, mul_assoc, ← Finset.mul_sum, starRootDirection_apply]

lemma finiteLinearForm_coloredSimplexLift (d r : ℕ) (i : Fin d) (b : Fin r → ℝ)
    (x : (Fin r × Fin d) → ℝ) :
    finiteLinearForm (coloredSimplexLift d r i b) x = finiteLinearForm b (coloredSimplexForm d r i x) := by
  simp only [finiteLinearForm, Fintype.sum_prod_type, coloredSimplexLift, coloredSimplexForm,
    mul_assoc, Finset.mul_sum]

lemma coloredSimplexLift_sum (d r : ℕ) (hd : 0 < d) (i : Fin d) (b : Fin r → ℝ) (a : Fin r) :
    (∑ j, coloredSimplexLift d r i b (a, j)) = 0 := by
  simp only [coloredSimplexLift, ← Finset.mul_sum, sum_starSimplexDirection d hd i, mul_zero]

lemma coloredSimplexLift_squareRadius (d r : ℕ) (hd : 2 ≤ d) (i : Fin d) (b : Fin r → ℝ) :
    squareRadius (coloredSimplexLift d r i b) = squareRadius b := by
  simp only [squareRadius, coloredSimplexLift, Fintype.sum_prod_type, mul_pow,
    ← Finset.mul_sum, starSimplexDirection_norm_sq d hd i, mul_one]

/-- Actual root and simplex vector observed simultaneously. -/
def coloredRootSimplexPair (d r : ℕ) (i : Fin d) (x : (Fin r × Fin d) → ℝ) :
    (Fin r → ℝ) × (Fin r → ℝ) :=
  (coloredStarRootForm d r x, coloredSimplexForm d r i x)

lemma measurable_coloredRootSimplexPair (d r : ℕ) (i : Fin d) :
    Measurable (coloredRootSimplexPair d r i) :=
  (continuous_coloredStarRootForm d r).measurable.prodMk
    (continuous_coloredSimplexForm d r i).measurable

lemma coloredRootForm_from_edge (d r : ℕ) (c : ℝ) (hc : |c| < 1)
    (i : Fin d) (x : (Fin r × Fin d) → ℝ) :
    (fun a => alpha c * (coloredStarEdgeProjection d r c i).mulVec x (false, a) +
      beta c * (coloredStarEdgeProjection d r c i).mulVec x (true, a)) = coloredStarRootForm d r x := by
  funext a
  simpa only [coloredStarEdgeProjection_mulVec, coloredStarRootForm_apply] using
    starRootForm_from_edge c hc i (fun j => x (a, j))

lemma coloredRootForm_from_reversed_edge (d r : ℕ) (c : ℝ) (hc : |c| < 1)
    (i : Fin d) (x : (Fin r × Fin d) → ℝ) :
    (fun a => beta c * (coloredStarEdgeProjection d r c i).mulVec x (false, a) +
      alpha c * (coloredStarEdgeProjection d r c i).mulVec x (true, a)) =
        affineGaussianMap c (rho c) (coloredRootSimplexPair d r i x) := by
  funext a
  simpa only [coloredStarEdgeProjection_mulVec, affineGaussianMap, coloredRootSimplexPair,
    coloredStarRootForm_apply, coloredSimplexForm] using
      starRootForm_from_reversed_edge c hc i (fun j => x (a, j))

/-- Simultaneous whole-edge reversal gives actual vector OU stationarity
once the actual root/simplex-vector pair is known to be an independent product. -/
theorem colored_root_stationary_of_pair_and_reversal
    (d r : ℕ) (P : Measure ((Fin r × Fin d) → ℝ)) [IsProbabilityMeasure P]
    (c : ℝ) (hc : |c| < 1) (i : Fin d) (v : ℝ≥0)
    (hpair : Measure.map (coloredRootSimplexPair d r i) P =
      (Measure.map (coloredStarRootForm d r) P).prod (heatGaussian (Fin r) ((v : ℝ) / 2)))
    (hrev : Measure.map (edgeFlipLinear r)
      (Measure.map (fun x => (coloredStarEdgeProjection d r c i).mulVec x) P) =
        Measure.map (fun x => (coloredStarEdgeProjection d r c i).mulVec x) P) :
    vectorHeatOULaw (Measure.map (coloredStarRootForm d r) P) v c =
      Measure.map (coloredStarRootForm d r) P := by
  let O := coloredStarEdgeProjection d r c i
  let R : ((Bool × Fin r) → ℝ) → (Fin r → ℝ) := fun z a =>
    alpha c * z (false, a) + beta c * z (true, a)
  have hR : Measurable R := by fun_prop
  have hO : Measurable (fun x => O.mulVec x) := measurable_finiteMatrixAction O
  have hcompose : affineGaussianMap c (rho c) ∘ coloredRootSimplexPair d r i =
      R ∘ edgeFlipLinear r ∘ (fun x => O.mulVec x) := by
    funext x a
    have h := congrFun (coloredRootForm_from_reversed_edge d r c hc i x) a
    change affineGaussianMap c (rho c) (coloredRootSimplexPair d r i x) a =
      alpha c * O.mulVec x (true, a) + beta c * O.mulVec x (false, a)
    exact h.symm.trans (by dsimp [O]; ring)
  calc
    _ = Measure.map (affineGaussianMap c (rho c)) (Measure.map (coloredRootSimplexPair d r i) P) := by
      rw [hpair]
      rfl
    _ = Measure.map (R ∘ edgeFlipLinear r ∘ (fun x => O.mulVec x)) P := by
      rw [Measure.map_map (measurable_affineGaussianMap c (rho c))
        (measurable_coloredRootSimplexPair d r i), hcompose]
    _ = Measure.map R (Measure.map (edgeFlipLinear r) (Measure.map (fun x => O.mulVec x) P)) := by
      rw [Measure.map_map (edgeFlipLinear r).continuous.measurable hO,
        Measure.map_map hR ((edgeFlipLinear r).continuous.measurable.comp hO)]
    _ = Measure.map R (Measure.map (fun x => O.mulVec x) P) := by rw [hrev]
    _ = _ := by
      rw [Measure.map_map hR hO]
      congr 1
      funext x
      exact coloredRootForm_from_edge d r c hc i x

/-- Genuine joint Gaussianity of the entire root channel vector. -/
theorem colored_root_gaussian_of_pair_and_reversal
    (d r : ℕ) (P : Measure ((Fin r × Fin d) → ℝ)) [IsProbabilityMeasure P]
    (c : ℝ) (hc : |c| < 1) (i : Fin d) (v : ℝ≥0)
    (hpair : Measure.map (coloredRootSimplexPair d r i) P =
      (Measure.map (coloredStarRootForm d r) P).prod (heatGaussian (Fin r) ((v : ℝ) / 2)))
    (hrev : Measure.map (edgeFlipLinear r)
      (Measure.map (fun x => (coloredStarEdgeProjection d r c i).mulVec x) P) =
        Measure.map (fun x => (coloredStarEdgeProjection d r c i).mulVec x) P) :
    Measure.map (coloredStarRootForm d r) P = heatGaussian (Fin r) ((v : ℝ) / 2) := by
  letI : IsProbabilityMeasure (Measure.map (coloredStarRootForm d r) P) :=
    isProbabilityMeasure_map (continuous_coloredStarRootForm d r).measurable.aemeasurable
  exact eq_heatGaussian_of_vectorHeatOU_stationary _ v c hc
    (colored_root_stationary_of_pair_and_reversal d r P c hc i v hpair hrev)


lemma colored_root_transverse_decomposition (d r : ℕ) (hd : 0 < d) (x : ColoredSpace d r) :
    x = coloredRootLift d r (coloredStarRootForm d r x) + coloredTransversePart d r x := by
  calc
    x = coloredRootPart d r x + coloredTransversePart d r x :=
      (coloredRootPart_add_transversePart d r x).symm
    _ = _ := by
      congr 1
      ext ⟨a, j⟩
      exact congrFun (starRootPart_eq_rootForm_smul hd (fun k => x (a, k))) j

lemma colored_root_transverse_energy (d r : ℕ) (hd : 0 < d) (x : ColoredSpace d r) :
    squareRadius (coloredStarRootForm d r x) + squareRadius (coloredTransversePart d r x) =
      squareRadius x := by
  change (∑ a, starRootForm (fun j => x (a, j)) ^ 2) +
    (∑ p : Fin r × Fin d, coloredTransversePart d r x p ^ 2) = _
  rw [Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  calc
    _ = ∑ a, squareRadius (fun j => x (a, j)) := by
      apply Finset.sum_congr rfl
      intro a _
      simpa only [coloredTransversePart_apply, starTransversePart_apply, squareRadius] using
        starRoot_centered_energy hd (fun j => x (a, j))
    _ = _ := by simp only [squareRadius, Fintype.sum_prod_type]

/-- Every centered colored coefficient is a scalar multiple of a genuine
unit vector in the whole colored transverse space. -/
theorem exists_unit_colored_transverse_decomposition (d r : ℕ) (hd : 2 ≤ d) (hr : 0 < r)
    (q : ColoredSpace d r) (hq : ∀ a, ∑ j, q (a, j) = 0) :
    ∃ (w : ColoredSpace d r) (s : ℝ), (∀ a, ∑ j, w (a, j) = 0) ∧ squareRadius w = 1 ∧
      q = s • w ∧ s ^ 2 = squareRadius q := by
  by_cases hzero : squareRadius q = 0
  · let i₀ : Fin d := ⟨0, by omega⟩
    let a₀ : Fin r := ⟨0, hr⟩
    have hqzero : q = 0 := by
      ext p
      have hp : q p ^ 2 ≤ squareRadius q :=
        Finset.single_le_sum (fun l _ => sq_nonneg (q l)) (Finset.mem_univ p)
      change q p = 0
      nlinarith [sq_nonneg (q p)]
    refine ⟨coloredSimplexLift d r i₀ (starCoordinateVector a₀), 0,
      coloredSimplexLift_sum d r (by omega) i₀ _, ?_, ?_, ?_⟩
    · rw [coloredSimplexLift_squareRadius d r hd, squareRadius_starCoordinateVector]
    · simp [hqzero]
    · simp [hzero]
  · let s := Real.sqrt (squareRadius q)
    have hs : 0 < s := Real.sqrt_pos.mpr
      (lt_of_le_of_ne (squareRadius_nonneg q) (Ne.symm hzero))
    have hs2 : s ^ 2 = squareRadius q := Real.sq_sqrt (squareRadius_nonneg q)
    let w : ColoredSpace d r := fun p => q p / s
    have hw : ∀ a, ∑ j, w (a, j) = 0 := by intro a; simp [w, ← Finset.sum_div, hq a]
    have hwnorm : squareRadius w = 1 := by
      simp only [squareRadius, w, div_pow, ← Finset.sum_div]
      change squareRadius q / s ^ 2 = 1
      rw [hs2, div_self hzero]
    have hsw : q = s • w := by
      ext p
      change q p = s * (q p / s)
      field_simp
    exact ⟨w, s, hw, hwnorm, hsw, hs2⟩

/-- The all-unit transverse factorization extends to every colored
transverse coefficient, including the zero vector. -/
theorem colored_transverse_factorization_all
    (d r : ℕ) (hd : 2 ≤ d) (hr : 0 < r)
    (P : Measure (ColoredSpace d r)) (v : ℝ≥0)
    (hfactor : ∀ w : ColoredSpace d r, (∀ a, ∑ j, w (a, j) = 0) → squareRadius w = 1 →
      ∀ a : Fin r → ℝ, ∀ s : ℝ,
      characteristicIntegral P (coloredRootLift d r a + s • w) =
        characteristicIntegral (Measure.map (coloredStarRootForm d r) P) a *
          Complex.exp (Complex.ofReal (-(1 / 2 : ℝ) * (v : ℝ) * s ^ 2)))
    (q : ColoredSpace d r) (hq : ∀ a, ∑ j, q (a, j) = 0) (a : Fin r → ℝ) :
    characteristicIntegral P (coloredRootLift d r a + q) =
      characteristicIntegral (Measure.map (coloredStarRootForm d r) P) a *
        Complex.exp (Complex.ofReal (-(1 / 2 : ℝ) * (v : ℝ) * squareRadius q)) := by
  obtain ⟨w, s, hw, hunit, hqeq, hs2⟩ :=
    exists_unit_colored_transverse_decomposition d r hd hr q hq
  calc
    _ = characteristicIntegral P (coloredRootLift d r a + s • w) := by rw [← hqeq]
    _ = _ := by rw [hfactor w hw hunit, hs2]

private def vectorPairToCoordinates (r : ℕ) (z : (Fin r → ℝ) × (Fin r → ℝ)) :
    (Bool × Fin r) → ℝ := fun p => if p.1 then z.2 p.2 else z.1 p.2
private def coordinatesToVectorPair (r : ℕ) (z : (Bool × Fin r) → ℝ) :
    (Fin r → ℝ) × (Fin r → ℝ) := (fun a => z (false, a), fun a => z (true, a))
private lemma measurable_vectorPairToCoordinates (r : ℕ) : Measurable (vectorPairToCoordinates r) := by
  apply measurable_pi_lambda
  rintro ⟨b, a⟩
  cases b
  · exact (measurable_pi_apply a).comp measurable_fst
  · exact (measurable_pi_apply a).comp measurable_snd
private lemma measurable_coordinatesToVectorPair (r : ℕ) : Measurable (coordinatesToVectorPair r) := by
  apply Measurable.prodMk <;> apply measurable_pi_lambda <;> intro a <;> exact measurable_pi_apply _

/-- Genuine measure uniqueness for pairs of whole channel vectors. -/
theorem measure_eq_of_vectorPair_characteristic (r : ℕ)
    (Q R : Measure ((Fin r → ℝ) × (Fin r → ℝ)))
    [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
    (h : ∀ a b : Fin r → ℝ,
      (∫ z : (Fin r → ℝ) × (Fin r → ℝ), Complex.exp ((↑(finiteLinearForm a z.1 + finiteLinearForm b z.2) : ℂ) * Complex.I) ∂ Q) =
        (∫ z : (Fin r → ℝ) × (Fin r → ℝ), Complex.exp ((↑(finiteLinearForm a z.1 + finiteLinearForm b z.2) : ℂ) * Complex.I) ∂ R)) :
    Q = R := by
  letI : IsProbabilityMeasure (Measure.map (vectorPairToCoordinates r) Q) :=
    isProbabilityMeasure_map (measurable_vectorPairToCoordinates r).aemeasurable
  letI : IsProbabilityMeasure (Measure.map (vectorPairToCoordinates r) R) :=
    isProbabilityMeasure_map (measurable_vectorPairToCoordinates r).aemeasurable
  have hm : Measure.map (vectorPairToCoordinates r) Q = Measure.map (vectorPairToCoordinates r) R := by
    apply measure_eq_of_linear_characteristic
    intro t
    change (∫ x, (linearCharacteristic t) x ∂Measure.map (vectorPairToCoordinates r) Q) =
      ∫ x, (linearCharacteristic t) x ∂Measure.map (vectorPairToCoordinates r) R
    rw [integral_map (measurable_vectorPairToCoordinates r).aemeasurable
        (linearCharacteristic t).continuous.measurable.aestronglyMeasurable,
      integral_map (measurable_vectorPairToCoordinates r).aemeasurable
        (linearCharacteristic t).continuous.measurable.aestronglyMeasurable]
    simpa only [linearCharacteristic, finiteLinearForm, Fintype.sum_prod_type, Fintype.sum_bool,
      vectorPairToCoordinates, Bool.false_eq_true, ↓reduceIte, add_comm] using
      h (fun a => t (false, a)) (fun a => t (true, a))
  have hi := congrArg (Measure.map (coordinatesToVectorPair r)) hm
  rw [Measure.map_map (measurable_coordinatesToVectorPair r) (measurable_vectorPairToCoordinates r),
    Measure.map_map (measurable_coordinatesToVectorPair r) (measurable_vectorPairToCoordinates r)] at hi
  change Measure.map id Q = Measure.map id R at hi
  simpa only [Measure.map_id] using hi

/-- The actual root/simplex-vector pair factors as an independent product.
Arbitrary channel coefficient vectors are used in the uniqueness proof. -/
theorem colored_root_simplex_pair_eq_product_of_transverse_characteristics
    (d r : ℕ) (hd : 2 ≤ d) (hr : 0 < r)
    (P : Measure (ColoredSpace d r)) [IsProbabilityMeasure P] (v : ℝ≥0) (i : Fin d)
    (hfactor : ∀ w : ColoredSpace d r, (∀ a, ∑ j, w (a, j) = 0) → squareRadius w = 1 →
      ∀ a : Fin r → ℝ, ∀ s : ℝ,
      characteristicIntegral P (coloredRootLift d r a + s • w) =
        characteristicIntegral (Measure.map (coloredStarRootForm d r) P) a *
          Complex.exp (Complex.ofReal (-(1 / 2 : ℝ) * (v : ℝ) * s ^ 2))) :
    Measure.map (coloredRootSimplexPair d r i) P =
      (Measure.map (coloredStarRootForm d r) P).prod (heatGaussian (Fin r) ((v : ℝ) / 2)) := by
  let ν := Measure.map (coloredStarRootForm d r) P
  letI : IsProbabilityMeasure ν :=
    isProbabilityMeasure_map (continuous_coloredStarRootForm d r).measurable.aemeasurable
  letI : IsProbabilityMeasure (Measure.map (coloredRootSimplexPair d r i) P) :=
    isProbabilityMeasure_map (measurable_coloredRootSimplexPair d r i).aemeasurable
  apply measure_eq_of_vectorPair_characteristic r
  intro a b
  rw [integral_map (measurable_coloredRootSimplexPair d r i).aemeasurable
    (show Continuous (fun z : (Fin r → ℝ) × (Fin r → ℝ) =>
      Complex.exp ((↑(finiteLinearForm a z.1 + finiteLinearForm b z.2) : ℂ) * Complex.I)) from
      Complex.continuous_exp.comp (((Complex.continuous_ofReal.comp
        (((continuous_finiteLinearForm a).comp continuous_fst).add
          ((continuous_finiteLinearForm b).comp continuous_snd))).mul continuous_const))).measurable.aestronglyMeasurable]
  have hlin (x : ColoredSpace d r) :
      finiteLinearForm (coloredRootLift d r a + coloredSimplexLift d r i b) x =
        finiteLinearForm a (coloredStarRootForm d r x) + finiteLinearForm b (coloredSimplexForm d r i x) := by
    simp only [finiteLinearForm, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    rw [show (∑ k, coloredRootLift d r a k * x k) =
      finiteLinearForm (coloredRootLift d r a) x from rfl,
      show (∑ k, coloredSimplexLift d r i b k * x k) =
      finiteLinearForm (coloredSimplexLift d r i b) x from rfl,
      finiteLinearForm_coloredRootLift, finiteLinearForm_coloredSimplexLift]
    rfl
  have hleft : (∫ x, Complex.exp ((↑(finiteLinearForm a (coloredStarRootForm d r x) +
      finiteLinearForm b (coloredSimplexForm d r i x)) : ℂ) * Complex.I) ∂P) =
      characteristicIntegral P (coloredRootLift d r a + coloredSimplexLift d r i b) := by
    simp only [characteristicIntegral, hlin]
  change (∫ x, Complex.exp ((↑(finiteLinearForm a (coloredStarRootForm d r x) +
      finiteLinearForm b (coloredSimplexForm d r i x)) : ℂ) * Complex.I) ∂P) = _
  rw [hleft, colored_transverse_factorization_all d r hd hr P v hfactor _
    (coloredSimplexLift_sum d r (by omega) i b) a, coloredSimplexLift_squareRadius d r hd i b]
  have heq (z : (Fin r → ℝ) × (Fin r → ℝ)) :
      Complex.exp ((↑(finiteLinearForm a z.1 + finiteLinearForm b z.2) : ℂ) * Complex.I) =
        Complex.exp ((↑(finiteLinearForm a z.1) : ℂ) * Complex.I) *
          Complex.exp ((↑(finiteLinearForm b z.2) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [heq]
  rw [integral_prod_mul
    (fun x : Fin r → ℝ => Complex.exp ((↑(finiteLinearForm a x) : ℂ) * Complex.I))
    (fun x : Fin r → ℝ => Complex.exp ((↑(finiteLinearForm b x) : ℂ) * Complex.I))]
  change _ = characteristicIntegral ν a * characteristicIntegral (heatGaussian (Fin r) ((v : ℝ) / 2)) b
  rw [heatGaussian_characteristic, coe_heatVariance_half_nnreal]
  rfl

/-- Full joint Gaussianity from the vector root and every whole-colored
transverse characteristic direction. -/
theorem colored_eq_heatGaussian_of_root_and_transverse_characteristics
    (d r : ℕ) (hd : 2 ≤ d) (hr : 0 < r)
    (P : Measure (ColoredSpace d r)) [IsProbabilityMeasure P] (v : ℝ≥0)
    (hroot : Measure.map (coloredStarRootForm d r) P = heatGaussian (Fin r) ((v : ℝ) / 2))
    (hfactor : ∀ w : ColoredSpace d r, (∀ a, ∑ j, w (a, j) = 0) → squareRadius w = 1 →
      ∀ a : Fin r → ℝ, ∀ s : ℝ,
      characteristicIntegral P (coloredRootLift d r a + s • w) =
        characteristicIntegral (Measure.map (coloredStarRootForm d r) P) a *
          Complex.exp (Complex.ofReal (-(1 / 2 : ℝ) * (v : ℝ) * s ^ 2))) :
    P = heatGaussian (Fin r × Fin d) ((v : ℝ) / 2) := by
  apply measure_eq_of_linear_characteristic
  intro t
  change characteristicIntegral P t = characteristicIntegral (heatGaussian (Fin r × Fin d) ((v : ℝ) / 2)) t
  have ht := colored_root_transverse_decomposition d r (by omega) t
  calc
    _ = characteristicIntegral P (coloredRootLift d r (coloredStarRootForm d r t) +
        coloredTransversePart d r t) := by rw [← ht]
    _ = _ := by
      rw [colored_transverse_factorization_all d r hd hr P v hfactor _
        (sum_coloredTransversePart d r (by omega) t), hroot,
        heatGaussian_characteristic, ← Complex.exp_add,
        heatGaussian_characteristic, coe_heatVariance_half_nnreal]
      congr 1
      have he := colored_root_transverse_energy d r (by omega) t
      change squareMass (coloredStarRootForm d r t) + squareRadius (coloredTransversePart d r t) = squareMass t at he
      rw [← he]
      push_cast
      ring

/-- Whole-edge reversal and the derived transverse characteristic factors
force the actual entire colored star to be Gaussian. -/
theorem colored_gaussian_of_transverse_characteristics_and_reversal
    (d r : ℕ) (hd : 2 ≤ d) (hr : 0 < r)
    (P : Measure (ColoredSpace d r)) [IsProbabilityMeasure P] (v : ℝ≥0)
    (c : ℝ) (hc : |c| < 1) (i₀ : Fin d)
    (hfactor : ∀ w : ColoredSpace d r, (∀ a, ∑ j, w (a, j) = 0) → squareRadius w = 1 →
      ∀ a : Fin r → ℝ, ∀ s : ℝ,
      characteristicIntegral P (coloredRootLift d r a + s • w) =
        characteristicIntegral (Measure.map (coloredStarRootForm d r) P) a *
          Complex.exp (Complex.ofReal (-(1 / 2 : ℝ) * (v : ℝ) * s ^ 2)))
    (hrev : Measure.map (edgeFlipLinear r)
      (Measure.map (fun x => (coloredStarEdgeProjection d r c i₀).mulVec x) P) =
        Measure.map (fun x => (coloredStarEdgeProjection d r c i₀).mulVec x) P) :
    P = heatGaussian (Fin r × Fin d) ((v : ℝ) / 2) := by
  have hpair := colored_root_simplex_pair_eq_product_of_transverse_characteristics
    d r hd hr P v i₀ hfactor
  have hroot := colored_root_gaussian_of_pair_and_reversal d r P c hc i₀ v hpair hrev
  exact colored_eq_heatGaussian_of_root_and_transverse_characteristics d r hd hr P v hroot hfactor


/-- Original whole-edge reversal is preserved by the actual heat flow. -/
theorem colored_heated_edge_reversal (d r : ℕ) (hd : 2 ≤ d)
    (μ : Measure (ColoredSpace d r)) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : |c| < 1) (i : Fin d)
    (hrev : Measure.map (edgeFlipLinear r)
      (Measure.map (fun x => (coloredStarEdgeProjection d r c i).mulVec x) μ) =
        Measure.map (fun x => (coloredStarEdgeProjection d r c i).mulVec x) μ) (t : ℝ) :
    Measure.map (edgeFlipLinear r)
      (Measure.map (fun x => (coloredStarEdgeProjection d r c i).mulVec x) (heatedLaw μ t)) =
        Measure.map (fun x => (coloredStarEdgeProjection d r c i).mulVec x) (heatedLaw μ t) := by
  let O := coloredStarEdgeProjection d r c i
  let ν := Measure.map (fun x => O.mulVec x) μ
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_map
    (measurable_finiteMatrixAction O).aemeasurable
  have h := heatedLaw_coordinatePermutation_invariant ν (edgeFlipIndex r) hrev t
  rw [← heatedLaw_map_orthonormal_rows μ O
    (coloredStarEdgeProjection_mul_transpose d r hd c hc i) t] at h
  exact h

/-- Genuine colored root stationarity and full characteristic reconstruction
for an actual heated law. This intermediate component explicitly consumes
the transverse factorization; the colored log-density/Stein stage supplies it
when the Gaussian strictness theorem is assembled. -/
theorem colored_heated_gaussian_of_transverse_characteristics_and_reversal
    (d r : ℕ) (hd : 2 ≤ d) (hr : 0 < r)
    (μ : Measure (ColoredSpace d r)) [IsProbabilityMeasure μ]
    (t : ℝ) (v : ℝ≥0) (c : ℝ) (hc : |c| < 1) (i₀ : Fin d)
    (hfactor : ∀ w : ColoredSpace d r, (∀ a, ∑ j, w (a, j) = 0) → squareRadius w = 1 →
      ∀ a : Fin r → ℝ, ∀ s : ℝ,
      characteristicIntegral (heatedLaw μ t) (coloredRootLift d r a + s • w) =
        characteristicIntegral (Measure.map (coloredStarRootForm d r) (heatedLaw μ t)) a *
          Complex.exp (Complex.ofReal (-(1 / 2 : ℝ) * (v : ℝ) * s ^ 2)))
    (hrev : Measure.map (edgeFlipLinear r)
      (Measure.map (fun x => (coloredStarEdgeProjection d r c i₀).mulVec x) μ) =
        Measure.map (fun x => (coloredStarEdgeProjection d r c i₀).mulVec x) μ) :
    heatedLaw μ t = heatGaussian (Fin r × Fin d) ((v : ℝ) / 2) :=
  colored_gaussian_of_transverse_characteristics_and_reversal d r hd hr (heatedLaw μ t) v c hc i₀ hfactor
    (colored_heated_edge_reversal d r hd μ c hc i₀ hrev t)

end GaussianWave.BS
