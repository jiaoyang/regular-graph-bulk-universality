import GaussianWave.BS.ColoredPhysicalStarMap
import GaussianWave.BS.PhysicalUpperBound
import GaussianWave.BS.ColoredUpperBound
import GaussianWave.BS.ColoredGaussianStrictness

/-!
# The actual common-energy colored physical entropy upper bound

Every whole-edge law retains all channels. Physical canonical second moments
give white identity moments, while inverse coordinate transport constructs
the white finite-entropy witnesses. No independence hypothesis is used.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianWave.BS

theorem coloredPhysicalStarMap_white_law
    (d r : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1)
    (μ : Measure ((Fin r × Fin d) → ℝ)) :
    Measure.map (fun z => (coloredPhysicalStarInverseMatrix d r c).mulVec z)
      (Measure.map (coloredPhysicalStarMap d r c) μ) = μ := by
  rw [Measure.map_map (measurable_finiteMatrixAction (coloredPhysicalStarInverseMatrix d r c))
    (coloredPhysicalStarMap d r c).continuous_of_finiteDimensional.measurable]
  calc
    _ = Measure.map id μ := by
      apply Measure.map_congr
      exact ae_of_all _ (fun y => by
        change (coloredPhysicalStarInverseMatrix d r c).mulVec ((coloredPhysicalStarMatrix d r c).mulVec y) = y
        rw [Matrix.mulVec_mulVec, coloredPhysicalStarInverseMatrix_left_inverse d r hd c hc, Matrix.one_mulVec])
    _ = μ := Measure.map_id

theorem identitySecondMoments_of_coloredPhysicalStarMap
    (d r : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1)
    (μ : Measure ((Fin r × Fin d) → ℝ))
    (hC : HasSecondMoments (Measure.map (coloredPhysicalStarMap d r c) μ)
      (coloredPhysicalStarCovariance d r c)) : HasIdentitySecondMoments μ := by
  have hdiag (p : Fin r × Fin (d + 1)) : coloredPhysicalStarCovariance d r c p p = 1 := by
    rcases p with ⟨a, j⟩
    simp only [coloredPhysicalStarCovariance, channelLiftMatrix, ↓reduceIte]
    refine Fin.cases ?_ (fun i => ?_) j <;> simp [RegularEigenData.starWaveCovariance]
  have hκ := integrable_squareRadius_of_unitDiagonal_secondMoments _ _ hC hdiag
  rw [← coloredPhysicalStarMatrix_gram d r hd c hc] at hC
  have h := identitySecondMoments_of_gram_leftInverse _ hκ (coloredPhysicalStarMatrix d r c)
    (coloredPhysicalStarInverseMatrix d r c) hC (coloredPhysicalStarInverseMatrix_left_inverse d r hd c hc)
  rw [coloredPhysicalStarMap_white_law d r hd c hc μ] at h
  exact h

theorem coloredPhysicalStarMap_edge_law
    (d r : ℕ) (c : ℝ) (hc : |c| < 1) (i : Fin d)
    (μ : Measure ((Fin r × Fin d) → ℝ)) :
    Measure.map (coloredPhysicalEdgeCoordinates i) (Measure.map (coloredPhysicalStarMap d r c) μ) =
      Measure.map (fun x => (coloredPhysicalEdgeMatrix r c).mulVec x)
        (Measure.map (fun y => (coloredStarEdgeProjection d r c i).mulVec y) μ) := by
  rw [Measure.map_map (measurable_coloredPhysicalEdgeCoordinates i)
      (coloredPhysicalStarMap d r c).continuous_of_finiteDimensional.measurable,
    Measure.map_map (measurable_finiteMatrixAction (coloredPhysicalEdgeMatrix r c))
      (measurable_finiteMatrixAction (coloredStarEdgeProjection d r c i))]
  congr 1
  funext y
  exact coloredPhysicalStarMap_edge d r c hc i y

theorem coloredPhysicalEdgeMatrix_commutes_edgeFlip
    (r : ℕ) (c : ℝ) (x : (Bool × Fin r) → ℝ) :
    (coloredPhysicalEdgeMatrix r c).mulVec (edgeFlipLinear r x) =
      edgeFlipLinear r ((coloredPhysicalEdgeMatrix r c).mulVec x) := by
  ext p
  rcases p with ⟨b, a⟩
  cases b <;> simp [coloredPhysicalEdgeMatrix, endpointLiftMatrix_mulVec,
    physicalEdgeMatrix_mulVec_false, physicalEdgeMatrix_mulVec_true,
    edgeFlipLinear, coordinatePermutation_apply, edgeFlipIndex, add_comm]

theorem colored_white_edge_reversal_of_physical
    (r : ℕ) (c : ℝ) (hc : |c| < 1) (ν : Measure ((Bool × Fin r) → ℝ))
    (hrev : Measure.map (edgeFlipLinear r)
      (Measure.map (fun x => (coloredPhysicalEdgeMatrix r c).mulVec x) ν) =
        Measure.map (fun x => (coloredPhysicalEdgeMatrix r c).mulVec x) ν) :
    Measure.map (edgeFlipLinear r) ν = ν := by
  let M := coloredPhysicalEdgeMatrix r c
  have hM : M.det ≠ 0 := coloredPhysicalEdgeMatrix_det_ne_zero r c hc
  apply MeasurableEquiv.map_measurableEquiv_injective (invertibleMatrixMeasurableEquiv M hM)
  change Measure.map (fun x => M.mulVec x) (Measure.map (edgeFlipLinear r) ν) =
    Measure.map (fun x => M.mulVec x) ν
  calc
    _ = Measure.map (edgeFlipLinear r) (Measure.map (fun x => M.mulVec x) ν) := by
      rw [Measure.map_map (measurable_finiteMatrixAction M) (edgeFlipLinear r).continuous.measurable,
        Measure.map_map (edgeFlipLinear r).continuous.measurable (measurable_finiteMatrixAction M)]
      congr 1
      funext x
      exact coloredPhysicalEdgeMatrix_commutes_edgeFlip r c x
    _ = _ := hrev

def coloredPhysicalStarPermutation {d r : ℕ} (p : Equiv.Perm (Fin d))
    (z : (Fin r × Fin (d + 1)) → ℝ) : (Fin r × Fin (d + 1)) → ℝ :=
  fun q => physicalStarPermutation p (fun j => z (q.1, j)) q.2

theorem measurable_coloredPhysicalStarPermutation {d r : ℕ} (p : Equiv.Perm (Fin d)) :
    Measurable (coloredPhysicalStarPermutation (r := r) p) := by
  apply measurable_pi_lambda
  rintro ⟨a, j⟩
  refine Fin.cases ?_ (fun i => ?_) j <;> exact measurable_pi_apply _

theorem coloredPhysicalStarMap_permutation
    {d r : ℕ} (c : ℝ) (p : Equiv.Perm (Fin d)) (y : (Fin r × Fin d) → ℝ) :
    coloredPhysicalStarMap d r c (fun q => y (q.1, p q.2)) =
      coloredPhysicalStarPermutation p (coloredPhysicalStarMap d r c y) := by
  ext q
  rcases q with ⟨a, j⟩
  have h := congrFun (physicalStarMap_permutation c p (fun i => y (a, i))) j
  simpa only [coloredPhysicalStarMap_apply, coloredPhysicalStarPermutation] using h

theorem colored_white_permutation_of_physical
    (d r : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1)
    (μ : Measure ((Fin r × Fin d) → ℝ))
    (hperm : ∀ p : Equiv.Perm (Fin d), Measure.map (coloredPhysicalStarPermutation p)
      (Measure.map (coloredPhysicalStarMap d r c) μ) = Measure.map (coloredPhysicalStarMap d r c) μ) :
    ∀ p : Equiv.Perm (Fin d),
      Measure.map (fun y : (Fin r × Fin d) → ℝ => fun q => y (q.1, p q.2)) μ = μ := by
  intro p
  have hw : Measurable (fun y : (Fin r × Fin d) → ℝ => fun q : Fin r × Fin d => y (q.1, p q.2)) :=
    measurable_pi_lambda _ (fun q => measurable_pi_apply (q.1, p q.2))
  have hcomm : Measure.map (coloredPhysicalStarMap d r c)
      (Measure.map (fun y : (Fin r × Fin d) → ℝ => fun q => y (q.1, p q.2)) μ) =
      Measure.map (coloredPhysicalStarPermutation p) (Measure.map (coloredPhysicalStarMap d r c) μ) := by
    rw [Measure.map_map (coloredPhysicalStarMap d r c).continuous_of_finiteDimensional.measurable hw,
      Measure.map_map (measurable_coloredPhysicalStarPermutation p)
        (coloredPhysicalStarMap d r c).continuous_of_finiteDimensional.measurable]
    congr 1
    funext y
    exact coloredPhysicalStarMap_permutation c p y
  rw [hperm] at hcomm
  have h := congrArg (Measure.map (fun z => (coloredPhysicalStarInverseMatrix d r c).mulVec z)) hcomm
  simpa only [coloredPhysicalStarMap_white_law d r hd c hc] using h

def coloredPhysicalGaussianStarEntropyDensity
    (d r : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1)
    (chart : coloredPhysicalStarHyperplane d r c ≃ₗ[ℝ] ((Fin r × Fin d) → ℝ)) :=
  (standardVectorEntropyDensity (Fin r × Fin d)).linearImage
    (coloredPhysicalStarChartMatrix d r hd c hc chart) (coloredPhysicalStarChartMatrix_det_ne_zero d r hd c hc chart)

def coloredPhysicalGaussianEdgeEntropyDensity (r : ℕ) (c : ℝ) (hc : |c| < 1) :=
  (standardVectorEntropyDensity (Bool × Fin r)).linearImage (coloredPhysicalEdgeMatrix r c)
    (coloredPhysicalEdgeMatrix_det_ne_zero r c hc)

theorem colored_standardVector_edge_projection
    (d r : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1) (i : Fin d) :
    Measure.map (fun x => (coloredStarEdgeProjection d r c i).mulVec x) (standardVector (Fin r × Fin d)) =
      standardVector (Bool × Fin r) := by
  rw [← heatGaussian_half_eq_standardVector (Fin r × Fin d),
    heatGaussian_map_orthonormal_rows _ (coloredStarEdgeProjection_mul_transpose d r hd c hc i),
    heatGaussian_half_eq_standardVector (Bool × Fin r)]

theorem coloredPhysicalGaussian_edge_law
    (d r : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1) (i : Fin d) :
    Measure.map (coloredPhysicalEdgeCoordinates i)
      (Measure.map (coloredPhysicalStarMap d r c) (standardVector (Fin r × Fin d))) =
      Measure.map (fun x => (coloredPhysicalEdgeMatrix r c).mulVec x) (standardVector (Bool × Fin r)) := by
  rw [coloredPhysicalStarMap_edge_law d r c hc, colored_standardVector_edge_projection d r hd c hc]

def coloredPhysicalGaussianHyperplaneLaw
    (d r : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1) :
    Measure (coloredPhysicalStarHyperplane d r c) :=
  Measure.map (coloredPhysicalStarEquiv d r hd c hc) (standardVector (Fin r × Fin d))

theorem coloredPhysicalGaussianStar_chart_law
    (d r : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1)
    (chart : coloredPhysicalStarHyperplane d r c ≃ₗ[ℝ] ((Fin r × Fin d) → ℝ)) :
    Measure.map chart (coloredPhysicalGaussianHyperplaneLaw d r hd c hc) =
      Measure.map (fun y => (coloredPhysicalStarChartMatrix d r hd c hc chart).mulVec y)
        (standardVector (Fin r × Fin d)) := by
  have hcm : Measurable (fun z : coloredPhysicalStarHyperplane d r c => chart z) :=
    chart.continuous_of_finiteDimensional.measurable
  change Measure.map (fun z : coloredPhysicalStarHyperplane d r c => chart z)
    (Measure.map (fun y => coloredPhysicalStarEquiv d r hd c hc y) (standardVector (Fin r × Fin d))) = _
  have hem : Measurable (fun y => coloredPhysicalStarEquiv d r hd c hc y) :=
    (coloredPhysicalStarEquiv d r hd c hc).continuous_of_finiteDimensional.measurable
  rw [Measure.map_map hcm hem]
  congr 1
  funext y
  exact (coloredPhysicalStarChartMatrix_mulVec d r hd c hc chart y).symm

def coloredPhysicalStarWhiteEntropyDensity
    (d r : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1)
    (chart : coloredPhysicalStarHyperplane d r c ≃ₗ[ℝ] ((Fin r × Fin d) → ℝ))
    {μ : Measure ((Fin r × Fin d) → ℝ)} [IsProbabilityMeasure μ]
    (f : FiniteEntropyDensity (Measure.map
      (fun y => chart (coloredPhysicalStarEquiv d r hd c hc y)) μ)) : FiniteEntropyDensity μ := by
  have hchart : Measure.map (fun y => (coloredPhysicalStarChartMatrix d r hd c hc chart).mulVec y) μ =
      Measure.map (fun y => chart (coloredPhysicalStarEquiv d r hd c hc y)) μ := by
    congr 1
    funext y
    exact coloredPhysicalStarChartMatrix_mulVec d r hd c hc chart y
  exact (f.cast hchart).linearPreimage (coloredPhysicalStarChartMatrix d r hd c hc chart)
    (coloredPhysicalStarChartMatrix_det_ne_zero d r hd c hc chart)

theorem coloredPhysicalStarWhiteEntropyDensity_entropy
    (d r : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1)
    (chart : coloredPhysicalStarHyperplane d r c ≃ₗ[ℝ] ((Fin r × Fin d) → ℝ))
    {μ : Measure ((Fin r × Fin d) → ℝ)} [IsProbabilityMeasure μ]
    (f : FiniteEntropyDensity (Measure.map
      (fun y => chart (coloredPhysicalStarEquiv d r hd c hc y)) μ)) :
    (coloredPhysicalStarWhiteEntropyDensity d r hd c hc chart f).entropy +
      Real.log |(coloredPhysicalStarChartMatrix d r hd c hc chart).det| = f.entropy := by
  unfold coloredPhysicalStarWhiteEntropyDensity
  rw [FiniteEntropyDensity.linearPreimage_entropy, FiniteEntropyDensity.cast_entropy]

def coloredPhysicalEdgeWhiteEntropyDensity
    (d r : ℕ) (c : ℝ) (hc : |c| < 1) {μ : Measure ((Fin r × Fin d) → ℝ)} [IsProbabilityMeasure μ]
    (i : Fin d) (g : FiniteEntropyDensity (Measure.map (coloredPhysicalEdgeCoordinates i)
      (Measure.map (coloredPhysicalStarMap d r c) μ))) :
    FiniteEntropyDensity (Measure.map (fun y => (coloredStarEdgeProjection d r c i).mulVec y) μ) := by
  letI : IsProbabilityMeasure (Measure.map (fun y => (coloredStarEdgeProjection d r c i).mulVec y) μ) :=
    isProbabilityMeasure_map (measurable_finiteMatrixAction (coloredStarEdgeProjection d r c i)).aemeasurable
  exact (g.cast (coloredPhysicalStarMap_edge_law d r c hc i μ).symm).linearPreimage
    (coloredPhysicalEdgeMatrix r c) (coloredPhysicalEdgeMatrix_det_ne_zero r c hc)

theorem coloredPhysicalEdgeWhiteEntropyDensity_entropy
    (d r : ℕ) (c : ℝ) (hc : |c| < 1) {μ : Measure ((Fin r × Fin d) → ℝ)} [IsProbabilityMeasure μ]
    (i : Fin d) (g : FiniteEntropyDensity (Measure.map (coloredPhysicalEdgeCoordinates i)
      (Measure.map (coloredPhysicalStarMap d r c) μ))) :
    (coloredPhysicalEdgeWhiteEntropyDensity d r c hc i g).entropy +
      Real.log |(coloredPhysicalEdgeMatrix r c).det| = g.entropy := by
  letI : IsProbabilityMeasure (Measure.map (fun y => (coloredStarEdgeProjection d r c i).mulVec y) μ) :=
    isProbabilityMeasure_map (measurable_finiteMatrixAction (coloredStarEdgeProjection d r c i)).aemeasurable
  unfold coloredPhysicalEdgeWhiteEntropyDensity
  rw [FiniteEntropyDensity.linearPreimage_entropy, FiniteEntropyDensity.cast_entropy]

theorem coloredPhysicalGaussian_reference_entropy_value
    (d r : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1)
    (chart : coloredPhysicalStarHyperplane d r c ≃ₗ[ℝ] ((Fin r × Fin d) → ℝ)) :
    (coloredPhysicalGaussianStarEntropyDensity d r hd c hc chart).entropy -
      (d : ℝ) / 2 * (coloredPhysicalGaussianEdgeEntropyDensity r c hc).entropy =
        Real.log |(coloredPhysicalStarChartMatrix d r hd c hc chart).det| -
          (d : ℝ) / 2 * Real.log |(coloredPhysicalEdgeMatrix r c).det| := by
  have hf : (coloredPhysicalGaussianStarEntropyDensity d r hd c hc chart).entropy =
      (standardVectorEntropyDensity (Fin r × Fin d)).entropy +
        Real.log |(coloredPhysicalStarChartMatrix d r hd c hc chart).det| :=
    (standardVectorEntropyDensity (Fin r × Fin d)).linearImage_entropy _
      (coloredPhysicalStarChartMatrix_det_ne_zero d r hd c hc chart)
  have hg : (coloredPhysicalGaussianEdgeEntropyDensity r c hc).entropy =
      (standardVectorEntropyDensity (Bool × Fin r)).entropy + Real.log |(coloredPhysicalEdgeMatrix r c).det| :=
    (standardVectorEntropyDensity (Bool × Fin r)).linearImage_entropy _
      (coloredPhysicalEdgeMatrix_det_ne_zero r c hc)
  rw [hf, hg, standardVectorEntropyDensity_entropy, standardVectorEntropyDensity_entropy]
  simp only [gaussianEntropyValue, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
    Nat.cast_mul, Nat.cast_ofNat, NNReal.coe_one]
  ring

/-- Exact actual Gaussian-relative entropy cancellation for the joint
colored constraint space and whole-edge laws. -/
theorem coloredPhysicalFrameEntropy_whitening
    (d r : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1)
    (chart : coloredPhysicalStarHyperplane d r c ≃ₗ[ℝ] ((Fin r × Fin d) → ℝ))
    {μ : Measure ((Fin r × Fin d) → ℝ)} [IsProbabilityMeasure μ]
    (f : FiniteEntropyDensity (Measure.map
      (fun y => chart (coloredPhysicalStarEquiv d r hd c hc y)) μ))
    (g : ∀ i, FiniteEntropyDensity (Measure.map (coloredPhysicalEdgeCoordinates i)
      (Measure.map (coloredPhysicalStarMap d r c) μ))) :
    (f.entropy - (1 / 2 : ℝ) * ∑ i, (g i).entropy) -
      ((coloredPhysicalGaussianStarEntropyDensity d r hd c hc chart).entropy -
        (d : ℝ) / 2 * (coloredPhysicalGaussianEdgeEntropyDensity r c hc).entropy) =
      initialFrameEntropy (coloredPhysicalStarWhiteEntropyDensity d r hd c hc chart f)
        (fun i => coloredPhysicalEdgeWhiteEntropyDensity d r c hc i (g i)) := by
  rw [coloredPhysicalGaussian_reference_entropy_value,
    ← coloredPhysicalStarWhiteEntropyDensity_entropy d r hd c hc chart f]
  simp_rw [← coloredPhysicalEdgeWhiteEntropyDensity_entropy d r c hc]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, initialFrameEntropy]
  ring

/-- Actual common-energy multichannel physical entropy upper bound, using
the proved bijective parameterization of the physical constraint space.
All moment, entropy, and symmetry assumptions concern the physical laws. -/
theorem colored_physical_star_entropy_upper
    (d r : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (chart : coloredPhysicalStarHyperplane d r c ≃ₗ[ℝ] ((Fin r × Fin d) → ℝ))
    (μ : Measure ((Fin r × Fin d) → ℝ)) [IsProbabilityMeasure μ]
    (hC : HasSecondMoments (Measure.map (coloredPhysicalStarMap d r c) μ)
      (coloredPhysicalStarCovariance d r c))
    (f : FiniteEntropyDensity (Measure.map
      (fun y => chart (coloredPhysicalStarEquiv d r (by omega) c (bulk_rho_lower d hd c hbulk).1 y)) μ))
    (g : ∀ i, FiniteEntropyDensity (Measure.map (coloredPhysicalEdgeCoordinates i)
      (Measure.map (coloredPhysicalStarMap d r c) μ)))
    (hrev : ∀ i, Measure.map (edgeFlipLinear r) (Measure.map (coloredPhysicalEdgeCoordinates i)
      (Measure.map (coloredPhysicalStarMap d r c) μ)) =
        Measure.map (coloredPhysicalEdgeCoordinates i) (Measure.map (coloredPhysicalStarMap d r c) μ)) :
    f.entropy - (1 / 2 : ℝ) * ∑ i, (g i).entropy ≤
      (coloredPhysicalGaussianStarEntropyDensity d r (by omega) c (bulk_rho_lower d hd c hbulk).1 chart).entropy -
        (d : ℝ) / 2 * (coloredPhysicalGaussianEdgeEntropyDensity r c (bulk_rho_lower d hd c hbulk).1).entropy := by
  let hd2 : 2 ≤ d := by omega
  let hc := (bulk_rho_lower d hd c hbulk).1
  let A := coloredPhysicalStarChartMatrix d r hd2 c hc chart
  have hA : A.det ≠ 0 := coloredPhysicalStarChartMatrix_det_ne_zero d r hd2 c hc chart
  let M := coloredPhysicalEdgeMatrix r c
  have hM : M.det ≠ 0 := coloredPhysicalEdgeMatrix_det_ne_zero r c hc
  have hchart : Measure.map (fun y => A.mulVec y) μ =
      Measure.map (fun y => chart (coloredPhysicalStarEquiv d r hd2 c hc y)) μ := by
    congr 1
    funext y
    exact coloredPhysicalStarChartMatrix_mulVec d r hd2 c hc chart y
  let fA := f.cast hchart
  let fw := fA.linearPreimage A hA
  let ν := fun i => Measure.map (fun y => (coloredStarEdgeProjection d r c i).mulVec y) μ
  letI : ∀ i, IsProbabilityMeasure (ν i) := fun i =>
    isProbabilityMeasure_map (measurable_finiteMatrixAction (coloredStarEdgeProjection d r c i)).aemeasurable
  let gA := fun i => (g i).cast (coloredPhysicalStarMap_edge_law d r c hc i μ).symm
  let gw := fun i => (gA i).linearPreimage M hM
  have hfw : fw.entropy + Real.log |A.det| = f.entropy := by
    simpa only [fw, fA, FiniteEntropyDensity.cast_entropy] using fA.linearPreimage_entropy A hA
  have hgw (i : Fin d) : (gw i).entropy + Real.log |M.det| = (g i).entropy := by
    simpa only [gw, gA, FiniteEntropyDensity.cast_entropy] using (gA i).linearPreimage_entropy M hM
  have hwhite := identitySecondMoments_of_coloredPhysicalStarMap d r hd2 c hc μ hC
  have hrevWhite (i : Fin d) : Measure.map (edgeFlipLinear r) (ν i) = ν i := by
    apply colored_white_edge_reversal_of_physical r c hc (ν i)
    have h := hrev i
    rw [coloredPhysicalStarMap_edge_law d r c hc i μ] at h
    exact h
  have hupper := colored_star_entropy_upper d r hd c hbulk μ
    (integrable_squareRadius_of_identitySecondMoments μ hwhite) hwhite fw gw hrevWhite
  have hrefFull : (coloredPhysicalGaussianStarEntropyDensity d r hd2 c hc chart).entropy =
      (standardVectorEntropyDensity (Fin r × Fin d)).entropy + Real.log |A.det| :=
    (standardVectorEntropyDensity (Fin r × Fin d)).linearImage_entropy A hA
  have hrefEdge : (coloredPhysicalGaussianEdgeEntropyDensity r c hc).entropy =
      (standardVectorEntropyDensity (Bool × Fin r)).entropy + Real.log |M.det| :=
    (standardVectorEntropyDensity (Bool × Fin r)).linearImage_entropy M hM
  have hGauss : (standardVectorEntropyDensity (Fin r × Fin d)).entropy -
      (d : ℝ) / 2 * (standardVectorEntropyDensity (Bool × Fin r)).entropy = 0 := by
    rw [standardVectorEntropyDensity_entropy, standardVectorEntropyDensity_entropy]
    simp only [gaussianEntropyValue, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
      Nat.cast_mul, Nat.cast_ofNat, NNReal.coe_one]
    ring
  calc
    _ = (fw.entropy - (1 / 2 : ℝ) * ∑ i, (gw i).entropy) +
        Real.log |A.det| - (d : ℝ) / 2 * Real.log |M.det| := by
      rw [← hfw]
      simp_rw [← hgw]
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      ring
    _ ≤ Real.log |A.det| - (d : ℝ) / 2 * Real.log |M.det| := by linarith
    _ = _ := by rw [hrefFull, hrefEdge]; linarith

/-- The actual colored physical upper inequality for a probability law on
the joint constraint subspace, without a white parameterization premise.
The channels of this law may have arbitrary higher dependence. -/
theorem colored_physical_hyperplane_entropy_upper
    (d r : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (chart : coloredPhysicalStarHyperplane d r c ≃ₗ[ℝ] ((Fin r × Fin d) → ℝ))
    (N : Measure (coloredPhysicalStarHyperplane d r c)) [IsProbabilityMeasure N]
    (hC : HasSecondMoments (Measure.map (fun z : coloredPhysicalStarHyperplane d r c =>
        (z : (Fin r × Fin (d + 1)) → ℝ)) N) (coloredPhysicalStarCovariance d r c))
    (f : FiniteEntropyDensity (Measure.map chart N))
    (g : ∀ i, FiniteEntropyDensity (Measure.map (coloredPhysicalEdgeCoordinates i)
      (Measure.map (fun z : coloredPhysicalStarHyperplane d r c => (z : (Fin r × Fin (d + 1)) → ℝ)) N)))
    (hrev : ∀ i, Measure.map (edgeFlipLinear r) (Measure.map (coloredPhysicalEdgeCoordinates i)
      (Measure.map (fun z : coloredPhysicalStarHyperplane d r c => (z : (Fin r × Fin (d + 1)) → ℝ)) N)) =
        Measure.map (coloredPhysicalEdgeCoordinates i)
          (Measure.map (fun z : coloredPhysicalStarHyperplane d r c => (z : (Fin r × Fin (d + 1)) → ℝ)) N)) :
    f.entropy - (1 / 2 : ℝ) * ∑ i, (g i).entropy ≤
      (coloredPhysicalGaussianStarEntropyDensity d r (by omega) c (bulk_rho_lower d hd c hbulk).1 chart).entropy -
        (d : ℝ) / 2 * (coloredPhysicalGaussianEdgeEntropyDensity r c (bulk_rho_lower d hd c hbulk).1).entropy := by
  let hd2 : 2 ≤ d := by omega
  let hc := (bulk_rho_lower d hd c hbulk).1
  let E := (coloredPhysicalStarEquiv d r hd2 c hc).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  let μ := Measure.map E.symm N
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_map E.symm.measurable.aemeasurable
  have hN : Measure.map E μ = N := MeasurableEquiv.map_map_symm E
  have hchart : Measure.map (fun y => chart (coloredPhysicalStarEquiv d r hd2 c hc y)) μ =
      Measure.map chart N := by
    rw [← hN]
    have hcm : Measurable (fun z : coloredPhysicalStarHyperplane d r c => chart z) :=
      chart.continuous_of_finiteDimensional.measurable
    exact (Measure.map_map hcm E.measurable).symm
  have hambient : Measure.map (coloredPhysicalStarMap d r c) μ =
      Measure.map (fun z : coloredPhysicalStarHyperplane d r c => (z : (Fin r × Fin (d + 1)) → ℝ)) N := by
    rw [← hN, Measure.map_map measurable_subtype_coe E.measurable]
    rfl
  have hCμ : HasSecondMoments (Measure.map (coloredPhysicalStarMap d r c) μ)
      (coloredPhysicalStarCovariance d r c) := by rw [hambient]; exact hC
  let fμ := f.cast hchart
  have hedge (i : Fin d) : Measure.map (coloredPhysicalEdgeCoordinates i) (Measure.map (coloredPhysicalStarMap d r c) μ) =
      Measure.map (coloredPhysicalEdgeCoordinates i)
        (Measure.map (fun z : coloredPhysicalStarHyperplane d r c => (z : (Fin r × Fin (d + 1)) → ℝ)) N) := by rw [hambient]
  let gμ := fun i => (g i).cast (hedge i)
  have hrevμ (i : Fin d) : Measure.map (edgeFlipLinear r)
      (Measure.map (coloredPhysicalEdgeCoordinates i) (Measure.map (coloredPhysicalStarMap d r c) μ)) =
        Measure.map (coloredPhysicalEdgeCoordinates i) (Measure.map (coloredPhysicalStarMap d r c) μ) := by
    rw [hedge]
    exact hrev i
  have h := colored_physical_star_entropy_upper d r hd c hbulk chart μ hCμ fμ gμ hrevμ
  simpa only [fμ, gμ, FiniteEntropyDensity.cast_entropy] using h

/-- Equality in the actual colored physical upper bound identifies the
full joint Gaussian law, including independence of the whitened channels as
a conclusion rather than an assumption. -/
theorem colored_physical_star_entropy_equality_iff_standardVector
    (d r : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (chart : coloredPhysicalStarHyperplane d r c ≃ₗ[ℝ] ((Fin r × Fin d) → ℝ))
    (μ : Measure ((Fin r × Fin d) → ℝ)) [IsProbabilityMeasure μ]
    (hC : HasSecondMoments (Measure.map (coloredPhysicalStarMap d r c) μ)
      (coloredPhysicalStarCovariance d r c))
    (f : FiniteEntropyDensity (Measure.map
      (fun y => chart (coloredPhysicalStarEquiv d r (by omega) c (bulk_rho_lower d hd c hbulk).1 y)) μ))
    (g : ∀ i, FiniteEntropyDensity (Measure.map (coloredPhysicalEdgeCoordinates i)
      (Measure.map (coloredPhysicalStarMap d r c) μ)))
    (hrev : ∀ i, Measure.map (edgeFlipLinear r) (Measure.map (coloredPhysicalEdgeCoordinates i)
      (Measure.map (coloredPhysicalStarMap d r c) μ)) =
        Measure.map (coloredPhysicalEdgeCoordinates i) (Measure.map (coloredPhysicalStarMap d r c) μ))
    (hperm : ∀ p : Equiv.Perm (Fin d), Measure.map (coloredPhysicalStarPermutation p)
      (Measure.map (coloredPhysicalStarMap d r c) μ) = Measure.map (coloredPhysicalStarMap d r c) μ) :
    (f.entropy - (1 / 2 : ℝ) * ∑ i, (g i).entropy =
      (coloredPhysicalGaussianStarEntropyDensity d r (by omega) c (bulk_rho_lower d hd c hbulk).1 chart).entropy -
        (d : ℝ) / 2 * (coloredPhysicalGaussianEdgeEntropyDensity r c (bulk_rho_lower d hd c hbulk).1).entropy) ↔
      μ = standardVector (Fin r × Fin d) := by
  let hd2 : 2 ≤ d := by omega
  let hc := (bulk_rho_lower d hd c hbulk).1
  have hwhite := identitySecondMoments_of_coloredPhysicalStarMap d r hd2 c hc μ hC
  have hrevWhite (i : Fin d) : Measure.map (edgeFlipLinear r)
      (Measure.map (fun y => (coloredStarEdgeProjection d r c i).mulVec y) μ) =
        Measure.map (fun y => (coloredStarEdgeProjection d r c i).mulVec y) μ := by
    apply colored_white_edge_reversal_of_physical r c hc
    have h := hrev i
    rw [coloredPhysicalStarMap_edge_law d r c hc i μ] at h
    exact h
  rw [← sub_eq_zero, coloredPhysicalFrameEntropy_whitening d r hd2 c hc chart f g]
  exact colored_star_entropy_equality_iff_standardVector d r hd c hbulk μ hwhite
    (coloredPhysicalStarWhiteEntropyDensity d r hd2 c hc chart f)
    (fun i => coloredPhysicalEdgeWhiteEntropyDensity d r c hc i (g i)) hrevWhite
    (colored_white_permutation_of_physical d r hd2 c hc μ hperm)

/-- The joint Gaussian equality case for an actual physical multichannel law
on its constraint space. The theorem includes r=0 and imposes no independence
assumption on the input law. -/
theorem colored_physical_hyperplane_entropy_equality_iff_gaussian
    (d r : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (chart : coloredPhysicalStarHyperplane d r c ≃ₗ[ℝ] ((Fin r × Fin d) → ℝ))
    (N : Measure (coloredPhysicalStarHyperplane d r c)) [IsProbabilityMeasure N]
    (hC : HasSecondMoments (Measure.map (fun z : coloredPhysicalStarHyperplane d r c =>
        (z : (Fin r × Fin (d + 1)) → ℝ)) N) (coloredPhysicalStarCovariance d r c))
    (f : FiniteEntropyDensity (Measure.map chart N))
    (g : ∀ i, FiniteEntropyDensity (Measure.map (coloredPhysicalEdgeCoordinates i)
      (Measure.map (fun z : coloredPhysicalStarHyperplane d r c => (z : (Fin r × Fin (d + 1)) → ℝ)) N)))
    (hrev : ∀ i, Measure.map (edgeFlipLinear r) (Measure.map (coloredPhysicalEdgeCoordinates i)
      (Measure.map (fun z : coloredPhysicalStarHyperplane d r c => (z : (Fin r × Fin (d + 1)) → ℝ)) N)) =
        Measure.map (coloredPhysicalEdgeCoordinates i)
          (Measure.map (fun z : coloredPhysicalStarHyperplane d r c => (z : (Fin r × Fin (d + 1)) → ℝ)) N))
    (hperm : ∀ p : Equiv.Perm (Fin d), Measure.map (coloredPhysicalStarPermutation p)
      (Measure.map (fun z : coloredPhysicalStarHyperplane d r c => (z : (Fin r × Fin (d + 1)) → ℝ)) N) =
        Measure.map (fun z : coloredPhysicalStarHyperplane d r c => (z : (Fin r × Fin (d + 1)) → ℝ)) N) :
    (f.entropy - (1 / 2 : ℝ) * ∑ i, (g i).entropy =
      (coloredPhysicalGaussianStarEntropyDensity d r (by omega) c (bulk_rho_lower d hd c hbulk).1 chart).entropy -
        (d : ℝ) / 2 * (coloredPhysicalGaussianEdgeEntropyDensity r c (bulk_rho_lower d hd c hbulk).1).entropy) ↔
      N = coloredPhysicalGaussianHyperplaneLaw d r (by omega) c (bulk_rho_lower d hd c hbulk).1 := by
  let hd2 : 2 ≤ d := by omega
  let hc := (bulk_rho_lower d hd c hbulk).1
  let E := (coloredPhysicalStarEquiv d r hd2 c hc).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  let μ := Measure.map E.symm N
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_map E.symm.measurable.aemeasurable
  have hN : Measure.map E μ = N := MeasurableEquiv.map_map_symm E
  have hchart : Measure.map (fun y => chart (coloredPhysicalStarEquiv d r hd2 c hc y)) μ =
      Measure.map chart N := by
    rw [← hN]
    have hcm : Measurable (fun z : coloredPhysicalStarHyperplane d r c => chart z) :=
      chart.continuous_of_finiteDimensional.measurable
    exact (Measure.map_map hcm E.measurable).symm
  have hambient : Measure.map (coloredPhysicalStarMap d r c) μ =
      Measure.map (fun z : coloredPhysicalStarHyperplane d r c => (z : (Fin r × Fin (d + 1)) → ℝ)) N := by
    rw [← hN, Measure.map_map measurable_subtype_coe E.measurable]
    rfl
  have hCμ : HasSecondMoments (Measure.map (coloredPhysicalStarMap d r c) μ)
      (coloredPhysicalStarCovariance d r c) := by rw [hambient]; exact hC
  let fμ := f.cast hchart
  have hedge (i : Fin d) : Measure.map (coloredPhysicalEdgeCoordinates i) (Measure.map (coloredPhysicalStarMap d r c) μ) =
      Measure.map (coloredPhysicalEdgeCoordinates i)
        (Measure.map (fun z : coloredPhysicalStarHyperplane d r c => (z : (Fin r × Fin (d + 1)) → ℝ)) N) := by rw [hambient]
  let gμ := fun i => (g i).cast (hedge i)
  have hrevμ (i : Fin d) : Measure.map (edgeFlipLinear r)
      (Measure.map (coloredPhysicalEdgeCoordinates i) (Measure.map (coloredPhysicalStarMap d r c) μ)) =
        Measure.map (coloredPhysicalEdgeCoordinates i) (Measure.map (coloredPhysicalStarMap d r c) μ) := by
    rw [hedge]
    exact hrev i
  have hpermμ (p : Equiv.Perm (Fin d)) : Measure.map (coloredPhysicalStarPermutation p)
      (Measure.map (coloredPhysicalStarMap d r c) μ) = Measure.map (coloredPhysicalStarMap d r c) μ := by
    rw [hambient]
    exact hperm p
  have h := colored_physical_star_entropy_equality_iff_standardVector d r hd c hbulk chart μ hCμ fμ gμ hrevμ hpermμ
  have hlaw : μ = standardVector (Fin r × Fin d) ↔
      N = coloredPhysicalGaussianHyperplaneLaw d r hd2 c hc := by
    change μ = standardVector (Fin r × Fin d) ↔ N = Measure.map E (standardVector (Fin r × Fin d))
    constructor
    · intro hμ
      rw [← hN, hμ]
    · intro hNstd
      apply MeasurableEquiv.map_measurableEquiv_injective E
      rw [hN, hNstd]
  simpa only [fμ, gμ, FiniteEntropyDensity.cast_entropy] using h.trans hlaw

end GaussianWave.BS
