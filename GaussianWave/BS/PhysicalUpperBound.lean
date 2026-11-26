import GaussianWave.BS.PhysicalStarMap
import GaussianWave.BS.SecondMomentTransport
import GaussianWave.BS.GaussianEntropyWitness
import GaussianWave.BS.ScalarGaussianStrictness
import GaussianWave.BS.StarSymmetry

/-!
# The BS upper inequality for actual physical star laws

The main theorem uses the bijective parameterization of the physical
eigenrelation hyperplane by `physicalStarEquiv`. All moment, entropy, and
reversal hypotheses are stated on its actual physical laws. White moments
and finite-entropy densities are derived, rather than assumed.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianWave.BS

theorem invertibleMatrix_inverse_map
    {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℝ) (hM : M.det ≠ 0) (μ : Measure (I → ℝ)) :
    Measure.map (fun x => M⁻¹.mulVec x) (Measure.map (fun x => M.mulVec x) μ) = μ := by
  rw [Measure.map_map (measurable_finiteMatrixAction M⁻¹) (measurable_finiteMatrixAction M)]
  have he : (fun x => M⁻¹.mulVec (M.mulVec x)) = id := by
    funext x
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM), Matrix.one_mulVec]
    rfl
  change Measure.map (fun x => M⁻¹.mulVec (M.mulVec x)) μ = μ
  rw [he, Measure.map_id]

/-- Construct a white finite-entropy witness from an actual nonsingular
linear image law, using the proved inverse-density Jacobian. -/
def FiniteEntropyDensity.linearPreimage
    {I : Type*} [Fintype I] [DecidableEq I]
    {μ : Measure (I → ℝ)} [IsProbabilityMeasure μ]
    (M : Matrix I I ℝ) (hM : M.det ≠ 0)
    (f : FiniteEntropyDensity (Measure.map (fun x => M.mulVec x) μ)) :
    FiniteEntropyDensity μ := by
  letI : IsProbabilityMeasure (Measure.map (fun x => M.mulVec x) μ) :=
    isProbabilityMeasure_map (measurable_finiteMatrixAction M).aemeasurable
  have hi : (M⁻¹).det ≠ 0 := by rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]; exact inv_ne_zero hM
  exact (f.linearImage M⁻¹ hi).cast (invertibleMatrix_inverse_map M hM μ).symm

theorem FiniteEntropyDensity.linearPreimage_entropy
    {I : Type*} [Fintype I] [DecidableEq I]
    {μ : Measure (I → ℝ)} [IsProbabilityMeasure μ]
    (M : Matrix I I ℝ) (hM : M.det ≠ 0)
    (f : FiniteEntropyDensity (Measure.map (fun x => M.mulVec x) μ)) :
    (f.linearPreimage M hM).entropy + Real.log |M.det| = f.entropy := by
  have h := ((f.linearPreimage M hM).linearImage M hM).entropy_eq_of_measure_eq f rfl
  rw [FiniteEntropyDensity.linearImage_entropy] at h
  exact h

theorem physicalStarMap_white_law (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1)
    (μ : Measure (Fin d → ℝ)) :
    Measure.map (fun z => (physicalStarInverseMatrix d c).mulVec z)
      (Measure.map (physicalStarMap d c) μ) = μ := by
  rw [Measure.map_map (measurable_finiteMatrixAction (physicalStarInverseMatrix d c))
    (physicalStarMap d c).continuous_of_finiteDimensional.measurable]
  calc
    _ = Measure.map id μ := by
      apply Measure.map_congr
      exact ae_of_all _ (fun y => by
        change (physicalStarInverseMatrix d c).mulVec (physicalStarMap d c y) = y
        rw [physicalStarInverseMatrix_mulVec]
        exact physicalStarInverse_left_inverse d hd c hc y)
    _ = μ := Measure.map_id

/-- Physical canonical second moments imply actual white identity moments.
There is no white moment normalization premise. -/
theorem identitySecondMoments_of_physicalStarMap
    (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1)
    (μ : Measure (Fin d → ℝ))
    (hC : HasSecondMoments (Measure.map (physicalStarMap d c) μ)
      (RegularEigenData.starWaveCovariance d ((d : ℝ) * c))) :
    HasIdentitySecondMoments μ := by
  have hdiag (a : Fin (d + 1)) :
      RegularEigenData.starWaveCovariance d ((d : ℝ) * c) a a = 1 := by
    refine Fin.cases ?_ (fun i => ?_) a <;> simp [RegularEigenData.starWaveCovariance]
  have hκ := integrable_squareRadius_of_unitDiagonal_secondMoments _ _ hC hdiag
  rw [← physicalStarMatrix_gram d hd c hc] at hC
  have h := identitySecondMoments_of_gram_leftInverse _ hκ (physicalStarMatrix d c)
    (physicalStarInverseMatrix d c) hC (physicalStarInverseMatrix_left_inverse d hd c hc)
  rw [physicalStarMap_white_law d hd c hc μ] at h
  exact h

theorem physicalEdgeMatrix_commutes_binarySwap (c : ℝ) (x : Bool → ℝ) :
    (physicalEdgeMatrix c).mulVec (binarySwap x) = binarySwap ((physicalEdgeMatrix c).mulVec x) := by
  ext b
  cases b <;> simp [physicalEdgeMatrix_mulVec_false, physicalEdgeMatrix_mulVec_true,
    binarySwap, coordinatePermutation_apply, Equiv.swap_apply_def, add_comm]

/-- Physical endpoint reversal is exactly the white edge reversal; the
commuting endpoint matrix is genuinely invertible in the strict bulk. -/
theorem white_edge_reversal_of_physical
    (c : ℝ) (hc : |c| < 1) (ν : Measure (Bool → ℝ))
    (hrev : Measure.map binarySwap (Measure.map (fun x => (physicalEdgeMatrix c).mulVec x) ν) =
      Measure.map (fun x => (physicalEdgeMatrix c).mulVec x) ν) :
    Measure.map binarySwap ν = ν := by
  have hdet : (physicalEdgeMatrix c).det ≠ 0 := by
    rw [physicalEdgeMatrix_det c hc]
    exact (rho_pos c hc).ne'
  apply MeasurableEquiv.map_measurableEquiv_injective (invertibleMatrixMeasurableEquiv (physicalEdgeMatrix c) hdet)
  change Measure.map (fun x => (physicalEdgeMatrix c).mulVec x) (Measure.map binarySwap ν) =
    Measure.map (fun x => (physicalEdgeMatrix c).mulVec x) ν
  calc
    _ = Measure.map binarySwap (Measure.map (fun x => (physicalEdgeMatrix c).mulVec x) ν) := by
      rw [Measure.map_map (measurable_finiteMatrixAction _) binarySwap.continuous.measurable,
        Measure.map_map binarySwap.continuous.measurable (measurable_finiteMatrixAction _)]
      congr 1
      funext x
      exact physicalEdgeMatrix_commutes_binarySwap c x
    _ = _ := hrev

def physicalGaussianStarEntropyDensity
    (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1)
    (chart : physicalStarHyperplane d c ≃ₗ[ℝ] (Fin d → ℝ)) :=
  (standardVectorEntropyDensity (Fin d)).physicalStarChart d hd c hc chart

def physicalGaussianEdgeEntropyDensity (c : ℝ) (hc : |c| < 1) :
    FiniteEntropyDensity (Measure.map (fun x => (physicalEdgeMatrix c).mulVec x) (standardVector Bool)) :=
  (standardVectorEntropyDensity Bool).linearImage (physicalEdgeMatrix c)
    (by rw [physicalEdgeMatrix_det c hc]; exact (rho_pos c hc).ne')

theorem physicalGaussian_edge_law (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1) (i : Fin d) :
    Measure.map (physicalEdgeCoordinates i) (Measure.map (physicalStarMap d c) (standardVector (Fin d))) =
      Measure.map (fun x => (physicalEdgeMatrix c).mulVec x) (standardVector Bool) := by
  rw [physicalStarMap_edge_law d c hc, standardVector_starEdgeProjection d hd c hc]

def physicalStarPermutation {d : ℕ} (p : Equiv.Perm (Fin d))
    (z : Fin (d + 1) → ℝ) : Fin (d + 1) → ℝ :=
  Fin.cases (z 0) (fun i => z (p i).succ)

theorem measurable_physicalStarPermutation {d : ℕ} (p : Equiv.Perm (Fin d)) :
    Measurable (physicalStarPermutation p) := by
  apply measurable_pi_lambda
  intro a
  refine Fin.cases ?_ (fun i => ?_) a <;> exact measurable_pi_apply _

theorem physicalStarMap_permutation {d : ℕ} (c : ℝ) (p : Equiv.Perm (Fin d)) (y : Fin d → ℝ) :
    physicalStarMap d c (fun j => y (p j)) = physicalStarPermutation p (physicalStarMap d c y) := by
  ext a
  refine Fin.cases ?_ (fun i => ?_) a
  · simp [physicalStarPermutation, starRootForm_permutation]
  · simp only [physicalStarMap_leaf, physicalStarPermutation, Fin.cases_succ,
      starRootForm_permutation, starCenteredCoordinate_permutation]

theorem white_permutation_of_physical
    (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1) (μ : Measure (Fin d → ℝ))
    (hperm : ∀ p : Equiv.Perm (Fin d), Measure.map (physicalStarPermutation p)
      (Measure.map (physicalStarMap d c) μ) = Measure.map (physicalStarMap d c) μ) :
    ∀ p : Equiv.Perm (Fin d), Measure.map (fun y : Fin d → ℝ => fun j => y (p j)) μ = μ := by
  intro p
  have hw : Measurable (fun y : Fin d → ℝ => fun j => y (p j)) :=
    measurable_pi_lambda _ (fun j => measurable_pi_apply (p j))
  have hcomm : Measure.map (physicalStarMap d c)
      (Measure.map (fun y : Fin d → ℝ => fun j => y (p j)) μ) =
      Measure.map (physicalStarPermutation p) (Measure.map (physicalStarMap d c) μ) := by
    rw [Measure.map_map (physicalStarMap d c).continuous_of_finiteDimensional.measurable hw,
      Measure.map_map (measurable_physicalStarPermutation p)
        (physicalStarMap d c).continuous_of_finiteDimensional.measurable]
    congr 1
    funext y
    exact physicalStarMap_permutation c p y
  rw [hperm] at hcomm
  have h := congrArg (Measure.map (fun z => (physicalStarInverseMatrix d c).mulVec z)) hcomm
  simpa only [physicalStarMap_white_law d hd c hc] using h

def physicalStarWhiteEntropyDensity
    (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1)
    (chart : physicalStarHyperplane d c ≃ₗ[ℝ] (Fin d → ℝ))
    {μ : Measure (Fin d → ℝ)} [IsProbabilityMeasure μ]
    (f : FiniteEntropyDensity (Measure.map (fun y => chart (physicalStarEquiv d hd c hc y)) μ)) :
    FiniteEntropyDensity μ := by
  have hchart : Measure.map (fun y => (physicalStarChartMatrix d hd c hc chart).mulVec y) μ =
      Measure.map (fun y => chart (physicalStarEquiv d hd c hc y)) μ := by
    congr 1
    funext y
    exact physicalStarChartMatrix_mulVec d hd c hc chart y
  exact (f.cast hchart).linearPreimage (physicalStarChartMatrix d hd c hc chart)
    (physicalStarChartMatrix_det_ne_zero d hd c hc chart)

theorem physicalStarWhiteEntropyDensity_entropy
    (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1)
    (chart : physicalStarHyperplane d c ≃ₗ[ℝ] (Fin d → ℝ))
    {μ : Measure (Fin d → ℝ)} [IsProbabilityMeasure μ]
    (f : FiniteEntropyDensity (Measure.map (fun y => chart (physicalStarEquiv d hd c hc y)) μ)) :
    (physicalStarWhiteEntropyDensity d hd c hc chart f).entropy +
      Real.log |(physicalStarChartMatrix d hd c hc chart).det| = f.entropy := by
  unfold physicalStarWhiteEntropyDensity
  rw [FiniteEntropyDensity.linearPreimage_entropy, FiniteEntropyDensity.cast_entropy]

def physicalEdgeWhiteEntropyDensity
    (d : ℕ) (c : ℝ) (hc : |c| < 1) {μ : Measure (Fin d → ℝ)} [IsProbabilityMeasure μ]
    (i : Fin d) (g : FiniteEntropyDensity
      (Measure.map (physicalEdgeCoordinates i) (Measure.map (physicalStarMap d c) μ))) :
    FiniteEntropyDensity (Measure.map (fun y => (starEdgeProjection d c i).mulVec y) μ) := by
  letI : IsProbabilityMeasure (Measure.map (fun y => (starEdgeProjection d c i).mulVec y) μ) :=
    isProbabilityMeasure_map (measurable_finiteMatrixAction (starEdgeProjection d c i)).aemeasurable
  exact (g.cast (physicalStarMap_edge_law d c hc i μ).symm).linearPreimage (physicalEdgeMatrix c)
    (by rw [physicalEdgeMatrix_det c hc]; exact (rho_pos c hc).ne')

theorem physicalEdgeWhiteEntropyDensity_entropy
    (d : ℕ) (c : ℝ) (hc : |c| < 1) {μ : Measure (Fin d → ℝ)} [IsProbabilityMeasure μ]
    (i : Fin d) (g : FiniteEntropyDensity
      (Measure.map (physicalEdgeCoordinates i) (Measure.map (physicalStarMap d c) μ))) :
    (physicalEdgeWhiteEntropyDensity d c hc i g).entropy + Real.log (rho c) = g.entropy := by
  letI : IsProbabilityMeasure (Measure.map (fun y => (starEdgeProjection d c i).mulVec y) μ) :=
    isProbabilityMeasure_map (measurable_finiteMatrixAction (starEdgeProjection d c i)).aemeasurable
  unfold physicalEdgeWhiteEntropyDensity
  rw [← abs_of_pos (rho_pos c hc), ← physicalEdgeMatrix_det c hc,
    FiniteEntropyDensity.linearPreimage_entropy, FiniteEntropyDensity.cast_entropy]

theorem physicalGaussian_reference_entropy_value
    (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1)
    (chart : physicalStarHyperplane d c ≃ₗ[ℝ] (Fin d → ℝ)) :
    (physicalGaussianStarEntropyDensity d hd c hc chart).entropy -
      (d : ℝ) / 2 * (physicalGaussianEdgeEntropyDensity c hc).entropy =
        Real.log |(physicalStarChartMatrix d hd c hc chart).det| - (d : ℝ) / 2 * Real.log (rho c) := by
  have hf : (physicalGaussianStarEntropyDensity d hd c hc chart).entropy =
      (standardVectorEntropyDensity (Fin d)).entropy +
        Real.log |(physicalStarChartMatrix d hd c hc chart).det| :=
    (standardVectorEntropyDensity (Fin d)).linearImage_entropy _
      (physicalStarChartMatrix_det_ne_zero d hd c hc chart)
  have hg := physicalEdge_entropy_change c hc (standardVectorEntropyDensity Bool)
  change (physicalGaussianEdgeEntropyDensity c hc).entropy =
    (standardVectorEntropyDensity Bool).entropy + Real.log (rho c) at hg
  rw [hf, hg, standardVectorEntropyDensity_entropy, standardVectorEntropyDensity_entropy]
  simp only [gaussianEntropyValue, Fintype.card_fin, Fintype.card_bool, Nat.cast_ofNat, NNReal.coe_one]
  ring

/-- The actual physical Gaussian-relative entropy functional is exactly the
white functional. Every density on the right is constructed by inverse
coordinate transport from the supplied physical density. -/
theorem physicalFrameEntropy_whitening
    (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1)
    (chart : physicalStarHyperplane d c ≃ₗ[ℝ] (Fin d → ℝ))
    {μ : Measure (Fin d → ℝ)} [IsProbabilityMeasure μ]
    (f : FiniteEntropyDensity (Measure.map (fun y => chart (physicalStarEquiv d hd c hc y)) μ))
    (g : ∀ i, FiniteEntropyDensity
      (Measure.map (physicalEdgeCoordinates i) (Measure.map (physicalStarMap d c) μ))) :
    (f.entropy - (1 / 2 : ℝ) * ∑ i, (g i).entropy) -
      ((physicalGaussianStarEntropyDensity d hd c hc chart).entropy -
        (d : ℝ) / 2 * (physicalGaussianEdgeEntropyDensity c hc).entropy) =
      initialFrameEntropy (physicalStarWhiteEntropyDensity d hd c hc chart f)
        (fun i => physicalEdgeWhiteEntropyDensity d c hc i (g i)) := by
  rw [physicalGaussian_reference_entropy_value,
    ← physicalStarWhiteEntropyDensity_entropy d hd c hc chart f]
  simp_rw [← physicalEdgeWhiteEntropyDensity_entropy d c hc]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, initialFrameEntropy]
  ring

/-- The actual physical BS entropy upper bound, in any chosen chart of the
eigenrelation hyperplane. The physical law is parameterized by the proved
bijection L, which loses no laws. All moments, entropy witnesses, and reversal
assumptions belong to the physical laws, and the comparison is with the actual
physical Gaussian image of the independent standard Gaussian.

Choosing an orthonormal chart gives intrinsic Euclidean entropy. The same
inequality holds for every linear chart because its Gaussian-relative
Jacobian cancels. -/
theorem physical_star_entropy_upper
    (d : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (chart : physicalStarHyperplane d c ≃ₗ[ℝ] (Fin d → ℝ))
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hC : HasSecondMoments (Measure.map (physicalStarMap d c) μ)
      (RegularEigenData.starWaveCovariance d ((d : ℝ) * c)))
    (f : FiniteEntropyDensity (Measure.map
      (fun y => chart (physicalStarEquiv d (by omega) c (bulk_rho_lower d hd c hbulk).1 y)) μ))
    (g : ∀ i, FiniteEntropyDensity
      (Measure.map (physicalEdgeCoordinates i) (Measure.map (physicalStarMap d c) μ)))
    (hrev : ∀ i, Measure.map binarySwap
      (Measure.map (physicalEdgeCoordinates i) (Measure.map (physicalStarMap d c) μ)) =
        Measure.map (physicalEdgeCoordinates i) (Measure.map (physicalStarMap d c) μ)) :
    f.entropy - (1 / 2 : ℝ) * ∑ i, (g i).entropy ≤
      (physicalGaussianStarEntropyDensity d (by omega) c (bulk_rho_lower d hd c hbulk).1 chart).entropy -
        (d : ℝ) / 2 * (physicalGaussianEdgeEntropyDensity c (bulk_rho_lower d hd c hbulk).1).entropy := by
  let hd2 : 2 ≤ d := by omega
  let hc := (bulk_rho_lower d hd c hbulk).1
  let A := physicalStarChartMatrix d hd2 c hc chart
  have hA : A.det ≠ 0 := physicalStarChartMatrix_det_ne_zero d hd2 c hc chart
  let M := physicalEdgeMatrix c
  have hM : M.det ≠ 0 := by rw [physicalEdgeMatrix_det c hc]; exact (rho_pos c hc).ne'
  have hchart : Measure.map (fun y => A.mulVec y) μ =
      Measure.map (fun y => chart (physicalStarEquiv d hd2 c hc y)) μ := by
    congr 1
    funext y
    exact physicalStarChartMatrix_mulVec d hd2 c hc chart y
  let fA := f.cast hchart
  let fw := fA.linearPreimage A hA
  let ν := fun i => Measure.map (fun y => (starEdgeProjection d c i).mulVec y) μ
  letI : ∀ i, IsProbabilityMeasure (ν i) :=
    fun i => isProbabilityMeasure_map (measurable_finiteMatrixAction (starEdgeProjection d c i)).aemeasurable
  let gA := fun i => (g i).cast (physicalStarMap_edge_law d c hc i μ).symm
  let gw := fun i => (gA i).linearPreimage M hM
  have hfw : fw.entropy + Real.log |A.det| = f.entropy := by
    simpa only [fw, fA, FiniteEntropyDensity.cast_entropy] using fA.linearPreimage_entropy A hA
  have hgw (i : Fin d) : (gw i).entropy + Real.log (rho c) = (g i).entropy := by
    have h := (gA i).linearPreimage_entropy M hM
    simpa only [gw, gA, M, physicalEdgeMatrix_det c hc, abs_of_pos (rho_pos c hc),
      FiniteEntropyDensity.cast_entropy] using h
  have hwhite := identitySecondMoments_of_physicalStarMap d hd2 c hc μ hC
  have hrevWhite (i : Fin d) : Measure.map binarySwap (ν i) = ν i := by
    apply white_edge_reversal_of_physical c hc (ν i)
    have h := hrev i
    rw [physicalStarMap_edge_law d c hc i μ] at h
    exact h
  have hupper := star_entropy_upper d hd c hbulk μ
    (integrable_squareRadius_of_identitySecondMoments μ hwhite) hwhite fw gw hrevWhite
  have hrefFull : (physicalGaussianStarEntropyDensity d hd2 c hc chart).entropy =
      (standardVectorEntropyDensity (Fin d)).entropy + Real.log |A.det| := by
    exact (standardVectorEntropyDensity (Fin d)).linearImage_entropy A hA
  have hrefEdge : (physicalGaussianEdgeEntropyDensity c hc).entropy =
      (standardVectorEntropyDensity Bool).entropy + Real.log (rho c) := by
    exact physicalEdge_entropy_change c hc (standardVectorEntropyDensity Bool)
  have hGauss : (standardVectorEntropyDensity (Fin d)).entropy -
      (d : ℝ) / 2 * (standardVectorEntropyDensity Bool).entropy = 0 := by
    rw [standardVectorEntropyDensity_entropy, standardVectorEntropyDensity_entropy]
    simp only [gaussianEntropyValue, Fintype.card_fin, Fintype.card_bool, Nat.cast_ofNat, NNReal.coe_one]
    ring
  calc
    _ = (fw.entropy - (1 / 2 : ℝ) * ∑ i, (gw i).entropy) +
        Real.log |A.det| - (d : ℝ) / 2 * Real.log (rho c) := by
      rw [← hfw]
      simp_rw [← hgw]
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      ring
    _ ≤ Real.log |A.det| - (d : ℝ) / 2 * Real.log (rho c) := by linarith
    _ = _ := by rw [hrefFull, hrefEdge]; linarith

/-- The same physical upper bound for an actual probability law on H_lambda,
without supplying a white parameterization. The inverse is the proved
physical whitening equivalence, and every white hypothesis is derived. -/
theorem physical_hyperplane_entropy_upper
    (d : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (chart : physicalStarHyperplane d c ≃ₗ[ℝ] (Fin d → ℝ))
    (N : Measure (physicalStarHyperplane d c)) [IsProbabilityMeasure N]
    (hC : HasSecondMoments (Measure.map (fun z : physicalStarHyperplane d c =>
        (z : Fin (d + 1) → ℝ)) N)
      (RegularEigenData.starWaveCovariance d ((d : ℝ) * c)))
    (f : FiniteEntropyDensity (Measure.map chart N))
    (g : ∀ i, FiniteEntropyDensity (Measure.map (physicalEdgeCoordinates i)
      (Measure.map (fun z : physicalStarHyperplane d c => (z : Fin (d + 1) → ℝ)) N)))
    (hrev : ∀ i, Measure.map binarySwap (Measure.map (physicalEdgeCoordinates i)
      (Measure.map (fun z : physicalStarHyperplane d c => (z : Fin (d + 1) → ℝ)) N)) =
        Measure.map (physicalEdgeCoordinates i)
          (Measure.map (fun z : physicalStarHyperplane d c => (z : Fin (d + 1) → ℝ)) N)) :
    f.entropy - (1 / 2 : ℝ) * ∑ i, (g i).entropy ≤
      (physicalGaussianStarEntropyDensity d (by omega) c (bulk_rho_lower d hd c hbulk).1 chart).entropy -
        (d : ℝ) / 2 * (physicalGaussianEdgeEntropyDensity c (bulk_rho_lower d hd c hbulk).1).entropy := by
  let hd2 : 2 ≤ d := by omega
  let hc := (bulk_rho_lower d hd c hbulk).1
  let E := (physicalStarEquiv d hd2 c hc).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  let μ := Measure.map E.symm N
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_map E.symm.measurable.aemeasurable
  have hN : Measure.map E μ = N := MeasurableEquiv.map_map_symm E
  have hchart : Measure.map (fun y => chart (physicalStarEquiv d hd2 c hc y)) μ =
      Measure.map chart N := by
    rw [← hN]
    have hcm : Measurable (fun z : physicalStarHyperplane d c => chart z) :=
      chart.continuous_of_finiteDimensional.measurable
    exact (Measure.map_map hcm E.measurable).symm
  have hambient : Measure.map (physicalStarMap d c) μ =
      Measure.map (fun z : physicalStarHyperplane d c => (z : Fin (d + 1) → ℝ)) N := by
    rw [← hN, Measure.map_map measurable_subtype_coe E.measurable]
    rfl
  have hCμ : HasSecondMoments (Measure.map (physicalStarMap d c) μ)
      (RegularEigenData.starWaveCovariance d ((d : ℝ) * c)) := by rw [hambient]; exact hC
  let fμ := f.cast hchart
  have hedge (i : Fin d) : Measure.map (physicalEdgeCoordinates i) (Measure.map (physicalStarMap d c) μ) =
      Measure.map (physicalEdgeCoordinates i)
        (Measure.map (fun z : physicalStarHyperplane d c => (z : Fin (d + 1) → ℝ)) N) := by rw [hambient]
  let gμ := fun i => (g i).cast (hedge i)
  have hrevμ (i : Fin d) : Measure.map binarySwap
      (Measure.map (physicalEdgeCoordinates i) (Measure.map (physicalStarMap d c) μ)) =
        Measure.map (physicalEdgeCoordinates i) (Measure.map (physicalStarMap d c) μ) := by
    rw [hedge]
    exact hrev i
  have h := physical_star_entropy_upper d hd c hbulk chart μ hCμ fμ gμ hrevμ
  simpa only [fμ, gμ, FiniteEntropyDensity.cast_entropy] using h

/-- Equality in the physical entropy upper bound identifies the actual
Gaussian wave law. All moments and symmetries are supplied in physical
coordinates; white normalization is derived. -/
theorem physical_star_entropy_equality_iff_standardVector
    (d : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (chart : physicalStarHyperplane d c ≃ₗ[ℝ] (Fin d → ℝ))
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hC : HasSecondMoments (Measure.map (physicalStarMap d c) μ)
      (RegularEigenData.starWaveCovariance d ((d : ℝ) * c)))
    (f : FiniteEntropyDensity (Measure.map
      (fun y => chart (physicalStarEquiv d (by omega) c (bulk_rho_lower d hd c hbulk).1 y)) μ))
    (g : ∀ i, FiniteEntropyDensity
      (Measure.map (physicalEdgeCoordinates i) (Measure.map (physicalStarMap d c) μ)))
    (hrev : ∀ i, Measure.map binarySwap
      (Measure.map (physicalEdgeCoordinates i) (Measure.map (physicalStarMap d c) μ)) =
        Measure.map (physicalEdgeCoordinates i) (Measure.map (physicalStarMap d c) μ))
    (hperm : ∀ p : Equiv.Perm (Fin d), Measure.map (physicalStarPermutation p)
      (Measure.map (physicalStarMap d c) μ) = Measure.map (physicalStarMap d c) μ) :
    (f.entropy - (1 / 2 : ℝ) * ∑ i, (g i).entropy =
      (physicalGaussianStarEntropyDensity d (by omega) c (bulk_rho_lower d hd c hbulk).1 chart).entropy -
        (d : ℝ) / 2 * (physicalGaussianEdgeEntropyDensity c (bulk_rho_lower d hd c hbulk).1).entropy) ↔
      μ = standardVector (Fin d) := by
  let hd2 : 2 ≤ d := by omega
  let hc := (bulk_rho_lower d hd c hbulk).1
  have hwhite := identitySecondMoments_of_physicalStarMap d hd2 c hc μ hC
  have hrevWhite (i : Fin d) : Measure.map binarySwap
      (Measure.map (fun y => (starEdgeProjection d c i).mulVec y) μ) =
      Measure.map (fun y => (starEdgeProjection d c i).mulVec y) μ := by
    apply white_edge_reversal_of_physical c hc
    have h := hrev i
    rw [physicalStarMap_edge_law d c hc i μ] at h
    exact h
  rw [← sub_eq_zero, physicalFrameEntropy_whitening d hd2 c hc chart f g]
  exact star_entropy_equality_iff_standardVector d hd c hbulk μ hwhite
    (physicalStarWhiteEntropyDensity d hd2 c hc chart f)
    (fun i => physicalEdgeWhiteEntropyDensity d c hc i (g i)) hrevWhite
    (white_permutation_of_physical d hd2 c hc μ hperm)

def physicalGaussianHyperplaneLaw (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1) :
    Measure (physicalStarHyperplane d c) :=
  Measure.map (physicalStarEquiv d hd c hc) (standardVector (Fin d))

/-- The full physical equality case for an actual probability measure on the
eigenrelation hyperplane. The Gaussian target is an actual mapped independent
standard Gaussian, and its covariance was computed as the canonical wave
covariance in PhysicalStarMap. -/
theorem physical_hyperplane_entropy_equality_iff_gaussian
    (d : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (chart : physicalStarHyperplane d c ≃ₗ[ℝ] (Fin d → ℝ))
    (N : Measure (physicalStarHyperplane d c)) [IsProbabilityMeasure N]
    (hC : HasSecondMoments (Measure.map (fun z : physicalStarHyperplane d c =>
        (z : Fin (d + 1) → ℝ)) N)
      (RegularEigenData.starWaveCovariance d ((d : ℝ) * c)))
    (f : FiniteEntropyDensity (Measure.map chart N))
    (g : ∀ i, FiniteEntropyDensity (Measure.map (physicalEdgeCoordinates i)
      (Measure.map (fun z : physicalStarHyperplane d c => (z : Fin (d + 1) → ℝ)) N)))
    (hrev : ∀ i, Measure.map binarySwap (Measure.map (physicalEdgeCoordinates i)
      (Measure.map (fun z : physicalStarHyperplane d c => (z : Fin (d + 1) → ℝ)) N)) =
        Measure.map (physicalEdgeCoordinates i)
          (Measure.map (fun z : physicalStarHyperplane d c => (z : Fin (d + 1) → ℝ)) N))
    (hperm : ∀ p : Equiv.Perm (Fin d), Measure.map (physicalStarPermutation p)
      (Measure.map (fun z : physicalStarHyperplane d c => (z : Fin (d + 1) → ℝ)) N) =
        Measure.map (fun z : physicalStarHyperplane d c => (z : Fin (d + 1) → ℝ)) N) :
    (f.entropy - (1 / 2 : ℝ) * ∑ i, (g i).entropy =
      (physicalGaussianStarEntropyDensity d (by omega) c (bulk_rho_lower d hd c hbulk).1 chart).entropy -
        (d : ℝ) / 2 * (physicalGaussianEdgeEntropyDensity c (bulk_rho_lower d hd c hbulk).1).entropy) ↔
      N = physicalGaussianHyperplaneLaw d (by omega) c (bulk_rho_lower d hd c hbulk).1 := by
  let hd2 : 2 ≤ d := by omega
  let hc := (bulk_rho_lower d hd c hbulk).1
  let E := (physicalStarEquiv d hd2 c hc).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  let μ := Measure.map E.symm N
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_map E.symm.measurable.aemeasurable
  have hN : Measure.map E μ = N := MeasurableEquiv.map_map_symm E
  have hchart : Measure.map (fun y => chart (physicalStarEquiv d hd2 c hc y)) μ =
      Measure.map chart N := by
    rw [← hN]
    have hcm : Measurable (fun z : physicalStarHyperplane d c => chart z) :=
      chart.continuous_of_finiteDimensional.measurable
    exact (Measure.map_map hcm E.measurable).symm
  have hambient : Measure.map (physicalStarMap d c) μ =
      Measure.map (fun z : physicalStarHyperplane d c => (z : Fin (d + 1) → ℝ)) N := by
    rw [← hN, Measure.map_map measurable_subtype_coe E.measurable]
    rfl
  have hCμ : HasSecondMoments (Measure.map (physicalStarMap d c) μ)
      (RegularEigenData.starWaveCovariance d ((d : ℝ) * c)) := by rw [hambient]; exact hC
  let fμ := f.cast hchart
  have hedge (i : Fin d) : Measure.map (physicalEdgeCoordinates i) (Measure.map (physicalStarMap d c) μ) =
      Measure.map (physicalEdgeCoordinates i)
        (Measure.map (fun z : physicalStarHyperplane d c => (z : Fin (d + 1) → ℝ)) N) := by rw [hambient]
  let gμ := fun i => (g i).cast (hedge i)
  have hrevμ (i : Fin d) : Measure.map binarySwap
      (Measure.map (physicalEdgeCoordinates i) (Measure.map (physicalStarMap d c) μ)) =
        Measure.map (physicalEdgeCoordinates i) (Measure.map (physicalStarMap d c) μ) := by
    rw [hedge]
    exact hrev i
  have hpermμ (p : Equiv.Perm (Fin d)) : Measure.map (physicalStarPermutation p)
      (Measure.map (physicalStarMap d c) μ) = Measure.map (physicalStarMap d c) μ := by
    rw [hambient]
    exact hperm p
  have h := physical_star_entropy_equality_iff_standardVector d hd c hbulk chart μ hCμ fμ gμ hrevμ hpermμ
  have hlaw : μ = standardVector (Fin d) ↔
      N = physicalGaussianHyperplaneLaw d hd2 c hc := by
    change μ = standardVector (Fin d) ↔ N = Measure.map E (standardVector (Fin d))
    constructor
    · intro hμ
      rw [← hN, hμ]
    · intro hNstd
      apply MeasurableEquiv.map_measurableEquiv_injective E
      rw [hN, hNstd]
  simpa only [fμ, gμ, FiniteEntropyDensity.cast_entropy] using h.trans hlaw

end GaussianWave.BS
