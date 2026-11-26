import GaussianWave.BS.Lower.DifferentialEntropyTransfer
import GaussianWave.BS.IntrinsicHeatDecomposition

/-! The finite-alphabet graph inequality yields a genuine intrinsic entropy
lower bound on any proved eigen-solution support. Gaussian normal entropy
cancels by the exact dimensions, and actual time-zero recovery finishes. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology Classical
namespace GaussianWave.BS.Lower

private theorem orthonormal_rows_card_le
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (O : Matrix J I ℝ) (hO : O * O.transpose = 1) : Fintype.card J ≤ Fintype.card I := by
  let row : J → EuclideanSpace ℝ I := fun j => (WithLp.equiv 2 (I → ℝ)).symm (O j)
  have hr : Orthonormal ℝ row := by
    rw [orthonormal_iff_ite]
    intro j k
    have h := congrArg (fun M : Matrix J J ℝ => M j k) hO
    simpa [row, EuclideanSpace.inner_piLp_equiv_symm, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.one_apply, dotProduct, mul_comm] using h
  simpa using hr.linearIndependent.fintype_card_le_finrank

variable {V W C E : Type*} [Fintype V] [Fintype W] [Fintype C] [Fintype E]
  [DecidableEq V] [DecidableEq W] [DecidableEq C] [DecidableEq E] {r : ℕ}

/-- Actual intrinsic smoothed entropy is nonnegative after normal Gaussian
cancellation. The sole entropy input is the discrete recoloring theorem. -/
theorem intrinsic_heat_entropy_nonneg_of_finite_recoloring
    (μC : Measure ((V × Fin r) → ℝ)) [IsProbabilityMeasure μC]
    (μE : Measure ((W × Fin r) → ℝ)) [IsProbabilityMeasure μE]
    (μo : Measure (Fin r → ℝ)) [IsProbabilityMeasure μo]
    (hC : Integrable (squareRadius (I := V × Fin r)) μC)
    (hE : Integrable (squareRadius (I := W × Fin r)) μE) (w : ℝ)
    (hdim : (Fintype.card V : ℝ) - w * Fintype.card W = 1)
    (hfinite : HasFiniteRecoloringEntropyLower μC μE μo w)
    (OC : Matrix C (V × Fin r) ℝ) (hOC : OC * OC.transpose = 1)
    (OE : Matrix E (W × Fin r) ℝ) (hOE : OE * OE.transpose = 1)
    (hsC : ∀ᵐ x ∂μC, OC.transpose.mulVec (OC.mulVec x) = x)
    (hsE : ∀ᵐ x ∂μE, OE.transpose.mulVec (OE.mulVec x) = x)
    (hdim_intrinsic : (Fintype.card C : ℝ) - w * Fintype.card E = 0)
    {t : ℝ} (ht : 0 < t) :
    0 ≤ densityEntropy volume (heatDensity (Measure.map OC.mulVec μC) t) -
      w * densityEntropy volume (heatDensity (Measure.map OE.mulVec μE) t) := by
  have hc := orthonormal_rows_card_le OC hOC
  have he := orthonormal_rows_card_le OE hOE
  have hnormal : ((Fintype.card (V × Fin r) - Fintype.card C : ℕ) : ℝ) -
      w * ((Fintype.card (W × Fin r) - Fintype.card E : ℕ) : ℝ) = r := by
    rw [Nat.cast_sub hc, Nat.cast_sub he]
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    nlinarith [congrArg (fun x : ℝ => x * (r : ℝ)) hdim]
  have hg : gaussianEntropyValue (Fin (Fintype.card (V × Fin r) - Fintype.card C)) (heatVariance t) -
      w * gaussianEntropyValue (Fin (Fintype.card (W × Fin r) - Fintype.card E)) (heatVariance t) =
        gaussianEntropyValue (Fin r) (heatVariance t) := by
    unfold gaussianEntropyValue
    simp only [Fintype.card_fin]
    have h := congrArg (fun x : ℝ => x / 2 * (Real.log (2 * Real.pi * (heatVariance t : ℝ)) + 1)) hnormal
    nlinarith
  have h := heat_entropy_lower_of_finite_recoloring μC μE μo hC hE w hdim hfinite ht
  rw [heatDensity_entropy_orthonormal_support μC hC OC hOC hsC ht,
    heatDensity_entropy_orthonormal_support μE hE OE hOE hsE ht] at h
  nlinarith

/-- Source Theorem 8.1's analytic implication, for full joint vector colors
and proved intrinsic support charts. Finite entropy is an ordinary density
hypothesis; no differential-entropy lower bound is supplied by the caller. -/
theorem intrinsic_entropy_nonneg_of_finite_recoloring
    (μC : Measure ((V × Fin r) → ℝ)) [IsProbabilityMeasure μC]
    (μE : Measure ((W × Fin r) → ℝ)) [IsProbabilityMeasure μE]
    (μo : Measure (Fin r → ℝ)) [IsProbabilityMeasure μo]
    (hC : Integrable (squareRadius (I := V × Fin r)) μC)
    (hE : Integrable (squareRadius (I := W × Fin r)) μE) (w : ℝ)
    (hdim : (Fintype.card V : ℝ) - w * Fintype.card W = 1)
    (hfinite : HasFiniteRecoloringEntropyLower μC μE μo w)
    (OC : Matrix C (V × Fin r) ℝ) (hOC : OC * OC.transpose = 1)
    (OE : Matrix E (W × Fin r) ℝ) (hOE : OE * OE.transpose = 1)
    (hsC : ∀ᵐ x ∂μC, OC.transpose.mulVec (OC.mulVec x) = x)
    (hsE : ∀ᵐ x ∂μE, OE.transpose.mulVec (OE.mulVec x) = x)
    (hdim_intrinsic : (Fintype.card C : ℝ) - w * Fintype.card E = 0)
    (fC : FiniteEntropyDensity (Measure.map OC.mulVec μC))
    (fE : FiniteEntropyDensity (Measure.map OE.mulVec μE)) :
    0 ≤ fC.entropy - w * fE.entropy := by
  let νC := Measure.map OC.mulVec μC
  let νE := Measure.map OE.mulVec μE
  letI : IsProbabilityMeasure νC := isProbabilityMeasure_map (measurable_finiteMatrixAction OC).aemeasurable
  letI : IsProbabilityMeasure νE := isProbabilityMeasure_map (measurable_finiteMatrixAction OE).aemeasurable
  have hνC := integrable_squareRadius_matrixImage μC hC OC
  have hνE := integrable_squareRadius_matrixImage μE hE OE
  have hlimC := tendsto_heatDensity_entropy_zero νC fC.density fC.measurable fC.nonneg fC.integrable
    fC.integral_eq_one fC.integrable_log fC.measure_eq hνC
  have hlimE := tendsto_heatDensity_entropy_zero νE fE.density fE.measurable fE.nonneg fE.integrable
    fE.integral_eq_one fE.integrable_log fE.measure_eq hνE
  apply le_of_tendsto_of_tendsto tendsto_const_nhds (hlimC.sub (hlimE.const_mul w))
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact intrinsic_heat_entropy_nonneg_of_finite_recoloring μC μE μo hC hE w hdim hfinite
    OC hOC OE hOE hsC hsE hdim_intrinsic ht
end GaussianWave.BS.Lower
