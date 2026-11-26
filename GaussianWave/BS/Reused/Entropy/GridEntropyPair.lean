import GaussianWave.BS.Reused.Entropy.GridEntropy

/-! The actual per-cell two-point entropy bound for the uniform grid. -/
noncomputable section
open MeasureTheory Set Function
open scoped BigOperators ENNReal
namespace GaussianWave.BS.Reused.Entropy
open GaussianWave.BS.Reused.Analysis
variable {I : Type*} [Fintype I]

theorem gridEntropyGap_eq_normalized (a : ℝ) (ha : 0 < a) (f : (I → ℝ) → ℝ)
    (hf : Continuous f) (hpos : ∀ x, 0 < f x) (j : I → ℤ) :
    gridEntropyGap a f j = (a ^ Fintype.card I) *
      ((∫ x, f x * Real.log (f x) ∂gridCellLaw a j) -
        (∫ x, f x ∂gridCellLaw a j) * Real.log (∫ x, f x ∂gridCellLaw a j)) := by
  have hp := gridMass_pos a ha f hf hpos j
  have hv : 0 < a ^ Fintype.card I := pow_pos ha _
  simp_rw [integral_gridCellLaw a ha j]
  change gridEntropyGap a f j = a ^ Fintype.card I *
    ((a ^ Fintype.card I)⁻¹ * (∫ x in gridCell a j, f x * Real.log (f x)) -
      ((a ^ Fintype.card I)⁻¹ * gridMass a f j) * Real.log ((a ^ Fintype.card I)⁻¹ * gridMass a f j))
  rw [Real.log_mul (inv_ne_zero hv.ne') hp.ne', Real.log_inv]
  unfold gridEntropyGap Real.negMulLog
  field_simp
  <;> ring

theorem gridEntropyGap_upper_pair (a : ℝ) (ha : 0 < a) (f : (I → ℝ) → ℝ)
    (hf : Continuous f) (hpos : ∀ x, 0 < f x) (j : I → ℤ) :
    gridEntropyGap a f j ≤ (a ^ Fintype.card I) / 2 *
      ∫ z : (I → ℝ) × (I → ℝ), (f z.1 - f z.2) * (Real.log (f z.1) - Real.log (f z.2))
        ∂(gridCellLaw a j).prod (gridCellLaw a j) := by
  letI := gridCellLaw_probability a ha j
  have hlog : Continuous (fun x => Real.log (f x)) := hf.log (fun x => ne_of_gt (hpos x))
  have hi := integrable_gridCellLaw_of_continuous a ha j f hf
  have hl := integrable_gridCellLaw_of_continuous a ha j _ hlog
  have hfl := integrable_gridCellLaw_of_continuous a ha j _ (hf.mul hlog)
  have hp := integral_pos_of_positive_probability (gridCellLaw a j) f hi hpos
  have hg := (entropy_gap_symmetrized_bound (gridCellLaw a j) f hpos hi hl hfl hp).2
  rw [gridEntropyGap_eq_normalized a ha f hf hpos j]
  convert mul_le_mul_of_nonneg_left hg (show 0 ≤ a ^ Fintype.card I by positivity) using 1 <;> ring

theorem grid_same_cell_difference (a : ℝ) (ha : 0 < a) (x y : I → ℝ)
    (hcell : gridLabel a x = gridLabel a y) (i : I) : |y i - x i| ≤ a := by
  let j := gridLabel a x
  have hx : x ∈ gridCell a j := (mem_gridCell_iff a ha j x).mpr rfl
  have hy : y ∈ gridCell a j := (mem_gridCell_iff a ha j y).mpr hcell.symm
  have hxi : a * (j i : ℝ) ≤ x i ∧ x i < a * ((j i : ℝ) + 1) := (Set.mem_univ_pi.mp hx) i
  have hyi : a * (j i : ℝ) ≤ y i ∧ y i < a * ((j i : ℝ) + 1) := (Set.mem_univ_pi.mp hy) i
  exact abs_le.mpr ⟨by nlinarith [hxi.2, hyi.1], by nlinarith [hyi.2, hxi.1]⟩

theorem symmetrized_log_nonneg (f g : ℝ) (hf : 0 < f) (hg : 0 < g) :
    0 ≤ (f - g) * (Real.log f - Real.log g) := by
  by_cases h : f ≤ g
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h)
      (sub_nonpos.mpr (Real.log_le_log hf h))
  · have hh : g ≤ f := le_of_lt (lt_of_not_ge h)
    exact mul_nonneg (sub_nonneg.mpr hh) (sub_nonneg.mpr (Real.log_le_log hg hh))

end GaussianWave.BS.Reused.Entropy
