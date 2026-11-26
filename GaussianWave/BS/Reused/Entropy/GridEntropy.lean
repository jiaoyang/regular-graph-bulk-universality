import GaussianWave.BS.Reused.Entropy.GridCells
import GaussianWave.BS.Reused.Entropy.CountableShannon
import GaussianWave.BS.Reused.Analysis.EntropyJensen

/-! The genuine cellwise entropy identity for the countable uniform grid. -/
noncomputable section
open MeasureTheory Set Function
open scoped BigOperators ENNReal
namespace GaussianWave.BS.Reused.Entropy
open GaussianWave.BS.Reused.Analysis
variable {I : Type*} [Fintype I]

def gridMass (a : ℝ) (f : (I → ℝ) → ℝ) (j : I → ℤ) : ℝ := ∫ x in gridCell a j, f x

def gridEntropyGap (a : ℝ) (f : (I → ℝ) → ℝ) (j : I → ℤ) : ℝ :=
  (∫ x in gridCell a j, f x * Real.log (f x)) + Real.negMulLog (gridMass a f j) +
    gridMass a f j * Real.log (a ^ Fintype.card I)

theorem integral_gridCellLaw (a : ℝ) (ha : 0 < a) (j : I → ℤ) (f : (I → ℝ) → ℝ) :
    (∫ x, f x ∂gridCellLaw a j) = (a ^ Fintype.card I)⁻¹ * ∫ x in gridCell a j, f x := by
  rw [gridCellLaw, integral_smul_measure]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofReal ha.le, smul_eq_mul]

theorem gridCell_subset_Icc (a : ℝ) (j : I → ℤ) :
    gridCell a j ⊆ Set.Icc (fun i => a * (j i : ℝ)) (fun i => a * ((j i : ℝ) + 1)) := by
  intro x hx
  have hh : ∀ i, a * (j i : ℝ) ≤ x i ∧ x i < a * ((j i : ℝ) + 1) := by
    simpa only [gridCell, Set.mem_univ_pi, Set.mem_Ico] using hx
  exact ⟨fun i => (hh i).1, fun i => (hh i).2.le⟩

theorem integrable_gridCellLaw_of_continuous (a : ℝ) (ha : 0 < a) (j : I → ℤ)
    (f : (I → ℝ) → ℝ) (hf : Continuous f) : Integrable f (gridCellLaw a j) := by
  have hi : IntegrableOn f (gridCell a j) := hf.continuousOn.integrableOn_Icc.mono_set (gridCell_subset_Icc a j)
  apply (integrable_smul_measure (ENNReal.inv_ne_zero.mpr
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))
    (ENNReal.inv_ne_top.mpr (pow_ne_zero _ (ne_of_gt (ENNReal.ofReal_pos.mpr ha))))).mpr hi

theorem integral_pos_of_positive_probability {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → ℝ) (hf : Integrable f μ)
    (hpos : ∀ x, 0 < f x) : 0 < ∫ x, f x ∂μ := by
  apply (integral_pos_iff_support_of_nonneg_ae (ae_of_all μ (fun x => (hpos x).le)) hf).mpr
  have hs : Function.support f = Set.univ := by
    ext x
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact ne_of_gt (hpos x)
  rw [hs, measure_univ]
  exact zero_lt_one

theorem gridMass_pos (a : ℝ) (ha : 0 < a) (f : (I → ℝ) → ℝ) (hf : Continuous f)
    (hpos : ∀ x, 0 < f x) (j : I → ℤ) : 0 < gridMass a f j := by
  letI := gridCellLaw_probability a ha j
  have h := integral_pos_of_positive_probability (gridCellLaw a j) f
    (integrable_gridCellLaw_of_continuous a ha j f hf) hpos
  rw [integral_gridCellLaw a ha j f] at h
  change 0 < (a ^ Fintype.card I)⁻¹ * gridMass a f j at h
  exact (mul_pos_iff.mp h).resolve_right (by intro hh; exact (not_lt_of_ge (by positivity)) hh.1) |>.2

theorem gridEntropyGap_nonneg (a : ℝ) (ha : 0 < a) (f : (I → ℝ) → ℝ)
    (hf : Continuous f) (hpos : ∀ x, 0 < f x) (j : I → ℤ) : 0 ≤ gridEntropyGap a f j := by
  letI := gridCellLaw_probability a ha j
  have hp := gridMass_pos a ha f hf hpos j
  have hlog : Continuous (fun x => Real.log (f x)) := hf.log (fun x => ne_of_gt (hpos x))
  have hmean := integral_pos_of_positive_probability (gridCellLaw a j) f
    (integrable_gridCellLaw_of_continuous a ha j f hf) hpos
  have hg := entropy_gap_nonneg (gridCellLaw a j) f hpos
    (integrable_gridCellLaw_of_continuous a ha j f hf)
    (integrable_gridCellLaw_of_continuous a ha j _ (hf.mul hlog)) hmean
  simp_rw [integral_gridCellLaw a ha j] at hg
  have hv : 0 < a ^ Fintype.card I := pow_pos ha _
  have he : Real.log ((a ^ Fintype.card I)⁻¹ * gridMass a f j) =
      Real.log (gridMass a f j) - Real.log (a ^ Fintype.card I) := by
    rw [Real.log_mul (inv_ne_zero hv.ne') hp.ne', Real.log_inv]
    ring
  change 0 ≤ (a ^ Fintype.card I)⁻¹ * (∫ x in gridCell a j, f x * Real.log (f x)) -
    ((a ^ Fintype.card I)⁻¹ * gridMass a f j) * Real.log ((a ^ Fintype.card I)⁻¹ * gridMass a f j) at hg
  rw [he] at hg
  have hm := mul_nonneg hv.le hg
  unfold gridEntropyGap Real.negMulLog
  dsimp only [gridMass] at hm ⊢
  field_simp at hm
  rw [Real.log_pow]
  nlinarith

theorem gridMass_hasSum (a : ℝ) (ha : 0 < a) (f : (I → ℝ) → ℝ) (hf : Integrable f)
    (hnorm : ∫ x, f x = 1) : HasSum (gridMass a f) 1 := by
  simpa only [gridMass, hnorm] using hasSum_gridCell_integral a ha f hf

theorem gridEntropyGap_hasSum (a : ℝ) (ha : 0 < a) (f : (I → ℝ) → ℝ)
    (hf : Integrable f) (hflog : Integrable (fun x => f x * Real.log (f x))) (hnorm : ∫ x, f x = 1)
    (hH : Summable (fun j => Real.negMulLog (gridMass a f j))) :
    HasSum (gridEntropyGap a f)
      (countableEntropy (gridMass a f) + (Fintype.card I : ℝ) * Real.log a + ∫ x, f x * Real.log (f x)) := by
  have h1 := hasSum_gridCell_integral a ha (fun x => f x * Real.log (f x)) hflog
  have h2 := hH.hasSum
  have h3 := (gridMass_hasSum a ha f hf hnorm).mul_right (Real.log (a ^ Fintype.card I))
  have h := (h1.add h2).add h3
  change HasSum (fun j => (∫ x in gridCell a j, f x * Real.log (f x)) +
    Real.negMulLog (gridMass a f j) + gridMass a f j * Real.log (a ^ Fintype.card I)) _
  simpa only [countableEntropy, Real.log_pow, one_mul, add_comm, add_left_comm, add_assoc] using h

end GaussianWave.BS.Reused.Entropy
