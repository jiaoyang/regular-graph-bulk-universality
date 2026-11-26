import GaussianWave.BS.Reused.Entropy.GridTranslation

/-! Conversion of normalized cell-pair integrals to the actual Lebesgue pair region. -/
noncomputable section
open MeasureTheory Set Function
open scoped BigOperators ENNReal
namespace GaussianWave.BS.Reused.Entropy
open GaussianWave.BS.Reused.Analysis
variable {I : Type*} [Fintype I]

theorem integrable_gridCell_prod_of_continuous (a : ℝ) (j : I → ℤ)
    (Φ : ((I → ℝ) × (I → ℝ)) → ℝ) (hΦ : Continuous Φ) :
    Integrable Φ ((volume.restrict (gridCell a j)).prod (volume.restrict (gridCell a j))) := by
  rw [Measure.prod_restrict]
  let K := Set.Icc (fun i => a * (j i : ℝ)) (fun i => a * ((j i : ℝ) + 1))
  have hK : IsCompact K := isCompact_Icc
  apply (hΦ.continuousOn.integrableOn_compact (hK.prod hK)).mono_set
  intro z hz
  exact ⟨gridCell_subset_Icc a j hz.1, gridCell_subset_Icc a j hz.2⟩

theorem integral_gridCellLaw_prod (a : ℝ) (ha : 0 < a) (j : I → ℤ)
    (Φ : ((I → ℝ) × (I → ℝ)) → ℝ)
    (hInt : Integrable Φ ((gridCellLaw a j).prod (gridCellLaw a j)))
    (hCell : Integrable Φ ((volume.restrict (gridCell a j)).prod (volume.restrict (gridCell a j)))) :
    (∫ z, Φ z ∂(gridCellLaw a j).prod (gridCellLaw a j)) =
      (a ^ Fintype.card I)⁻¹ ^ 2 * ∫ z in gridCell a j ×ˢ gridCell a j, Φ z ∂volume.prod volume := by
  letI := gridCellLaw_probability a ha j
  rw [integral_prod Φ hInt, integral_gridCellLaw a ha j]
  simp_rw [integral_gridCellLaw a ha j]
  rw [integral_const_mul]
  have h := integral_prod Φ hCell
  rw [Measure.prod_restrict] at h
  rw [← h]
  ring

theorem gridEntropyGap_upper_lebesgue_pair (a : ℝ) (ha : 0 < a) (f : (I → ℝ) → ℝ)
    (hf : Continuous f) (hpos : ∀ x, 0 < f x) (j : I → ℤ) :
    gridEntropyGap a f j ≤ ((2 * a ^ Fintype.card I)⁻¹) *
      ∫ z in gridCell a j ×ˢ gridCell a j,
        (f z.1 - f z.2) * (Real.log (f z.1) - Real.log (f z.2)) ∂volume.prod volume := by
  letI := gridCellLaw_probability a ha j
  have hlog : Continuous (fun x => Real.log (f x)) := hf.log (fun x => ne_of_gt (hpos x))
  have hS : Continuous (fun z : (I → ℝ) × (I → ℝ) =>
      (f z.1 - f z.2) * (Real.log (f z.1) - Real.log (f z.2))) :=
    ((hf.comp continuous_fst).sub (hf.comp continuous_snd)).mul
      ((hlog.comp continuous_fst).sub (hlog.comp continuous_snd))
  have hi := integrable_gridCellLaw_of_continuous a ha j f hf
  have hl := integrable_gridCellLaw_of_continuous a ha j _ hlog
  have hfl := integrable_gridCellLaw_of_continuous a ha j _ (hf.mul hlog)
  have hpair := (integral_symmetrized_entropy (gridCellLaw a j) f hi hl hfl).1
  have hcell := integrable_gridCell_prod_of_continuous a j _ hS
  have hg := gridEntropyGap_upper_pair a ha f hf hpos j
  rw [integral_gridCellLaw_prod a ha j _ hpair hcell] at hg
  have hv : a ^ Fintype.card I ≠ 0 := ne_of_gt (pow_pos ha _)
  convert hg using 1
  field_simp
  <;> ring

end GaussianWave.BS.Reused.Entropy
