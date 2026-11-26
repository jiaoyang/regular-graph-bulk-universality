import GaussianWave.BS.Reused.Entropy.GridPairIntegral

/-! Summing genuine cellwise entropy errors and bounding them by translation entropy. -/
noncomputable section
open MeasureTheory Set Function
open scoped BigOperators ENNReal
namespace GaussianWave.BS.Reused.Entropy
open GaussianWave.BS.Reused.Analysis
variable {I : Type*} [Fintype I]

def symmetrizedDensityPair (f : (I → ℝ) → ℝ) (z : (I → ℝ) × (I → ℝ)) : ℝ :=
  (f z.1 - f z.2) * (Real.log (f z.1) - Real.log (f z.2))

theorem continuous_symmetrizedDensityPair (f : (I → ℝ) → ℝ) (hf : Continuous f) (hp : ∀ x, 0 < f x) :
    Continuous (symmetrizedDensityPair f) := by
  have hl : Continuous (fun x => Real.log (f x)) := hf.log (fun x => (hp x).ne')
  exact ((hf.comp continuous_fst).sub (hf.comp continuous_snd)).mul
    ((hl.comp continuous_fst).sub (hl.comp continuous_snd))

theorem symmetrizedDensityPair_nonneg (f : (I → ℝ) → ℝ) (hp : ∀ x, 0 < f x)
    (z : (I → ℝ) × (I → ℝ)) : 0 ≤ symmetrizedDensityPair f z :=
  symmetrized_log_nonneg _ _ (hp _) (hp _)

theorem volume_gridShiftBox (a : ℝ) :
    volume (gridShiftBox (I := I) a) = ENNReal.ofReal (2 * a) ^ Fintype.card I := by
  rw [gridShiftBox, Real.volume_Icc_pi]
  simp only [sub_neg_eq_add, ← two_mul, Finset.prod_const, Finset.card_univ]

theorem lintegral_translation_bound (a : ℝ) (ha : 0 < a) (f : (I → ℝ) → ℝ)
    (hp : ∀ x, 0 < f x) (C : ℝ) (hC : 0 ≤ C)
    (hInt : ∀ h, Integrable (fun x => symmetrizedDensityPair f (x, x + h)))
    (hbound : ∀ h, (∫ x, symmetrizedDensityPair f (x, x + h)) ≤ C * ∑ i, h i ^ 2) :
    (∫⁻ h in gridShiftBox a, ∫⁻ x, ENNReal.ofReal (symmetrizedDensityPair f (x, x + h))) ≤
      ENNReal.ofReal (C * Fintype.card I * a ^ 2) * ENNReal.ofReal (2 * a) ^ Fintype.card I := by
  calc
    _ ≤ ∫⁻ _h in gridShiftBox a, ENNReal.ofReal (C * Fintype.card I * a ^ 2) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (show MeasurableSet (gridShiftBox (I := I) a) from measurableSet_Icc)] with h hh
      rw [← ofReal_integral_eq_lintegral_ofReal (hInt h)
        (ae_of_all _ (fun x => symmetrizedDensityPair_nonneg f hp (x,x+h)))]
      apply ENNReal.ofReal_le_ofReal
      refine (hbound h).trans ?_
      have hs : (∑ i, h i ^ 2) ≤ (Fintype.card I : ℝ) * a ^ 2 := by
        calc
          _ ≤ ∑ _i : I, a ^ 2 := by
            apply Finset.sum_le_sum
            intro i hi
            have hab : |h i| ≤ a := abs_le.mpr ⟨hh.1 i, hh.2 i⟩
            simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hab 2
          _ = _ := by simp
      nlinarith [mul_le_mul_of_nonneg_left hs hC]
    _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ, volume_gridShiftBox]

theorem grid_entropy_error_bound (a : ℝ) (ha : 0 < a) (f : (I → ℝ) → ℝ)
    (hf : Continuous f) (hp : ∀ x, 0 < f x) (hi : Integrable f)
    (hflog : Integrable (fun x => f x * Real.log (f x))) (hnorm : ∫ x, f x = 1)
    (hH : Summable (fun j => Real.negMulLog (gridMass a f j)))
    (C : ℝ) (hC : 0 ≤ C)
    (hInt : ∀ h, Integrable (fun x => symmetrizedDensityPair f (x, x + h)))
    (hbound : ∀ h, (∫ x, symmetrizedDensityPair f (x, x + h)) ≤ C * ∑ i, h i ^ 2) :
    0 ≤ countableEntropy (gridMass a f) + (Fintype.card I : ℝ) * Real.log a + ∫ x, f x * Real.log (f x) ∧
    countableEntropy (gridMass a f) + (Fintype.card I : ℝ) * Real.log a + ∫ x, f x * Real.log (f x) ≤
      (2 * a ^ Fintype.card I)⁻¹ * (C * Fintype.card I * a ^ 2) * (2 * a) ^ Fintype.card I := by
  let gap := gridEntropyGap a f
  let Φ := fun z : (I → ℝ) × (I → ℝ) => ENNReal.ofReal (symmetrizedDensityPair f z)
  let coeff : ℝ := (2 * a ^ Fintype.card I)⁻¹
  have hcoeff : 0 ≤ coeff := by dsimp [coeff]; positivity
  have hΦ : Measurable Φ := (continuous_symmetrizedDensityPair f hf hp).measurable.ennreal_ofReal
  have hgap := gridEntropyGap_hasSum a ha f hi hflog hnorm hH
  have hn (j : I → ℤ) : 0 ≤ gap j := gridEntropyGap_nonneg a ha f hf hp j
  have hj (j : I → ℤ) : ENNReal.ofReal (gap j) ≤ ENNReal.ofReal coeff *
      ∫⁻ z in gridCell a j ×ˢ gridCell a j, Φ z ∂volume.prod volume := by
    have hCell := integrable_gridCell_prod_of_continuous a j _ (continuous_symmetrizedDensityPair f hf hp)
    rw [Measure.prod_restrict] at hCell
    change ENNReal.ofReal (gap j) ≤ ENNReal.ofReal coeff *
      ∫⁻ z in gridCell a j ×ˢ gridCell a j, ENNReal.ofReal (symmetrizedDensityPair f z) ∂volume.prod volume
    rw [← ofReal_integral_eq_lintegral_ofReal hCell (ae_of_all _ (symmetrizedDensityPair_nonneg f hp)),
      ← ENNReal.ofReal_mul hcoeff]
    exact ENNReal.ofReal_le_ofReal (gridEntropyGap_upper_lebesgue_pair a ha f hf hp j)
  have he : (∑' j, gap j) = countableEntropy (gridMass a f) + (Fintype.card I : ℝ) * Real.log a +
      ∫ x, f x * Real.log (f x) := hgap.tsum_eq
  refine ⟨by rw [← he]; exact tsum_nonneg hn, ?_⟩
  have hb : ENNReal.ofReal (∑' j, gap j) ≤ ENNReal.ofReal coeff *
      (ENNReal.ofReal (C * Fintype.card I * a ^ 2) * ENNReal.ofReal (2 * a) ^ Fintype.card I) := by
    calc
      _ = ∑' j, ENNReal.ofReal (gap j) := ENNReal.ofReal_tsum_of_nonneg hn hgap.summable
      _ ≤ ∑' j, ENNReal.ofReal coeff * ∫⁻ z in gridCell a j ×ˢ gridCell a j, Φ z ∂volume.prod volume :=
        ENNReal.tsum_le_tsum hj
      _ = ENNReal.ofReal coeff * ∫⁻ z in sameGridPair a, Φ z ∂volume.prod volume := by
        rw [ENNReal.tsum_mul_left, lintegral_sameGridPair_eq_tsum a ha]
      _ ≤ ENNReal.ofReal coeff * ∫⁻ h in gridShiftBox a, ∫⁻ x, Φ (x,x+h) :=
        mul_le_mul_left' (lintegral_sameGridPair_le_translations a ha Φ hΦ) _
      _ ≤ _ := mul_le_mul_left' (lintegral_translation_bound a ha f hp C hC hInt hbound) _
  have hreal : ENNReal.ofReal coeff *
      (ENNReal.ofReal (C * Fintype.card I * a ^ 2) * ENNReal.ofReal (2 * a) ^ Fintype.card I) =
      ENNReal.ofReal (coeff * (C * Fintype.card I * a ^ 2) * (2 * a) ^ Fintype.card I) := by
    rw [ENNReal.ofReal_mul (mul_nonneg hcoeff (by positivity)), ENNReal.ofReal_mul hcoeff,
      ENNReal.ofReal_pow (by positivity : 0 ≤ 2 * a)]
    simp only [mul_assoc]
  rw [hreal, he] at hb
  have hK : 0 ≤ coeff * (C * Fintype.card I * a ^ 2) * (2 * a) ^ Fintype.card I := by positivity
  exact (ENNReal.ofReal_le_ofReal_iff hK).mp hb

end GaussianWave.BS.Reused.Entropy
