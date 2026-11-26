import GeneralizedBulk.Analysis.UpperHalfNormalization

/-! Normalization at imaginary infinity forces infinitely many particles. -/
noncomputable section
open MeasureTheory BourgadeHuang Filter
open scoped Topology ENNReal
namespace GeneralizedBulk.Analysis

/-- A finite-mass state without an affine term has Poisson height at most
its total mass divided by the spectral height. -/
theorem anchored_height_le_totalMass_div
    (s : AnchoredCountingState) (hlinear : anchoredLinearCoefficient s = 0)
    (K Y : ℝ) (hK0 : 0 ≤ K) (hK : s.val.1.measure Set.univ ≤ ENNReal.ofReal K) (hY : 0 < Y) :
    (anchoredNevanlinna s ((Y : ℂ) * Complex.I)).im ≤ K / Y := by
  have hfinite : s.val.1.measure Set.univ ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hK
  letI : IsFiniteMeasure s.val.1.measure := ⟨hfinite.lt_top⟩
  have hz : (((Y : ℂ) * Complex.I)).im ≠ 0 := by simpa using ne_of_gt hY
  have hi : Integrable (fun a : ℝ => (((Y : ℂ) * Complex.I)).im /
      Complex.normSq ((a : ℂ) - ((Y : ℂ) * Complex.I))) s.val.1.measure := by
    have hh := (integrable_regularizedResolventKernel s hz).im
    change Integrable (fun a => (regularizedResolventKernel ((Y : ℂ) * Complex.I) a).im)
      s.val.1.measure at hh
    simpa only [regularizedResolventKernel_im] using hh
  have hp (a : ℝ) : (((Y : ℂ) * Complex.I)).im /
      Complex.normSq ((a : ℂ) - ((Y : ℂ) * Complex.I)) ≤ Y⁻¹ := by
    have hden : 0 < a ^ 2 + Y ^ 2 := by nlinarith [sq_nonneg a]
    have heq : Complex.normSq ((a : ℂ) - ((Y : ℂ) * Complex.I)) = a ^ 2 + Y ^ 2 := by
      simp [Complex.normSq_apply, pow_two]
    rw [heq]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_im,
      Complex.I_re, mul_one, zero_mul, add_zero]
    rw [inv_eq_one_div, div_le_div_iff₀ hden hY]
    nlinarith [sq_nonneg a]
  rw [anchoredNevanlinna_im_eq s hz, hlinear, mul_zero, zero_add]
  calc
    _ ≤ ∫ _ : ℝ, Y⁻¹ ∂s.val.1.measure := integral_mono hi (integrable_const _) hp
    _ = (s.val.1.measure Set.univ).toReal * Y⁻¹ := by
      rw [integral_const, smul_eq_mul]
      rfl
    _ ≤ K * Y⁻¹ := by
      apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hY.le)
      simpa only [ENNReal.toReal_ofReal hK0] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hK
    _ = K / Y := by ring

/-- The total-mass events are measurable for the actual vague counting-state
space, including the value infinity. -/
theorem measurable_anchored_totalMass :
    Measurable (fun s : AnchoredCountingState => s.val.1.measure Set.univ) :=
  (LocalCountingMeasure.measurable_mass MeasurableSet.univ).comp
    (measurable_fst.comp measurable_subtype_coe)

/-- L1 normalization at imaginary infinity excludes every finite particle
count, without any integrability assumption on the total particle number. -/
theorem anchored_totalMass_eq_top_ae_of_normalization
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hm : Integrable (fun s : AnchoredCountingState => ‖s.val.2‖) ν)
    (hlinear : ∀ᵐ s ∂ν, anchoredLinearCoefficient s = 0)
    (hnormal : Tendsto (fun n : ℕ => ∫ s,
      ‖anchoredNevanlinna s ((((n : ℝ) + 1 : ℝ) : ℂ) * Complex.I) - Complex.I‖ ∂ν)
      atTop (𝓝 0)) :
    ∀ᵐ s ∂ν, s.val.1.measure Set.univ = ∞ := by
  classical
  have hnull (K : ℕ) : ν {s : AnchoredCountingState | s.val.1.measure Set.univ ≤ K} = 0 := by
    let A := {s : AnchoredCountingState | s.val.1.measure Set.univ ≤ K}
    have hA : MeasurableSet A := measurable_anchored_totalMass measurableSet_Iic
    have hbound (n : ℕ) : (1 - (K : ℝ) / ((n : ℝ) + 1)) * ν.real A ≤
        ∫ s, ‖anchoredNevanlinna s ((((n : ℝ) + 1 : ℝ) : ℂ) * Complex.I) - Complex.I‖ ∂ν := by
      have hY : 0 < (n : ℝ) + 1 := by positivity
      have hw : (((((n : ℝ) + 1 : ℝ) : ℂ) * Complex.I)).im ≠ 0 := by simpa using ne_of_gt hY
      have hi := (integrable_scalar_norm_of_anchor ν id measurable_id hm hw)
      have hdiff : Integrable (fun s => ‖anchoredNevanlinna s
          ((((n : ℝ) + 1 : ℝ) : ℂ) * Complex.I) - Complex.I‖) ν := by
        apply (hi.add (integrable_const 1)).mono'
          (((continuous_anchoredNevanlinna hw).measurable.sub_const Complex.I).norm).aestronglyMeasurable
        filter_upwards [] with s
        rw [norm_norm]
        simpa only [Complex.norm_I] using norm_sub_le (anchoredNevanlinna s
          ((((n : ℝ) + 1 : ℝ) : ℂ) * Complex.I)) Complex.I
      have hpoint : ∀ᵐ s ∂ν, A.indicator (fun _ => 1 - (K : ℝ) / ((n : ℝ) + 1)) s ≤
          ‖anchoredNevanlinna s ((((n : ℝ) + 1 : ℝ) : ℂ) * Complex.I) - Complex.I‖ := by
        filter_upwards [hlinear] with s hs
        by_cases hmem : s ∈ A
        · rw [Set.indicator_of_mem hmem]
          have hh := anchored_height_le_totalMass_div s hs K ((n : ℝ) + 1) (Nat.cast_nonneg K)
            (by simpa only [ENNReal.ofReal_natCast] using hmem) hY
          have habs := Complex.abs_im_le_norm (anchoredNevanlinna s
            ((((n : ℝ) + 1 : ℝ) : ℂ) * Complex.I) - Complex.I)
          simp only [Complex.sub_im, Complex.I_im] at habs
          linarith [neg_abs_le ((anchoredNevanlinna s
            ((((n : ℝ) + 1 : ℝ) : ℂ) * Complex.I)).im - 1)]
        · rw [Set.indicator_of_not_mem hmem]
          exact norm_nonneg _
      have h := integral_mono_ae ((integrable_const _).indicator hA) hdiff hpoint
      rw [integral_indicator_const _ hA, smul_eq_mul] at h
      simpa only [mul_comm] using h
    have hfactor : Tendsto (fun n : ℕ => (1 - (K : ℝ) / ((n : ℝ) + 1)) * ν.real A)
        atTop (𝓝 (ν.real A)) := by
      have hdiv : Tendsto (fun n : ℕ => (K : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
        simpa only [mul_one_div, mul_zero] using
          tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat (a := (K : ℝ))
      simpa only [sub_zero, one_mul] using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hdiv).mul_const (ν.real A)
    have hz : ν.real A = 0 := le_antisymm
      (le_of_tendsto_of_tendsto hfactor hnormal (Eventually.of_forall hbound)) measureReal_nonneg
    exact (measureReal_eq_zero_iff (measure_ne_top _ _)).mp hz
  have hall : ∀ᵐ s ∂ν, ∀ K : ℕ, ¬(s.val.1.measure Set.univ ≤ (K : ℝ≥0∞)) := by
    apply ae_all_iff.mpr
    intro K
    apply ae_iff.mpr
    simpa only [not_not] using hnull K
  filter_upwards [hall] with s hs
  by_contra hfinite
  obtain ⟨K,hK⟩ := exists_nat_ge (s.val.1.measure Set.univ).toReal
  exact hs K ((ENNReal.toReal_le_toReal hfinite (ENNReal.natCast_ne_top K)).mp (by simpa using hK))

end GeneralizedBulk.Analysis
