import GeneralizedBulk.Entropy.GaussianMixtureStabilityPointwise

/-! Integrating an actual common-Gaussian coupling controls mixture entropy. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace GeneralizedBulk.Entropy
open GeneralizedBulk.Gaussian GeneralizedBulk.Analysis Hermite Mehler
variable {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S]

theorem coordinateL1_sq_le_dimension_energy (z : I → ℝ) :
    coordinateL1 z ^ 2 ≤ (Fintype.card I : ℝ) * ∑ i, z i ^ 2 := by
  have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i : I => |z i|) (fun _ => (1 : ℝ))
  simpa only [mul_one, sq_abs, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] using hh

theorem integral_coordinateL1_sq_le_dimension :
    (∫ z : I → ℝ, coordinateL1 z ^ 2 ∂standardGaussian I) ≤ (Fintype.card I : ℝ) ^ 2 := by
  have hi := standardGaussian_memLp_coordinateL1 (I := I) |>.integrable_sq
  have hs := integrable_finset_sum (Finset.univ : Finset I) (fun i _ => standardGaussian_integrable_coordinate_pow i 2)
  have hh := integral_mono hi (hs.const_mul (Fintype.card I : ℝ)) coordinateL1_sq_le_dimension_energy
  rw [integral_const_mul, integral_finset_sum _ (fun i _ => standardGaussian_integrable_coordinate_pow i 2)] at hh
  change (∫ z : I → ℝ, coordinateL1 z ^ 2 ∂standardGaussian I) ≤
    (Fintype.card I : ℝ) * ∑ i : I, ∫ z : I → ℝ, z i ^ 2 ∂standardGaussian I at hh
  simp_rw [standardGaussian_coordinate_sq] at hh
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, pow_two] using hh

theorem integrable_log_mixture_standard_pullback (weight : S → ℝ) (mean : S → I → ℝ)
    (M : S → Matrix I I ℝ) (hw : ∀ s, 0 ≤ weight s) (hnorm : ∑ s, weight s = 1)
    (hM : ∀ s, (M s).det ≠ 0) (b : I → ℝ) (A : Matrix I I ℝ) :
    Integrable (fun z => Real.log (gaussianMixturePDF weight mean M (b + A.mulVec z))) (standardGaussian I) := by
  have h := integrable_log_gaussianMixturePDF_under_affineGaussian weight mean M hw hnorm hM b A
  rw [affineGaussian_map_standardGaussian] at h
  exact (integrable_map_measure (measurable_gaussianMixturePDF weight mean M).log.aestronglyMeasurable
    (by fun_prop : Measurable (fun z : I → ℝ => b + A.mulVec z)).aemeasurable).mp h

theorem differentialEntropy_gaussianMixture_as_standard (weight : S → ℝ) (mean : S → I → ℝ)
    (M : S → Matrix I I ℝ) (hw : ∀ s, 0 ≤ weight s) (hnorm : ∑ s, weight s = 1)
    (hM : ∀ s, (M s).det ≠ 0) :
    differentialEntropy (gaussianMixturePDF weight mean M) =
      -∑ s, weight s * ∫ z, Real.log (gaussianMixturePDF weight mean M (mean s + (M s).mulVec z)) ∂standardGaussian I := by
  rw [differentialEntropy_gaussianMixture_as_expectations weight mean M hw hnorm hM]
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  rw [affineGaussian_map_standardGaussian, integral_map
    (by fun_prop : Measurable (fun z : I → ℝ => mean s + (M s).mulVec z)).aemeasurable
    (measurable_gaussianMixturePDF weight mean M).log.aestronglyMeasurable]

theorem gaussianMixture_entropy_difference_of_coupling
    (weight : S → ℝ) (mean : S → I → ℝ) (M A : S → Matrix I I ℝ)
    (hw : ∀ s, 0 ≤ weight s) (hnorm : ∑ s, weight s = 1)
    (hM : ∀ s, (M s).det ≠ 0) (hA : ∀ s, (A s).det ≠ 0)
    (E : ℝ) (hE : 0 ≤ E)
    (hbound : ∀ s z,
      |Real.log (gaussianMixturePDF weight mean M (mean s + (M s).mulVec z)) -
        Real.log (gaussianMixturePDF weight mean A (mean s + (A s).mulVec z))| ≤ E * (1 + coordinateL1 z ^ 2)) :
    |differentialEntropy (gaussianMixturePDF weight mean M) - differentialEntropy (gaussianMixturePDF weight mean A)| ≤
      E * (1 + (Fintype.card I : ℝ) ^ 2) := by
  let F := fun s z => Real.log (gaussianMixturePDF weight mean M (mean s + (M s).mulVec z))
  let G := fun s z => Real.log (gaussianMixturePDF weight mean A (mean s + (A s).mulVec z))
  have hF (s) : Integrable (F s) (standardGaussian I) :=
    integrable_log_mixture_standard_pullback weight mean M hw hnorm hM _ _
  have hG (s) : Integrable (G s) (standardGaussian I) :=
    integrable_log_mixture_standard_pullback weight mean A hw hnorm hA _ _
  have hmajor := ((integrable_const (1 : ℝ) (μ := standardGaussian I)).add
    standardGaussian_memLp_coordinateL1.integrable_sq).const_mul E
  have hind (s : S) : |(∫ z, F s z ∂standardGaussian I) - ∫ z, G s z ∂standardGaussian I| ≤
      E * (1 + (Fintype.card I : ℝ) ^ 2) := by
    rw [← integral_sub (hF s) (hG s)]
    have hh : (∫ z, |F s z - G s z| ∂standardGaussian I) ≤
        ∫ z, E * (1 + coordinateL1 z ^ 2) ∂standardGaussian I :=
      integral_mono (by simpa only [Real.norm_eq_abs] using ((hF s).sub (hG s)).norm) hmajor (hbound s)
    calc
      _ ≤ ∫ z, |F s z - G s z| ∂standardGaussian I := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun z => F s z - G s z)
      _ ≤ _ := hh.trans (by
        rw [integral_const_mul, integral_add (integrable_const _) standardGaussian_memLp_coordinateL1.integrable_sq,
          integral_const]
        simp only [measureReal_univ_eq_one, smul_eq_mul, one_mul]
        exact mul_le_mul_of_nonneg_left (add_le_add_left integral_coordinateL1_sq_le_dimension 1) hE)
  rw [differentialEntropy_gaussianMixture_as_standard weight mean M hw hnorm hM,
    differentialEntropy_gaussianMixture_as_standard weight mean A hw hnorm hA]
  change |-(∑ s, weight s * ∫ z, F s z ∂standardGaussian I) -
    -(∑ s, weight s * ∫ z, G s z ∂standardGaussian I)| ≤ _
  rw [neg_sub_neg, abs_sub_comm, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ s, |weight s * (∫ z, F s z ∂standardGaussian I) - weight s * ∫ z, G s z ∂standardGaussian I| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ s, weight s * |(∫ z, F s z ∂standardGaussian I) - ∫ z, G s z ∂standardGaussian I| := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [← mul_sub, abs_mul, abs_of_nonneg (hw s)]
    _ ≤ ∑ s, weight s * (E * (1 + (Fintype.card I : ℝ) ^ 2)) :=
      Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hind s) (hw s))
    _ = _ := by rw [← Finset.sum_mul, hnorm, one_mul]

end GeneralizedBulk.Entropy
