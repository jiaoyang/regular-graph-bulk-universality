import GeneralizedBulk.Entropy.GaussianMixtureEntropyCoupling
import GeneralizedBulk.Matrix.CovarianceLogEnvelope

/-! Absolute mixture-entropy bounds independent of the number of components. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace GeneralizedBulk.Entropy
open GeneralizedBulk.Gaussian GeneralizedBulk.Analysis Hermite Mehler GeneralizedBulk.Covariance
variable {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S]

def mixtureAbsoluteEntropyEnvelope (I : Type*) [Fintype I] (B T L D : ℝ) : ℝ :=
  (D+(Fintype.card I : ℝ)/2*|Real.log (2*Real.pi)|+L^2*(1+B^2))*(1+2*B^2+2*T^2)

theorem gaussianMixture_log_absolute_pullback_le
    (weight : S → ℝ) (mean : S → I → ℝ) (M : S → Matrix I I ℝ)
    (hw : ∀ s,0 ≤ weight s) (hnorm : ∑ s,weight s=1) (hM : ∀ s,(M s).det ≠ 0)
    (B T L D : ℝ) (hB0 : 0 ≤ B) (hT0 : 0 ≤ T) (hL0 : 0 ≤ L) (hD0 : 0 ≤ D)
    (hB : ∀ s,coordinateL1 (mean s) ≤ B) (hT : ∀ s,matrixEntryL1 (M s) ≤ T)
    (hL : ∀ s,matrixEntryL1 (M s)⁻¹ ≤ L) (hD : ∀ s,|Real.log (|(M s).det|)| ≤ D)
    (s : S) (z : I → ℝ) :
    |Real.log (gaussianMixturePDF weight mean M (mean s+(M s).mulVec z))| ≤
      mixtureAbsoluteEntropyEnvelope I B T L D*(1+coordinateL1 z^2) := by
  let R := D+(Fintype.card I : ℝ)/2*|Real.log (2*Real.pi)|+L^2*(1+B^2)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have henv (j : S) : gaussianLogEnvelope (mean j) (M j) ≤ R := by
    unfold gaussianLogEnvelope R
    gcongr
    · exact hD j
    · exact matrixEntryL1_nonneg _
    · exact hL j
    · exact coordinateL1_nonneg _
    · exact hB j
  let x := mean s+(M s).mulVec z
  have hx : coordinateL1 x ≤ B+T*coordinateL1 z :=
    (coordinateL1_add_le _ _).trans (add_le_add (hB s)
      ((coordinateL1_mulVec_le _ _).trans (mul_le_mul_of_nonneg_right (hT s) (coordinateL1_nonneg z))))
  have hlog : |Real.log (gaussianMixturePDF weight mean M x)| ≤ R*(1+coordinateL1 x^2) := by
    apply abs_log_weighted_sum_le weight _ hw hnorm (fun j => affineGaussianPDF_pos _ _ (hM j) x)
    intro j
    exact (abs_log_affineGaussianPDF_quadratic _ _ (hM j) x).trans
      (mul_le_mul_of_nonneg_right (henv j) (by positivity))
  have hsq : 1+coordinateL1 x^2 ≤ (1+2*B^2+2*T^2)*(1+coordinateL1 z^2) := by
    have hxx := pow_le_pow_left₀ (coordinateL1_nonneg x) hx 2
    nlinarith [sq_nonneg (B-T*coordinateL1 z),mul_nonneg (sq_nonneg B) (sq_nonneg (coordinateL1 z)),
      sq_nonneg (coordinateL1 z),sq_nonneg T]
  exact hlog.trans (by
    simpa only [mixtureAbsoluteEntropyEnvelope,R,mul_assoc] using mul_le_mul_of_nonneg_left hsq hR)

theorem gaussianMixture_absolute_entropy_le
    (weight : S → ℝ) (mean : S → I → ℝ) (M : S → Matrix I I ℝ)
    (hw : ∀ s,0 ≤ weight s) (hnorm : ∑ s,weight s=1) (hM : ∀ s,(M s).det ≠ 0)
    (B T L D : ℝ) (hB0 : 0 ≤ B) (hT0 : 0 ≤ T) (hL0 : 0 ≤ L) (hD0 : 0 ≤ D)
    (hB : ∀ s,coordinateL1 (mean s) ≤ B) (hT : ∀ s,matrixEntryL1 (M s) ≤ T)
    (hL : ∀ s,matrixEntryL1 (M s)⁻¹ ≤ L) (hD : ∀ s,|Real.log (|(M s).det|)| ≤ D) :
    |differentialEntropy (gaussianMixturePDF weight mean M)| ≤
      mixtureAbsoluteEntropyEnvelope I B T L D*(1+(Fintype.card I : ℝ)^2) := by
  let C := mixtureAbsoluteEntropyEnvelope I B T L D
  have hC : 0 ≤ C := by dsimp [C,mixtureAbsoluteEntropyEnvelope]; positivity
  have hmajor := ((integrable_const (1 : ℝ) (μ := standardGaussian I)).add
    standardGaussian_memLp_coordinateL1.integrable_sq).const_mul C
  have hind (s : S) : |∫ z,Real.log (gaussianMixturePDF weight mean M (mean s+(M s).mulVec z)) ∂standardGaussian I| ≤
      C*(1+(Fintype.card I : ℝ)^2) := by
    have hi := integrable_log_mixture_standard_pullback weight mean M hw hnorm hM (mean s) (M s)
    have hh := integral_mono (by simpa only [Real.norm_eq_abs] using hi.norm) hmajor
      (gaussianMixture_log_absolute_pullback_le weight mean M hw hnorm hM B T L D hB0 hT0 hL0 hD0 hB hT hL hD s)
    calc
      _ ≤ ∫ z,|Real.log (gaussianMixturePDF weight mean M (mean s+(M s).mulVec z))| ∂standardGaussian I := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun z => Real.log (gaussianMixturePDF weight mean M (mean s+(M s).mulVec z)))
      _ ≤ _ := hh.trans (by
        simp only [Pi.add_apply]
        rw [integral_const_mul,integral_add (integrable_const _) standardGaussian_memLp_coordinateL1.integrable_sq,integral_const]
        simp only [measureReal_univ_eq_one,smul_eq_mul,one_mul]
        exact mul_le_mul_of_nonneg_left (add_le_add_left integral_coordinateL1_sq_le_dimension 1) hC)
  rw [differentialEntropy_gaussianMixture_as_standard weight mean M hw hnorm hM,abs_neg]
  calc
    _ ≤ ∑ s,|weight s*(∫ z,Real.log (gaussianMixturePDF weight mean M (mean s+(M s).mulVec z)) ∂standardGaussian I)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s,weight s*(C*(1+(Fintype.card I : ℝ)^2)) := by
      apply Finset.sum_le_sum
      intro s hs
      rw [abs_mul,abs_of_nonneg (hw s)]
      exact mul_le_mul_of_nonneg_left (hind s) (hw s)
    _ = _ := by rw [← Finset.sum_mul,hnorm,one_mul]

def uniformMixtureAbsoluteEntropyBound (I : Type*) [Fintype I] (kappa U B : ℝ) : ℝ :=
  let m : ℝ := Fintype.card I
  mixtureAbsoluteEntropyEnvelope I B (m^2*Real.sqrt U) (m^2*Real.sqrt (m/kappa))
    (m/2*(|Real.log kappa|+|Real.log U|))*(1+m^2)

theorem gaussianMixture_absolute_entropy_of_covariance
    (weight : S → ℝ) (mean : S → I → ℝ) (M : S → Matrix I I ℝ)
    (hw : ∀ s,0 ≤ weight s) (hnorm : ∑ s,weight s=1) (hM : ∀ s,(M s).det ≠ 0)
    (kappa U B : ℝ) (hkappa : 0 < kappa) (hU : 0 < U) (hB0 : 0 ≤ B)
    (hB : ∀ s,coordinateL1 (mean s) ≤ B)
    (hfloor : ∀ s x,kappa*(∑ i,x i^2) ≤ dotProduct x ((M s*(M s).transpose).mulVec x))
    (htrace : ∀ s,Matrix.trace (M s*(M s).transpose) ≤ U) :
    |differentialEntropy (gaussianMixturePDF weight mean M)| ≤ uniformMixtureAbsoluteEntropyBound I kappa U B := by
  have hb (s) := covariance_reference_uniform_bounds (M s) (hM s) kappa U hkappa hU.le (hfloor s) (htrace s)
  exact gaussianMixture_absolute_entropy_le weight mean M hw hnorm hM
    B ((Fintype.card I : ℝ)^2*Real.sqrt U) ((Fintype.card I : ℝ)^2*Real.sqrt (Fintype.card I/kappa))
    ((Fintype.card I : ℝ)/2*(|Real.log kappa|+|Real.log U|)) hB0 (by positivity) (by positivity) (by positivity)
    hB (fun s => (hb s).2.2.1) (fun s => (hb s).2.2.2.1)
    (fun s => covariance_factor_logabsdet_le (M s) (hM s) kappa U hkappa hU (hfloor s) (htrace s))

end GeneralizedBulk.Entropy
