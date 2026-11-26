import GeneralizedBulk.Entropy.GaussianQuantizedEntropy

/-! The global correlated Gaussian quantizer lower bound. Only the lower
grid entropy estimate is used, so no exponential-in-dimension grid error
enters the whole-configuration comparison. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical NNReal

namespace GeneralizedBulk.Entropy

theorem affineGaussian_clipped_entropy_lower {m : ℕ} (mean : Fin m → ℝ)
    (M : Matrix (Fin m) (Fin m) ℝ) (hdet : M.det ≠ 0)
    (H : ℝ) (hH : 0 ≤ H) (hmean : ∀ i,|mean i| ≤ H)
    (c : ℝ≥0) (hc : 0 < c) (hvar : ∀ i,GeneralizedBulk.Gaussian.coordinateVariance M i ≤ c)
    (a : ℝ) (ha : 0 < a) (K : ℕ) (hK : 0 < K) (hR : H ≤ (K : ℝ)*a) :
    -gaussianClippingError m a H c K ≤
      Finite.entropy (lawMass (affineGaussian mean M) (codedClipIntegerVector K hK ∘ gridLabel a))+
        (m : ℝ)*Real.log a-differentialEntropy (affineGaussianPDF mean M) := by
  have h := gaussianMixture_clipped_entropy_lower (S := Unit) (fun _ => 1) (fun _ => mean) (fun _ => M)
    (by intro; norm_num) (by simp) (fun _ => hdet) H hH (fun _ => hmean) c hc (fun _ => hvar) a ha K hK hR
  have he : gaussianMixturePDF (fun _ : Unit => 1) (fun _ => mean) (fun _ => M) = affineGaussianPDF mean M := by
    funext x
    simp only [gaussianMixturePDF,Fintype.sum_unique,one_mul]
  rw [he] at h
  simpa only [gaussianMixtureLaw,Fintype.sum_unique,ENNReal.ofReal_one,one_smul] using h

end GeneralizedBulk.Entropy
