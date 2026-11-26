import GeneralizedBulk.Entropy.GaussianTranslationKL

/-! Translation entropy bounds for actual finite Gaussian mixtures. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace GeneralizedBulk.Entropy
open GeneralizedBulk.Gaussian GeneralizedBulk.Analysis Hermite
variable {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S]

def gaussianMixturePDF (weight : S → ℝ) (mean : S → I → ℝ) (M : S → Matrix I I ℝ) (x : I → ℝ) : ℝ :=
  ∑ s, weight s * affineGaussianPDF (mean s) (M s) x

theorem measurable_gaussianMixturePDF (weight : S → ℝ) (mean : S → I → ℝ) (M : S → Matrix I I ℝ) :
    Measurable (gaussianMixturePDF weight mean M) :=
  Finset.measurable_sum _ (fun s _ => (measurable_affineGaussianPDF (mean s) (M s)).const_mul _)

theorem gaussianMixturePDF_pos (weight : S → ℝ) (mean : S → I → ℝ) (M : S → Matrix I I ℝ)
    (hw : ∀ s, 0 ≤ weight s) (hnorm : ∑ s, weight s = 1) (hM : ∀ s, (M s).det ≠ 0) (x : I → ℝ) :
    0 < gaussianMixturePDF weight mean M x :=
  positive_weighted_sum weight _ hw hnorm (fun s => affineGaussianPDF_pos _ _ (hM s) x)

theorem integrable_gaussianMixturePDF (weight : S → ℝ) (mean : S → I → ℝ) (M : S → Matrix I I ℝ)
    (hM : ∀ s, (M s).det ≠ 0) : Integrable (gaussianMixturePDF weight mean M) volume :=
  integrable_finset_sum _ (fun s _ => (integrable_affineGaussianPDF _ _ (hM s)).const_mul _)

theorem integral_gaussianMixturePDF (weight : S → ℝ) (mean : S → I → ℝ) (M : S → Matrix I I ℝ)
    (hnorm : ∑ s, weight s = 1) (hM : ∀ s, (M s).det ≠ 0) :
    (∫ x, gaussianMixturePDF weight mean M x) = 1 := by
  change (∫ x, ∑ s, weight s * affineGaussianPDF (mean s) (M s) x) = 1
  rw [integral_finset_sum _
    (fun s _ => (integrable_affineGaussianPDF _ _ (hM s)).const_mul _)]
  simp_rw [integral_const_mul, integral_affineGaussianPDF _ _ (hM _), mul_one]
  exact hnorm

theorem affineGaussianPDF_translate (mean y : I → ℝ) (M : Matrix I I ℝ) (x : I → ℝ) :
    affineGaussianPDF mean M (x + y) = affineGaussianPDF (mean - y) M x := by
  unfold affineGaussianPDF
  congr 1
  abel

theorem gaussianMixturePDF_translate (weight : S → ℝ) (mean : S → I → ℝ) (M : S → Matrix I I ℝ)
    (x y : I → ℝ) : gaussianMixturePDF weight mean M (x + y) =
      gaussianMixturePDF weight (fun s => mean s - y) M x := by
  unfold gaussianMixturePDF
  simp_rw [affineGaussianPDF_translate]

theorem gaussianMixture_translation_kl (weight : S → ℝ) (mean : S → I → ℝ) (M : S → Matrix I I ℝ)
    (hw : ∀ s, 0 ≤ weight s) (hnorm : ∑ s, weight s = 1) (hM : ∀ s, (M s).det ≠ 0) (y : I → ℝ) :
    Integrable (fun x => klIntegrand (gaussianMixturePDF weight mean M x)
      (gaussianMixturePDF weight mean M (x + y))) volume ∧
    (∫ x, klIntegrand (gaussianMixturePDF weight mean M x)
      (gaussianMixturePDF weight mean M (x + y))) ≤
        ∑ s, weight s * (∑ i, ((M s)⁻¹.mulVec y i) ^ 2) / 2 := by
  simp_rw [gaussianMixturePDF_translate]
  have h := integral_kl_mixture_le volume weight
    (fun s => affineGaussianPDF (mean s) (M s)) (fun s => affineGaussianPDF (mean s - y) (M s))
    hw hnorm (fun s x => affineGaussianPDF_pos _ _ (hM s) x)
    (fun s x => affineGaussianPDF_pos _ _ (hM s) x)
    (fun s => measurable_affineGaussianPDF _ _) (fun s => measurable_affineGaussianPDF _ _)
    (fun s => (gaussian_klIntegrand_translation (mean s) (mean s - y) (M s) (hM s)).1)
  refine ⟨h.1, h.2.trans_eq ?_⟩
  apply Finset.sum_congr rfl
  intro s hs
  rw [(gaussian_klIntegrand_translation (mean s) (mean s - y) (M s) (hM s)).2,
    sub_sub_cancel]
  ring

theorem klIntegrand_swap_sum (f g : ℝ) (hf : 0 < f) (hg : 0 < g) :
    klIntegrand f g + klIntegrand g f = (f - g) * Real.log (f / g) := by
  have h : Real.log (g / f) = -Real.log (f / g) := by
    rw [Real.log_div (ne_of_gt hg) (ne_of_gt hf), Real.log_div (ne_of_gt hf) (ne_of_gt hg)]
    ring
  unfold klIntegrand
  rw [h]
  ring

theorem gaussianMixture_translation_symmetric_kl (weight : S → ℝ) (mean : S → I → ℝ) (M : S → Matrix I I ℝ)
    (hw : ∀ s, 0 ≤ weight s) (hnorm : ∑ s, weight s = 1) (hM : ∀ s, (M s).det ≠ 0) (y : I → ℝ) :
    Integrable (fun x => (gaussianMixturePDF weight mean M x - gaussianMixturePDF weight mean M (x + y)) *
      Real.log (gaussianMixturePDF weight mean M x / gaussianMixturePDF weight mean M (x + y))) volume ∧
    (∫ x, (gaussianMixturePDF weight mean M x - gaussianMixturePDF weight mean M (x + y)) *
      Real.log (gaussianMixturePDF weight mean M x / gaussianMixturePDF weight mean M (x + y))) ≤
        ∑ s, weight s * ∑ i, ((M s)⁻¹.mulVec y i) ^ 2 := by
  let f := gaussianMixturePDF weight mean M
  let g := gaussianMixturePDF weight (fun s => mean s - y) M
  have hf (x) : 0 < f x := gaussianMixturePDF_pos weight mean M hw hnorm hM x
  have hg (x) : 0 < g x := gaussianMixturePDF_pos weight _ M hw hnorm hM x
  have hforward := gaussianMixture_translation_kl weight mean M hw hnorm hM y
  simp_rw [gaussianMixturePDF_translate] at hforward ⊢
  have hreverse := integral_kl_mixture_le volume weight
    (fun s => affineGaussianPDF (mean s - y) (M s)) (fun s => affineGaussianPDF (mean s) (M s))
    hw hnorm (fun s x => affineGaussianPDF_pos _ _ (hM s) x)
    (fun s x => affineGaussianPDF_pos _ _ (hM s) x)
    (fun s => measurable_affineGaussianPDF _ _) (fun s => measurable_affineGaussianPDF _ _)
    (fun s => (gaussian_klIntegrand_translation (mean s - y) (mean s) (M s) (hM s)).1)
  have hb : (∫ x, klIntegrand (g x) (f x)) ≤ ∑ s, weight s * (∑ i, ((M s)⁻¹.mulVec y i) ^ 2) / 2 := by
    refine hreverse.2.trans_eq ?_
    apply Finset.sum_congr rfl
    intro s hs
    rw [(gaussian_klIntegrand_translation (mean s - y) (mean s) (M s) (hM s)).2]
    have he : mean s - y - mean s = -y := by abel
    rw [he, Matrix.mulVec_neg]
    simp only [Pi.neg_apply, neg_sq]
    ring
  have he (x) : (f x - g x) * Real.log (f x / g x) = klIntegrand (f x) (g x) + klIntegrand (g x) (f x) :=
    (klIntegrand_swap_sum _ _ (hf x) (hg x)).symm
  change Integrable (fun x => (f x - g x) * Real.log (f x / g x)) volume ∧
    (∫ x, (f x - g x) * Real.log (f x / g x)) ≤ _
  simp_rw [he]
  refine ⟨hforward.1.add hreverse.1, ?_⟩
  have hsum : (∑ s, weight s * (∑ i, ((M s)⁻¹.mulVec y i) ^ 2) / 2) +
      (∑ s, weight s * (∑ i, ((M s)⁻¹.mulVec y i) ^ 2) / 2) =
        ∑ s, weight s * ∑ i, ((M s)⁻¹.mulVec y i) ^ 2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    ring
  calc
    _ = (∫ x, klIntegrand (f x) (g x)) + ∫ x, klIntegrand (g x) (f x) :=
      integral_add hforward.1 hreverse.1
    _ ≤ _ := (add_le_add hforward.2 hb).trans_eq hsum

end GeneralizedBulk.Entropy
