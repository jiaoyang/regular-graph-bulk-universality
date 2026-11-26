import GeneralizedBulk.Entropy.CorrelatedGridClipping
import GeneralizedBulk.Entropy.GaussianGridLaw

/-! Uniform clipping loss for actual finite Gaussian mixtures. The bound is
independent of the number of mixture components. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal

namespace GeneralizedBulk.Entropy
open GeneralizedBulk.Gaussian

variable {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S]

theorem affineGaussian_coordinate_law (mean : I → ℝ) (M : Matrix I I ℝ) (i : I) :
    Measure.map (fun x : I → ℝ => x i) (affineGaussian mean M) = gaussianReal (mean i) (coordinateVariance M i) := by
  rw [affineGaussian,Measure.map_map (measurable_pi_apply i) (by fun_prop)]
  exact linearImageGaussian_shifted_coordinate M mean i

theorem integrable_gaussianMixtureLaw_of_components (weight : S → ℝ) (mean : S → I → ℝ)
    (M : S → Matrix I I ℝ) (f : (I → ℝ) → ℝ) (hf : ∀ s,Integrable f (affineGaussian (mean s) (M s))) :
    Integrable f (gaussianMixtureLaw weight mean M) :=
  integrable_finset_sum_measure.mpr (fun s hs => (hf s).smul_measure ENNReal.ofReal_ne_top)

theorem integral_gaussianMixtureLaw (weight : S → ℝ) (mean : S → I → ℝ)
    (M : S → Matrix I I ℝ) (hw : ∀ s,0 ≤ weight s) (f : (I → ℝ) → ℝ)
    (hf : ∀ s,Integrable f (affineGaussian (mean s) (M s))) :
    (∫ x,f x ∂gaussianMixtureLaw weight mean M) =
      ∑ s,weight s*(∫ x,f x ∂affineGaussian (mean s) (M s)) := by
  rw [gaussianMixtureLaw,integral_finset_sum_measure (fun s hs => (hf s).smul_measure ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro s hs
  rw [integral_smul_measure,ENNReal.toReal_ofReal (hw s),smul_eq_mul]

theorem gaussianMixtureLaw_real (weight : S → ℝ) (mean : S → I → ℝ)
    (M : S → Matrix I I ℝ) (hw : ∀ s,0 ≤ weight s) (T : Set (I → ℝ)) :
    (gaussianMixtureLaw weight mean M).real T = ∑ s,weight s*(affineGaussian (mean s) (M s)).real T := by
  unfold gaussianMixtureLaw Measure.real
  rw [Measure.finset_sum_apply,ENNReal.toReal_sum (fun s hs => by
    simp only [Measure.smul_apply,smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by finiteness))]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,ENNReal.toReal_ofReal (hw s)]

set_option maxHeartbeats 1500000 in
theorem gaussianMixture_grid_clipping_loss {m : ℕ}
    (weight : S → ℝ) (mean : S → Fin m → ℝ) (M : S → Matrix (Fin m) (Fin m) ℝ)
    (hw : ∀ s,0 ≤ weight s) (hsum : ∑ s,weight s = 1) (hdet : ∀ s,(M s).det ≠ 0)
    (H : ℝ) (hH : 0 ≤ H) (hmean : ∀ s i,|mean s i| ≤ H)
    (c : ℝ≥0) (hc : 0 < c) (hvar : ∀ s i,coordinateVariance (M s) i ≤ c)
    (a : ℝ) (ha : 0 < a) (K : ℕ) (hK : 0 < K) (hR : H ≤ (K : ℝ)*a) :
    countableEntropy (gridMass a (gaussianMixturePDF weight mean M))-
      Finite.entropy (lawMass (gaussianMixtureLaw weight mean M) (codedClipIntegerVector K hK ∘ gridLabel a)) ≤
      gridClippingLossConstant m a (H^2+(c : ℝ))*
        Real.sqrt (2*(m : ℝ)*Real.exp (-((K : ℝ)*a-H)^2/(2*(c : ℝ)))) := by
  let μ := gaussianMixtureLaw weight mean M
  letI : IsProbabilityMeasure μ := gaussianMixtureLaw_probability weight mean M hw hsum hdet
  have hi (s : S) (i : Fin m) : Integrable (fun x : Fin m → ℝ => x i^2) (affineGaussian (mean s) (M s)) :=
    gaussianLaw_integrable_pow (affineGaussian (mean s) (M s)) (fun x : Fin m → ℝ => x i) (mean s i) (coordinateVariance (M s) i)
      (affineGaussian_coordinate_law _ _ i) 2
  have hcoord (i : Fin m) : MemLp (fun x : Fin m → ℝ => x i) 2 μ :=
    (memLp_two_iff_integrable_sq (measurable_pi_apply i).aestronglyMeasurable).mpr
      (integrable_gaussianMixtureLaw_of_components weight mean M _ (fun s => hi s i))
  have hB (i : Fin m) : (∫ x : Fin m → ℝ,x i^2 ∂μ) ≤ H^2+(c : ℝ) := by
    rw [integral_gaussianMixtureLaw weight mean M hw _ (fun s => hi s i)]
    calc
      _ ≤ ∑ s,weight s*(H^2+(c : ℝ)) := by
        apply Finset.sum_le_sum
        intro s hs
        apply mul_le_mul_of_nonneg_left _ (hw s)
        rw [gaussianLaw_second_moment (affineGaussian (mean s) (M s)) (fun x : Fin m → ℝ => x i) (mean s i) (coordinateVariance (M s) i)
          (affineGaussian_coordinate_law _ _ i)]
        have hv : (coordinateVariance (M s) i : ℝ) ≤ c := by exact_mod_cast hvar s i
        have hsq : (mean s i)^2 ≤ H^2 := by
          simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hH).mpr (hmean s i)
        linarith
      _ = _ := by rw [← Finset.sum_mul,hsum,one_mul]
  have htail : μ.real {x | integerClippingTail K (gridLabel a x)} ≤
      2*(m : ℝ)*Real.exp (-((K : ℝ)*a-H)^2/(2*(c : ℝ))) := by
    rw [gaussianMixtureLaw_real weight mean M hw]
    calc
      _ ≤ ∑ s,weight s*(2*(m : ℝ)*Real.exp (-((K : ℝ)*a-H)^2/(2*(c : ℝ)))) := by
        apply Finset.sum_le_sum
        intro s hs
        apply mul_le_mul_of_nonneg_left _ (hw s)
        rw [affineGaussian,Measure.real,Measure.map_apply (by fun_prop)
          (measurableSet_countable_event (gridLabel a) (measurable_gridLabel a) (integerClippingTail K))]
        exact correlated_grid_clipping_probability_le (M s) (mean s) H (hmean s) c hc (hvar s) a ha K hR
      _ = _ := by rw [← Finset.sum_mul,hsum,one_mul]
  have h := grid_clipping_entropy_loss_le μ id measurable_id hcoord (H^2+(c : ℝ)) hB a ha K hK
  simp only [Function.comp_id,id_eq] at h
  rw [lawMass_gaussianMixture_gridLabel weight mean M hw hsum hdet a ha] at h
  exact h.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt htail) (gridClippingLossConstant_nonneg m a _))

end GeneralizedBulk.Entropy
