import GeneralizedBulk.Entropy.ConditionalFiniteWeights
import GeneralizedBulk.Entropy.DifferentialRestoration
import GeneralizedBulk.Entropy.GaussianMixtureAbsoluteEntropy

/-! An actual good/bad-root Gaussian-mixture factory and entropy restoration.
Conditional zero-mass laws use the original normalized mixture, making the
identities and bounds valid also when the bad mass is zero or one. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical

namespace GeneralizedBulk.Entropy
open Mehler

variable {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S]

def conditionalGaussianMixturePDF (weight : S → ℝ) (mean : S → I → ℝ)
    (M : S → Matrix I I ℝ) (s : S → Prop) : (I → ℝ) → ℝ :=
  gaussianMixturePDF (conditionalFiniteWeight weight s) mean M

theorem gaussianMixturePDF_conditional_split (weight : S → ℝ) (mean : S → I → ℝ)
    (M : S → Matrix I I ℝ) (hw : ∀ s,0 ≤ weight s) (hsum : ∑ s,weight s = 1) (bad : S → Prop) (x : I → ℝ) :
    gaussianMixturePDF weight mean M x =
      (1-subsetWeightMass weight bad)*conditionalGaussianMixturePDF weight mean M (fun s => ¬ bad s) x+
        subsetWeightMass weight bad*conditionalGaussianMixturePDF weight mean M bad x := by
  unfold conditionalGaussianMixturePDF gaussianMixturePDF
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  rw [show (1-subsetWeightMass weight bad)*(conditionalFiniteWeight weight (fun s => ¬ bad s) s*affineGaussianPDF (mean s) (M s) x)+
    subsetWeightMass weight bad*(conditionalFiniteWeight weight bad s*affineGaussianPDF (mean s) (M s) x) =
    ((1-subsetWeightMass weight bad)*conditionalFiniteWeight weight (fun s => ¬ bad s) s+
      subsetWeightMass weight bad*conditionalFiniteWeight weight bad s)*affineGaussianPDF (mean s) (M s) x from by ring,
    conditionalFiniteWeight_split weight hw hsum bad s]

theorem conditionalGaussianMixturePDF_eq_subtype (weight : S → ℝ) (mean : S → I → ℝ)
    (M : S → Matrix I I ℝ) (s : S → Prop) (hs : subsetWeightMass weight s ≠ 0) :
    conditionalGaussianMixturePDF weight mean M s =
      gaussianMixturePDF (conditionalSubtypeWeight weight s) (fun i => mean i.val) (fun i => M i.val) := by
  funext x
  have he : (∑ i : {i : S // s i},weight i.val/subsetWeightMass weight s*affineGaussianPDF (mean i.val) (M i.val) x) =
      ∑ i,if s i then weight i/subsetWeightMass weight s*affineGaussianPDF (mean i) (M i) x else 0 := by
    simpa only [tsum_fintype,Set.indicator,Set.mem_setOf_eq] using
      tsum_subtype {i : S | s i} (fun i => weight i/subsetWeightMass weight s*affineGaussianPDF (mean i) (M i) x)
  unfold conditionalGaussianMixturePDF gaussianMixturePDF conditionalSubtypeWeight
  rw [he]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hi : s i <;> simp [conditionalFiniteWeight,hs,hi]

set_option maxHeartbeats 1500000 in
theorem gaussianMixture_entropy_restoration (weight : S → ℝ) (mean : S → I → ℝ)
    (M : S → Matrix I I ℝ) (hw : ∀ s,0 ≤ weight s) (hsum : ∑ s,weight s = 1)
    (hdet : ∀ s,(M s).det ≠ 0) (bad : S → Prop) :
    |differentialEntropy (gaussianMixturePDF weight mean M)-
      differentialEntropy (conditionalGaussianMixturePDF weight mean M (fun s => ¬ bad s))| ≤
      subsetWeightMass weight bad*
        (|differentialEntropy (conditionalGaussianMixturePDF weight mean M bad)|+
          |differentialEntropy (conditionalGaussianMixturePDF weight mean M (fun s => ¬ bad s))|)+
        Real.binEntropy (subsetWeightMass weight bad) := by
  have hwp (s : S → Prop) := conditionalFiniteWeight_nonneg weight hw s
  have hwn (s : S → Prop) := conditionalFiniteWeight_sum weight hw hsum s
  exact differentialEntropy_restoration _ _ _ (subsetWeightMass weight bad)
    (subsetWeightMass_nonneg weight hw bad) (subsetWeightMass_le_one weight hw hsum bad)
    (gaussianMixturePDF_conditional_split weight mean M hw hsum bad)
    (fun x => (gaussianMixturePDF_pos _ mean M (hwp _) (hwn _) hdet x).le)
    (fun x => (gaussianMixturePDF_pos _ mean M (hwp _) (hwn _) hdet x).le)
    (integrable_gaussianMixturePDF _ mean M hdet) (integrable_gaussianMixturePDF _ mean M hdet)
    (integral_gaussianMixturePDF _ mean M (hwn _) hdet) (integral_gaussianMixturePDF _ mean M (hwn _) hdet)
    (integrable_gaussianMixturePDF_mul_log _ mean M (hwp _) (hwn _) hdet)
    (integrable_gaussianMixturePDF_mul_log _ mean M (hwp _) (hwn _) hdet)
    (integrable_gaussianMixturePDF_mul_log weight mean M hw hsum hdet)

theorem gaussianMixture_entropy_restoration_uniform (weight : S → ℝ) (mean : S → I → ℝ)
    (M : S → Matrix I I ℝ) (hw : ∀ s,0 ≤ weight s) (hsum : ∑ s,weight s = 1)
    (hdet : ∀ s,(M s).det ≠ 0) (bad : S → Prop)
    (κ U B : ℝ) (hκ : 0 < κ) (hU : 0 < U) (hB0 : 0 ≤ B)
    (hB : ∀ s,coordinateL1 (mean s) ≤ B)
    (hfloor : ∀ s x,κ*(∑ i,x i^2) ≤ dotProduct x ((M s*(M s).transpose).mulVec x))
    (htrace : ∀ s,Matrix.trace (M s*(M s).transpose) ≤ U) :
    |differentialEntropy (gaussianMixturePDF weight mean M)-
      differentialEntropy (conditionalGaussianMixturePDF weight mean M (fun s => ¬ bad s))| ≤
      2*subsetWeightMass weight bad*uniformMixtureAbsoluteEntropyBound I κ U B+
        Real.binEntropy (subsetWeightMass weight bad) := by
  have h := gaussianMixture_entropy_restoration weight mean M hw hsum hdet bad
  dsimp only [conditionalGaussianMixturePDF] at h ⊢
  have hgood := gaussianMixture_absolute_entropy_of_covariance (conditionalFiniteWeight weight (fun s => ¬ bad s)) mean M
    (conditionalFiniteWeight_nonneg weight hw _) (conditionalFiniteWeight_sum weight hw hsum _)
    hdet κ U B hκ hU hB0 hB hfloor htrace
  have hbad := gaussianMixture_absolute_entropy_of_covariance (conditionalFiniteWeight weight bad) mean M
    (conditionalFiniteWeight_nonneg weight hw _) (conditionalFiniteWeight_sum weight hw hsum _)
    hdet κ U B hκ hU hB0 hB hfloor htrace
  have hp := subsetWeightMass_nonneg weight hw bad
  have hh := mul_le_mul_of_nonneg_left (add_le_add hbad hgood) hp
  nlinarith

end GeneralizedBulk.Entropy
