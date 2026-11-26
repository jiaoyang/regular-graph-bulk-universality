import GeneralizedBulk.Entropy.GaussianMixtureRestoration
import GeneralizedBulk.Entropy.GaussianMixtureLinearEntropy

/-! Restoring raw and reference mixtures around a good-root normal
rescaling. All entropy functions below are the actual Lebesgue densities. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.Entropy
open Mehler
variable {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S]

theorem gaussianMixture_entropy_compare_after_good_rescaling
    (weight : S → ℝ) (mean : S → I → ℝ) (A : S → Matrix I I ℝ) (M T : Matrix I I ℝ)
    (hw : ∀ s,0 ≤ weight s) (hsum : ∑ s,weight s=1)
    (hA : ∀ s,(A s).det ≠ 0) (hM : M.det ≠ 0) (hT : T.det ≠ 0)
    (hfix : ∀ s,T.mulVec (mean s)=mean s) (bad : S → Prop)
    (κ U κref Uref B e : ℝ) (hκ : 0 < κ) (hU : 0 < U) (hκref : 0 < κref) (hUref : 0 < Uref)
    (hB0 : 0 ≤ B) (hB : ∀ s,coordinateL1 (mean s) ≤ B)
    (hfloor : ∀ s x,κ*(∑ i,x i^2) ≤ dotProduct x ((A s*(A s).transpose).mulVec x))
    (htrace : ∀ s,Matrix.trace (A s*(A s).transpose) ≤ U)
    (hreffloor : ∀ x,κref*(∑ i,x i^2) ≤ dotProduct x ((M*M.transpose).mulVec x))
    (hreftrace : Matrix.trace (M*M.transpose) ≤ Uref)
    (hgood : |differentialEntropy (conditionalGaussianMixturePDF weight mean (fun s => T*A s) (fun s => ¬ bad s))-
      differentialEntropy (conditionalGaussianMixturePDF weight mean (fun _ => M) (fun s => ¬ bad s))| ≤ e) :
    |differentialEntropy (gaussianMixturePDF weight mean A)-
      (differentialEntropy (gaussianMixturePDF weight mean (fun _ => M))-Real.log (|T.det|))| ≤
      2*subsetWeightMass weight bad*(uniformMixtureAbsoluteEntropyBound I κ U B+
        uniformMixtureAbsoluteEntropyBound I κref Uref B)+2*Real.binEntropy (subsetWeightMass weight bad)+e := by
  have hr := gaussianMixture_entropy_restoration_uniform weight mean A hw hsum hA bad κ U B hκ hU hB0 hB hfloor htrace
  have href := gaussianMixture_entropy_restoration_uniform weight mean (fun _ => M) hw hsum (fun _ => hM) bad
    κref Uref B hκref hUref hB0 hB (fun _ => hreffloor) (fun _ => hreftrace)
  have hj := gaussianMixture_linear_entropy_fixed_means (conditionalFiniteWeight weight (fun s => ¬ bad s)) mean A T
    (conditionalFiniteWeight_nonneg weight hw _) (conditionalFiniteWeight_sum weight hw hsum _) hA hT hfix
  change differentialEntropy (conditionalGaussianMixturePDF weight mean (fun s => T*A s) (fun s => ¬ bad s))=
    differentialEntropy (conditionalGaussianMixturePDF weight mean A (fun s => ¬ bad s))+Real.log (|T.det|) at hj
  rw [hj] at hgood
  let F := differentialEntropy (gaussianMixturePDF weight mean A)
  let G := differentialEntropy (conditionalGaussianMixturePDF weight mean A (fun s => ¬ bad s))
  let R := differentialEntropy (gaussianMixturePDF weight mean (fun _ => M))
  let RG := differentialEntropy (conditionalGaussianMixturePDF weight mean (fun _ => M) (fun s => ¬ bad s))
  let J := Real.log (|T.det|)
  have hg : |G-(RG-J)| ≤ e := by convert hgood using 1 <;> dsimp [G,RG,J] <;> congr 1 <;> ring
  have htri := abs_sub_le F G (R-J)
  have htri2 := abs_sub_le G (RG-J) (R-J)
  have hlast : |(RG-J)-(R-J)|=|R-RG| := by rw [sub_sub_sub_cancel_right,abs_sub_comm]
  rw [hlast] at htri2
  change |F-G| ≤ _ at hr
  change |R-RG| ≤ _ at href
  change |F-(R-J)| ≤ _
  nlinarith only [htri,htri2,hg,hr,href]

end GeneralizedBulk.Entropy
