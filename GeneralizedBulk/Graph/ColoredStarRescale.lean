import GeneralizedBulk.Graph.PermutedStarCovariance
import GeneralizedBulk.Matrix.ColorBlockDeterminant
import GeneralizedBulk.Entropy.GaussianMixtureLinearEntropy

/-! The actual colored star normal rescaling fixes eigenvector means and
has its exact entropy Jacobian. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Gaussian GeneralizedBulk.Covariance GeneralizedBulk.Entropy
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

def coloredStarRescale {k : ℕ} (energy sigma : Fin k → ℝ) (eta : ℝ) :
    Matrix (Fin k × Fin (d+1)) (Fin k × Fin (d+1)) ℝ :=
  colorBlock (fun a => projectionRescale (starNormalProjection d (energy a))
    (starNormalRescaleFactor d (energy a) eta (sigma a)))

theorem coloredStarRescale_transpose {k : ℕ} (energy sigma : Fin k → ℝ) (eta : ℝ) :
    (coloredStarRescale (d := d) energy sigma eta).transpose=coloredStarRescale (d := d) energy sigma eta := by
  unfold coloredStarRescale
  rw [colorBlock_transpose]
  apply congrArg colorBlock
  funext a
  exact projectionRescale_transpose _ (starNormalProjection_transpose d (energy a)) _

theorem coloredStarRescale_logdet {k : ℕ} (hd : 0 < d) (energy sigma : Fin k → ℝ) (eta : ℝ)
    (heta : 0 < eta) (hsigma : ∀ a,0 < sigma a) :
    (coloredStarRescale (d := d) energy sigma eta).det ≠ 0 ∧
      Real.log (|(coloredStarRescale (d := d) energy sigma eta).det|)=
        ∑ a,Real.log (starNormalRescaleFactor d (energy a) eta (sigma a)) := by
  have hdet (a : Fin k) : (projectionRescale (starNormalProjection d (energy a))
      (starNormalRescaleFactor d (energy a) eta (sigma a))).det=starNormalRescaleFactor d (energy a) eta (sigma a) :=
    starNormalRescale_det hd _ _ _
  have hp (a : Fin k) : 0 < starNormalRescaleFactor d (energy a) eta (sigma a) :=
    starNormalRescaleFactor_pos hd _ _ _ heta (hsigma a)
  constructor
  · rw [coloredStarRescale,colorBlock_det]
    exact Finset.prod_ne_zero_iff.mpr (fun a ha => by rw [hdet a]; exact (hp a).ne')
  · rw [coloredStarRescale,colorBlock_logabsdet _ (fun a => by rw [hdet a]; exact (hp a).ne')]
    simp only [hdet,abs_of_pos (hp _)]

theorem coloredStarRescale_starSample_fixed {k : ℕ} (q : Fin k → Fin (N n) → ℝ)
    (s : Fin (N n) × Equiv.Perm (Fin d)) (energy sigma : Fin k → ℝ) (eta r : ℝ)
    (heigen : ∀ a,∑ v,D.adjacency n ω s.1 v*q a v=energy a*q a s.1) :
    (coloredStarRescale (d := d) energy sigma eta).mulVec (r • D.starSample n ω q s)=r • D.starSample n ω q s := by
  rw [Matrix.mulVec_smul]
  congr 1
  funext aj
  have hh := congrFun (D.projectionRescale_starSample_fixed n ω q s aj.1 (energy aj.1)
    (starNormalRescaleFactor d (energy aj.1) eta (sigma aj.1)) (heigen aj.1)) aj.2
  simpa [coloredStarRescale,colorBlock,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,ite_mul,
    Finset.sum_ite_irrel] using hh

theorem coloredStarRescale_covariance {k : ℕ} (s : Fin (N n) × Equiv.Perm (Fin d))
    (energy sigma : Fin k → ℝ) (eta : ℝ)
    (A : Matrix (Fin k × Fin (d+1)) (Fin k × Fin (d+1)) ℝ)
    (hA : A*A.transpose=colorBlock (fun a => (D.resolventCovariance n ω (energy a) eta (sigma a)).submatrix
      (D.starVertex n ω s) (D.starVertex n ω s))) :
    let T := coloredStarRescale (d := d) energy sigma eta
    (T*A)*(T*A).transpose=colorBlock (fun a => D.rescaledPermutedStarCovariance n ω s (energy a) eta (sigma a)) := by
  dsimp only
  rw [Matrix.transpose_mul,Matrix.mul_assoc,← Matrix.mul_assoc A,hA,coloredStarRescale_transpose]
  unfold coloredStarRescale
  rw [colorBlock_mul,colorBlock_mul]
  apply congrArg colorBlock
  funext a
  simpa only [Matrix.mul_assoc] using (D.rescaledPermutedStarCovariance_congruence n ω s (energy a) eta (sigma a)).symm

end GeneralizedBulk.External.RegularSpectralData
