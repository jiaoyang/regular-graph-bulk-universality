import GeneralizedBulk.Gaussian.ColoredExtendedWhitening
import GeneralizedBulk.Gaussian.CovarianceLaw

/-! The actual extended Gaussian is the linear image of independent tangent
and normal Gaussian coordinates, with the empirical signal shifted only in
the tangent coordinates. -/
noncomputable section
open MeasureTheory
open scoped Matrix
namespace GeneralizedBulk.Gaussian
open GeneralizedBulk.Entropy.Channel

 theorem linearImageGaussian_sum_split {I J K : Type*} [Fintype I] [Fintype J]
    (A : Matrix K (I ⊕ J) ℝ) :
    linearImageGaussian A = ((standardVector I).prod (standardVector J)).map
      (fun xy : (I → ℝ) × (J → ℝ) => A.mulVec (Sum.elim xy.1 xy.2)) := by
  have hs := measurePreserving_sumPiEquivProdPi_symm (fun _ : I ⊕ J => standardNormal)
  have hm : ((standardVector I).prod (standardVector J)).map
      (fun xy : (I → ℝ) × (J → ℝ) => Sum.elim xy.1 xy.2) = standardVector (I ⊕ J) := hs.map_eq
  have hmeas : Measurable (fun xy : (I → ℝ) × (J → ℝ) => Sum.elim xy.1 xy.2) :=
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : I ⊕ J => ℝ)).symm.measurable
  rw [linearImageGaussian, ← hm, Measure.map_map (measurable_finiteMatrixAction A) hmeas]
  rfl

 theorem coloredExtendedGaussian_product (d k : ℕ) (hd : 2 ≤ d) (energy : Fin k → ℝ)
    (hE : ∀ a, |energy a| < d) (signal : ScalarCoordinate d k → ℝ) :
    GeneralizedBulk.Entropy.affineGaussian
      ((coloredExtendedCoefficients d k hd energy).mulVec (Sum.elim signal (fun _ : Fin k => 0)))
      (coloredExtendedFactor d k hd energy) =
      ((standardVector (ScalarCoordinate d k)).prod (standardVector (Fin k))).map
        (fun xy : (ScalarCoordinate d k → ℝ) × (Fin k → ℝ) =>
          (coloredExtendedCoefficients d k hd energy).mulVec (Sum.elim (signal + xy.1) xy.2)) := by
  let A := coloredExtendedCoefficients d k hd energy
  have hc : coloredExtendedFactor d k hd energy * (coloredExtendedFactor d k hd energy).transpose = A * A.transpose := by
    rw [coloredExtendedFactor_covariance d k hd energy hE, coloredExtendedCoefficients_gram d k hd energy hE]
  rw [GeneralizedBulk.Entropy.affineGaussian, linearImageGaussian_eq_of_covariance _ A hc,
    linearImageGaussian_sum_split]
  have hsplit : Measurable (fun xy : (ScalarCoordinate d k → ℝ) × (Fin k → ℝ) => Sum.elim xy.1 xy.2) :=
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : ExtendedColoredCoordinate d k => ℝ)).symm.measurable
  have hmap : Measurable (fun xy : (ScalarCoordinate d k → ℝ) × (Fin k → ℝ) => A.mulVec (Sum.elim xy.1 xy.2)) :=
    (measurable_finiteMatrixAction A).comp hsplit
  have htrans : Measurable (fun x : (Fin k × Fin (d + 1)) → ℝ => A.mulVec (Sum.elim signal (fun _ => 0)) + x) := by fun_prop
  rw [Measure.map_map htrans hmap]
  congr 1
  funext xy
  change A.mulVec (Sum.elim signal (fun _ => 0)) + A.mulVec (Sum.elim xy.1 xy.2) =
    A.mulVec (Sum.elim (signal + xy.1) xy.2)
  rw [← Matrix.mulVec_add]
  apply congrArg A.mulVec
  funext i
  cases i <;> simp only [Pi.add_apply, Sum.elim_inl, Sum.elim_inr, zero_add]

end GeneralizedBulk.Gaussian
