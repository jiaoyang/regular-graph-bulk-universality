import GeneralizedBulk.Graph.HYRescaledStarCovariance
import GeneralizedBulk.Graph.StarNormalSignal
import GeneralizedBulk.Gaussian.StarPermutation
import GeneralizedBulk.Matrix.PositiveCompression

/-! Actual permuted star covariances satisfy the same normal-rescaled HY estimate. -/
noncomputable section
namespace GeneralizedBulk.External.RegularSpectralData
open Set MeasureTheory GeneralizedBulk.KestenMcKay GeneralizedBulk.Gaussian GeneralizedBulk.Entropy GeneralizedBulk.Covariance
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

def rescaledPermutedStarCovariance (s : Fin (N n) × Equiv.Perm (Fin d)) (E eta sigma : ℝ) :
    Matrix (Fin (d+1)) (Fin (d+1)) ℝ :=
  (D.rescaledLocalStarCovariance n ω s.1 E eta sigma).submatrix (starLeafPermutation s.2) (starLeafPermutation s.2)

theorem rescaledPermutedStarCovariance_congruence (s : Fin (N n) × Equiv.Perm (Fin d)) (E eta sigma : ℝ) :
    D.rescaledPermutedStarCovariance n ω s E eta sigma=
      let R := projectionRescale (starNormalProjection d E) (starNormalRescaleFactor d E eta sigma)
      R*((D.resolventCovariance n ω E eta sigma).submatrix
        (D.starVertex n ω s) (D.starVertex n ω s))*R := by
  rw [rescaledPermutedStarCovariance,rescaledLocalStarCovariance,← starRescale_permuted_covariance]
  congr 2
  ext i j
  refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j <;>
    simp [localEntropyStarCovariance,Matrix.submatrix_apply,entropyStarVertex,starVertex]

theorem rescaledPermutedStarCovariance_posDef (hd : 0 < d) (s : Fin (N n) × Equiv.Perm (Fin d))
    (E eta sigma : ℝ) (heta : 0 < eta) (hsigma : 0 < sigma) :
    (D.rescaledPermutedStarCovariance n ω s E eta sigma).PosDef :=
  posDef_submatrix_of_injective _ (D.rescaledLocalStarCovariance_posDef n ω hd s.1 E eta sigma heta hsigma)
    (starLeafPermutation s.2) (starLeafPermutation s.2).injective

theorem rescaledPermutedStarCovariance_entry_bound (s : Fin (N n) × Equiv.Perm (Fin d))
    (E eta sigma e : ℝ)
    (hbound : matrixEntryL1 (D.rescaledLocalStarCovariance n ω s.1 E eta sigma-starReferenceCovariance d E) ≤ e)
    (i j : Fin (d+1)) :
    |(D.rescaledPermutedStarCovariance n ω s E eta sigma-starReferenceCovariance d E) i j| ≤ e := by
  have href : (starReferenceCovariance d E).submatrix (starLeafPermutation s.2) (starLeafPermutation s.2)=starReferenceCovariance d E := by
    ext i j
    exact congrArg₂ (·+·)
      (congrFun (congrFun (starWaveCovariance_leaf_permutation s.2 E) i) j)
      (congrFun (congrFun (starNormalProjection_leaf_permutation s.2 E) i) j)
  calc
    _ = |(D.rescaledLocalStarCovariance n ω s.1 E eta sigma-starReferenceCovariance d E)
        (starLeafPermutation s.2 i) (starLeafPermutation s.2 j)| := by
      have hr := congrFun (congrFun href i) j
      change starReferenceCovariance d E (starLeafPermutation s.2 i) (starLeafPermutation s.2 j)=starReferenceCovariance d E i j at hr
      simp only [rescaledPermutedStarCovariance,Matrix.sub_apply,Matrix.submatrix_apply,hr]
    _ ≤ e := (abs_matrix_entry_le_matrixEntryL1 _ _ _).trans hbound

end GeneralizedBulk.External.RegularSpectralData
