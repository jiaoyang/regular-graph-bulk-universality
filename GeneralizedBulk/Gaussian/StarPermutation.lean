import GeneralizedBulk.Gaussian.StarNormalProjection
import GeneralizedBulk.Matrix.ProjectionRescale

/-! Neighbor permutations preserve the literal star reference and its normal rescaling. -/
noncomputable section
namespace GeneralizedBulk.Gaussian
open GeneralizedBulk.External.RegularSpectralData GeneralizedBulk.Covariance

def starLeafPermutation {d : ℕ} (p : Equiv.Perm (Fin d)) : Equiv.Perm (Fin (d+1)) :=
  (finSuccEquiv d).trans ((Equiv.optionCongr p).trans (finSuccEquiv d).symm)

@[simp] theorem starLeafPermutation_zero {d : ℕ} (p : Equiv.Perm (Fin d)) : starLeafPermutation p 0=0 := by
  simp [starLeafPermutation]

@[simp] theorem starLeafPermutation_succ {d : ℕ} (p : Equiv.Perm (Fin d)) (j : Fin d) :
    starLeafPermutation p j.succ=(p j).succ := by simp [starLeafPermutation]

theorem starWaveCovariance_leaf_permutation {d : ℕ} (p : Equiv.Perm (Fin d)) (E : ℝ) :
    (starWaveCovariance d E).submatrix (starLeafPermutation p) (starLeafPermutation p)=starWaveCovariance d E := by
  ext i j
  refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j <;>
    simp [Matrix.submatrix_apply,starWaveCovariance]

theorem normalizedStarNormal_leaf_permutation {d : ℕ} (p : Equiv.Perm (Fin d)) (E : ℝ) (j : Fin (d+1)) :
    normalizedStarNormal d E (starLeafPermutation p j)=normalizedStarNormal d E j := by
  refine Fin.cases ?_ (fun a => ?_) j <;> simp [normalizedStarNormal,entropyStarNormal]

theorem starNormalProjection_leaf_permutation {d : ℕ} (p : Equiv.Perm (Fin d)) (E : ℝ) :
    (starNormalProjection d E).submatrix (starLeafPermutation p) (starLeafPermutation p)=starNormalProjection d E := by
  ext i j
  simp [Matrix.submatrix_apply,starNormalProjection,unitNormalProjection,normalizedStarNormal_leaf_permutation]

theorem starRescale_leaf_permutation {d : ℕ} (p : Equiv.Perm (Fin d)) (E t : ℝ) :
    (projectionRescale (starNormalProjection d E) t).submatrix (starLeafPermutation p) (starLeafPermutation p)=
      projectionRescale (starNormalProjection d E) t := by
  ext i j
  have hp := congrFun (congrFun (starNormalProjection_leaf_permutation p E) i) j
  change starNormalProjection d E (starLeafPermutation p i) (starLeafPermutation p j)=starNormalProjection d E i j at hp
  have hi : (1 : Matrix (Fin (d+1)) (Fin (d+1)) ℝ) (starLeafPermutation p i) (starLeafPermutation p j) =
      (1 : Matrix (Fin (d+1)) (Fin (d+1)) ℝ) i j := by simp [Matrix.one_apply]
  simpa only [Matrix.submatrix_apply,projectionRescale,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,hi,hp]

theorem starRescale_permuted_covariance {d : ℕ} (p : Equiv.Perm (Fin d)) (E t : ℝ)
    (Q : Matrix (Fin (d+1)) (Fin (d+1)) ℝ) :
    let R := projectionRescale (starNormalProjection d E) t
    R*Q.submatrix (starLeafPermutation p) (starLeafPermutation p)*R=
      (R*Q*R).submatrix (starLeafPermutation p) (starLeafPermutation p) := by
  dsimp only
  rw [← Matrix.submatrix_mul_equiv _ _ _ (starLeafPermutation p) _,
    ← Matrix.submatrix_mul_equiv _ _ _ (starLeafPermutation p) _,
    starRescale_leaf_permutation]

end GeneralizedBulk.Gaussian
