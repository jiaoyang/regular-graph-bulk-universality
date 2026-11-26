import GaussianWave.BS.GaussianForestGram

/-!
# The actual vertex-ball Gaussian law has the wave kernel

The Gaussian characteristic function is proved for the concrete finite
independent-noise law.  Radial covariance is computed, not assumed.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianWave.BS

theorem vertexGaussianMap_root_eq_physical (m k : ℕ) (energy : ℝ)
    (hne : energy ≠ (m + 2 : ℝ)) (z : VertexGaussianInput m k → ℝ) :
    vertexInnovationRoot m k energy (vertexGaussianInnovation m k energy z) =
      physicalStarMap (m + 2) (energy / (m + 2)) (fun j => z (Sum.inl j)) 0 := by
  let y := fun j : Fin (m + 2) => z (Sum.inl j)
  let x : VertexBallVertex (m + 2) 0 → ℝ := Sum.elim
    (fun _ => physicalStarMap (m + 2) (energy / (m + 2)) y 0)
    (fun av => physicalStarMap (m + 2) (energy / (m + 2)) y av.1.succ)
  have he : ((m + 2 : ℕ) : ℝ) * (energy / (m + 2 : ℝ)) = energy := by
    norm_num only [Nat.cast_add, Nat.cast_ofNat]
    field_simp
  have hx : VertexBallEigenrelation m 0 energy x := by
    constructor
    · change (∑ a : Fin (m + 2), physicalStarMap (m + 2) (energy / (m + 2)) y a.succ) =
        energy * physicalStarMap (m + 2) (energy / (m + 2)) y 0
      rw [physicalStarMap_eigenrelation _ (by omega), he]
    · intro a
      trivial
  exact vertexInnovationRoot_extract m 0 energy hne x hx

theorem vertexGaussianMap_branch_eq (m k : ℕ) (energy : ℝ)
    (hne : energy ≠ (m + 2 : ℝ)) (z : VertexGaussianInput m k → ℝ)
    (a : Fin (m + 2)) (v : BranchVertex (m + 1) k) :
    vertexGaussianMap m k energy z (Sum.inr (a, v)) =
      gaussianBranchBuild m k energy
        (physicalStarMap (m + 2) (energy / (m + 2)) (fun j => z (Sum.inl j)) 0)
        (physicalStarMap (m + 2) (energy / (m + 2)) (fun j => z (Sum.inl j)) a.succ)
        (fun j => z (Sum.inr (a, j))) v := by
  change branchBuild m k energy (vertexInnovationRoot m k energy _)
    (vertexInnovationRoot m k energy _ +
      (physicalStarMap (m + 2) (energy / (m + 2)) (fun j => z (Sum.inl j)) a.succ -
        physicalStarMap (m + 2) (energy / (m + 2)) (fun j => z (Sum.inl j)) 0)) _ v = _
  erw [vertexGaussianMap_root_eq_physical m k energy hne z]
  have hh : physicalStarMap (m + 2) (energy / (m + 2)) (fun j => z (Sum.inl j)) 0 +
      (physicalStarMap (m + 2) (energy / (m + 2)) (fun j => z (Sum.inl j)) a.succ -
        physicalStarMap (m + 2) (energy / (m + 2)) (fun j => z (Sum.inl j)) 0) =
      physicalStarMap (m + 2) (energy / (m + 2)) (fun j => z (Sum.inl j)) a.succ := by ring
  rw [hh]
  rfl

def vertexWaveCoefficient (m k : ℕ) (energy : ℝ) :
    Matrix (VertexBallVertex (m + 2) k) (VertexGaussianInput m k) ℝ :=
  vertexForestCoefficient m k energy
    (physicalStarMatrix (m + 2) (energy / (m + 2)) 0)
    (fun a => physicalStarMatrix (m + 2) (energy / (m + 2)) a.succ)

theorem vertexWaveCoefficient_mulVec (m k : ℕ) (energy : ℝ)
    (hne : energy ≠ (m + 2 : ℝ)) (z : VertexGaussianInput m k → ℝ) :
    (vertexWaveCoefficient m k energy).mulVec z = vertexGaussianMap m k energy z := by
  ext v
  cases v with
  | inl u =>
      change finiteLinearForm (oldBranchRow _) z = vertexInnovationRoot m k energy _
      rw [oldBranchRow_linearForm]
      erw [vertexGaussianMap_root_eq_physical m k energy hne z]
      rfl
  | inr av =>
      change finiteLinearForm (forestRowExtension av.1 _) z = _
      rw [forestRowExtension_linearForm, gaussianBranchCoefficient_linearForm,
        vertexGaussianMap_branch_eq m k energy hne z]
      rfl

theorem vertexWaveCoefficient_gram (m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) :
    vertexWaveCoefficient m k energy * (vertexWaveCoefficient m k energy).transpose =
      fun v w => sphericalCovariance (m + 2) energy (vertexBallDistance m k v w) := by
  have hc : |energy / (m + 2 : ℝ)| < 1 := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < m + 2)]
    exact (div_lt_one (by positivity)).mpr he
  have hgram := physicalStarMatrix_gram (m + 2) (by omega) (energy / (m + 2 : ℝ)) hc
  have heq : ((m + 2 : ℕ) : ℝ) * (energy / (m + 2 : ℝ)) = energy := by
    norm_num only [Nat.cast_add, Nat.cast_ofNat]
    field_simp
  rw [heq] at hgram
  have hr : (∑ i, physicalStarMatrix (m + 2) (energy / (m + 2)) 0 i ^ 2) = 1 := by
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, RegularEigenData.starWaveCovariance,
      Fin.cases_zero, pow_two] using congrArg (fun M => M 0 0) hgram
  have hrl (a : Fin (m + 2)) :
      (∑ i, physicalStarMatrix (m + 2) (energy / (m + 2)) 0 i *
        physicalStarMatrix (m + 2) (energy / (m + 2)) a.succ i) = energy / (m + 2) := by
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, RegularEigenData.starWaveCovariance,
      Fin.cases_zero, Fin.cases_succ, Nat.cast_add, Nat.cast_ofNat] using
        congrArg (fun M => M 0 a.succ) hgram
  have hll (a b : Fin (m + 2)) :
      (∑ i, physicalStarMatrix (m + 2) (energy / (m + 2)) a.succ i *
        physicalStarMatrix (m + 2) (energy / (m + 2)) b.succ i) =
      if a = b then 1 else sphericalCovariance (m + 2) energy 2 := by
    rw [sphericalCovariance_two _ _ (by positivity)]
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, RegularEigenData.starWaveCovariance,
      Fin.cases_succ, Nat.cast_add, Nat.cast_ofNat] using
        congrArg (fun M => M a.succ b.succ) hgram
  ext v w
  exact vertexForestCoefficient_gram m k energy he _ _ hr hrl hll v w

theorem vertexGaussianBallLaw_eq_waveFactor (m k : ℕ) (energy : ℝ)
    (hne : energy ≠ (m + 2 : ℝ)) :
    vertexGaussianBallLaw m k energy = linearImageGaussian (vertexWaveCoefficient m k energy) := by
  unfold vertexGaussianBallLaw linearImageGaussian
  congr 1
  exact (funext (vertexWaveCoefficient_mulVec m k energy hne)).symm

theorem vertexGaussianBallLaw_wave_kernel (m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) :
    HasGaussianCovariance (vertexGaussianBallLaw m k energy)
      (fun v w => sphericalCovariance (m + 2) energy (vertexBallDistance m k v w)) := by
  have hne : energy ≠ (m + 2 : ℝ) := ne_of_lt ((le_abs_self energy).trans_lt he)
  rw [vertexGaussianBallLaw_eq_waveFactor m k energy hne, ← vertexWaveCoefficient_gram m k energy he]
  exact linearImageGaussian_characteristic _

end GaussianWave.BS
