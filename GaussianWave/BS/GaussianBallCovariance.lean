import GaussianWave.BS.GaussianBallConstruction

/-!
# Computed Gaussian covariance of finite recursive balls

All Gaussianity statements here concern the actual independent-noise
construction.  The one-step Gram identities are the deterministic covariance
calculation behind the radial-kernel induction.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianWave.BS

def vertexGaussianMatrix (m k : ℕ) (energy : ℝ) :
    Matrix (VertexBallVertex (m + 2) k) (VertexGaussianInput m k) ℝ :=
  LinearMap.toMatrix' (vertexGaussianMap m k energy)

def edgeGaussianMatrix (m k : ℕ) (energy : ℝ) :
    Matrix (EdgeBallVertex (m + 2) k) (EdgeGaussianInput m k) ℝ :=
  LinearMap.toMatrix' (edgeGaussianMap m k energy)

theorem vertexGaussianMatrix_mulVec (m k : ℕ) (energy : ℝ) (z : VertexGaussianInput m k → ℝ) :
    (vertexGaussianMatrix m k energy).mulVec z = vertexGaussianMap m k energy z := by
  exact congrArg (fun f => f z) (Matrix.toLin'_toMatrix' (vertexGaussianMap m k energy))

theorem edgeGaussianMatrix_mulVec (m k : ℕ) (energy : ℝ) (z : EdgeGaussianInput m k → ℝ) :
    (edgeGaussianMatrix m k energy).mulVec z = edgeGaussianMap m k energy z := by
  exact congrArg (fun f => f z) (Matrix.toLin'_toMatrix' (edgeGaussianMap m k energy))

theorem vertexGaussianBallLaw_eq_linearImage (m k : ℕ) (energy : ℝ) :
    vertexGaussianBallLaw m k energy = linearImageGaussian (vertexGaussianMatrix m k energy) := by
  unfold vertexGaussianBallLaw linearImageGaussian
  congr 1
  exact (funext (vertexGaussianMatrix_mulVec m k energy)).symm

theorem edgeGaussianBallLaw_eq_linearImage (m k : ℕ) (energy : ℝ) :
    edgeGaussianBallLaw m k energy = linearImageGaussian (edgeGaussianMatrix m k energy) := by
  unfold edgeGaussianBallLaw linearImageGaussian
  congr 1
  exact (funext (edgeGaussianMatrix_mulVec m k energy)).symm

theorem vertexGaussianBallLaw_gaussian (m k : ℕ) (energy : ℝ) :
    HasGaussianCovariance (vertexGaussianBallLaw m k energy)
      (vertexGaussianMatrix m k energy * (vertexGaussianMatrix m k energy).transpose) := by
  rw [vertexGaussianBallLaw_eq_linearImage]
  exact linearImageGaussian_characteristic _

theorem edgeGaussianBallLaw_gaussian (m k : ℕ) (energy : ℝ) :
    HasGaussianCovariance (edgeGaussianBallLaw m k energy)
      (edgeGaussianMatrix m k energy * (edgeGaussianMatrix m k energy).transpose) := by
  rw [edgeGaussianBallLaw_eq_linearImage]
  exact linearImageGaussian_characteristic _

def centeredNoiseRow (q : ℕ) (a : Fin q) : Fin q → ℝ :=
  fun i => (if i = a then 1 else 0) - 1 / q

theorem centeredNoiseRow_apply (q : ℕ) (a : Fin q) (z : Fin q → ℝ) :
    finiteLinearForm (centeredNoiseRow q a) z = centeredNoise z a := by
  simp only [finiteLinearForm, centeredNoiseRow, sub_mul, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  simp [centeredNoise, div_eq_mul_inv, mul_comm]

theorem centeredNoiseRow_gram (q : ℕ) (hq : 0 < q) (a b : Fin q) :
    (∑ i, centeredNoiseRow q a i * centeredNoiseRow q b i) =
      (if a = b then 1 else 0) - 1 / (q : ℝ) := by
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have he (i : Fin q) : centeredNoiseRow q a i * centeredNoiseRow q b i =
      (if i = a then 1 else 0) * (if i = b then 1 else 0) -
      (1 / (q : ℝ)) * (if i = a then 1 else 0) -
      (1 / (q : ℝ)) * (if i = b then 1 else 0) + (1 / (q : ℝ)) ^ 2 := by
    unfold centeredNoiseRow
    ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [ite_mul, zero_mul, one_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte, Finset.sum_ite_eq, eq_comm]
  split_ifs <;> field_simp <;> ring

def branchConditionalMean {I : Type*} (q : ℕ) (energy : ℝ) (root parent : I → ℝ) : I → ℝ :=
  fun i => (energy * root i - parent i) / q

def siblingExtensionMatrix {I : Type*} (q : ℕ) (energy scale : ℝ) (root parent : I → ℝ) :
    Matrix (Fin q) (I ⊕ Fin q) ℝ :=
  fun a => Sum.elim (branchConditionalMean q energy root parent)
    (fun j => scale * centeredNoiseRow q a j)

theorem siblingExtensionMatrix_gram {I : Type*} [Fintype I]
    (q : ℕ) (hq : 0 < q) (energy scale : ℝ) (root parent : I → ℝ) (a b : Fin q) :
    (∑ i, siblingExtensionMatrix q energy scale root parent a i *
      siblingExtensionMatrix q energy scale root parent b i) =
      (∑ i, (branchConditionalMean q energy root parent i) ^ 2) +
        scale ^ 2 * ((if a = b then 1 else 0) - 1 / (q : ℝ)) := by
  rw [Fintype.sum_sum_type]
  simp only [siblingExtensionMatrix, Sum.elim_inl, Sum.elim_inr]
  have hs : (∑ i, (scale * centeredNoiseRow q a i) * (scale * centeredNoiseRow q b i)) =
      scale ^ 2 * ∑ i, centeredNoiseRow q a i * centeredNoiseRow q b i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs, centeredNoiseRow_gram q hq]
  simp only [pow_two]

theorem branchConditionalMean_norm_sq {I : Type*} [Fintype I]
    (q : ℕ) (energy c : ℝ) (root parent : I → ℝ)
    (hr : (∑ i, root i ^ 2) = 1) (hp : (∑ i, parent i ^ 2) = 1)
    (hrp : (∑ i, root i * parent i) = c) :
    (∑ i, (branchConditionalMean q energy root parent i) ^ 2) =
      (energy ^ 2 + 1 - 2 * energy * c) / (q : ℝ) ^ 2 := by
  have he (i : I) : (branchConditionalMean q energy root parent i) ^ 2 =
      (energy ^ 2 * root i ^ 2 + parent i ^ 2 - 2 * energy * (root i * parent i)) /
        (q : ℝ) ^ 2 := by
    unfold branchConditionalMean
    ring
  simp_rw [he]
  rw [← Finset.sum_div]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hr, hp, hrp]
  ring

/-- One actual attachment preserves unit variance and the prescribed
distance-two covariance. -/
theorem siblingExtensionMatrix_wave_gram {I : Type*} [Fintype I]
    (m : ℕ) (energy : ℝ) (he : |energy| < (m + 2 : ℝ)) (root parent : I → ℝ)
    (hr : (∑ i, root i ^ 2) = 1) (hp : (∑ i, parent i ^ 2) = 1)
    (hrp : (∑ i, root i * parent i) = energy / (m + 2)) (a b : Fin (m + 1)) :
    (∑ i, siblingExtensionMatrix (m + 1) energy
      (Real.sqrt (siblingVariance (m + 2) energy)) root parent a i *
      siblingExtensionMatrix (m + 1) energy
      (Real.sqrt (siblingVariance (m + 2) energy)) root parent b i) =
      if a = b then 1 else GaussianWave.sphericalCovariance (m + 2) energy 2 := by
  have hv : 0 ≤ siblingVariance (m + 2) energy :=
    (siblingVariance_pos (m + 2) (by omega) energy (by
      simpa only [Nat.cast_add, Nat.cast_ofNat] using he)).le
  rw [siblingExtensionMatrix_gram _ (by omega),
    branchConditionalMean_norm_sq _ _ _ _ _ hr hp hrp, Real.sq_sqrt hv]
  have hd : (m + 2 : ℝ) ≠ 0 := by positivity
  have hq : (m + 1 : ℝ) ≠ 0 := by positivity
  rw [GaussianWave.sphericalCovariance_two _ _ (by exact_mod_cast (by omega : m + 2 ≠ 0))]
  unfold siblingVariance
  norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  rw [show (m : ℝ) + 2 - 1 = (m : ℝ) + 1 by ring]
  split_ifs <;> field_simp [hd, hq] <;> ring

end GaussianWave.BS
