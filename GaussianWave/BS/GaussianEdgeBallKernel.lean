import GaussianWave.BS.GaussianVertexBallKernel

/-!
# The actual edge-ball Gaussian law has the wave kernel
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaussianWave.BS

def edgeBallDistance (m k : ℕ) (v w : EdgeBallVertex (m + 2) k) : ℕ :=
  if v.1 = w.1 then branchDistance (m + 1) k v.2 w.2
    else branchDepth (m + 1) k v.2 + branchDepth (m + 1) k w.2 + 1

def edgeWaveCoefficient (m k : ℕ) (energy : ℝ) :
    Matrix (EdgeBallVertex (m + 2) k) (EdgeGaussianInput m k) ℝ :=
  fun bv => forestRowExtension bv.1 (gaussianBranchCoefficient m energy k
    (physicalEdgeMatrix (energy / (m + 2)) bv.1)
    (physicalEdgeMatrix (energy / (m + 2)) (!bv.1)) bv.2)

theorem physicalEdgeMatrix_gram_entry (c : ℝ) (hc : |c| < 1) (a b : Bool) :
    (∑ i, physicalEdgeMatrix c a i * physicalEdgeMatrix c b i) = if a = b then 1 else c := by
  cases a <;> cases b <;> norm_num [physicalEdgeMatrix, Fintype.sum_bool] <;>
    nlinarith [alpha_sq_add_beta_sq c hc, two_alpha_mul_beta c hc]

theorem sum_two_linear_product_general {I : Type*} [Fintype I]
    (r p s q : I → ℝ) (a b c d : ℝ) :
    (∑ i, (a * r i + b * p i) * (c * s i + d * q i)) =
      a * c * (∑ i, r i * s i) + a * d * (∑ i, r i * q i) +
        b * c * (∑ i, p i * s i) + b * d * (∑ i, p i * q i) := by
  calc
    _ = ∑ i, (a * c * (r i * s i) + a * d * (r i * q i) +
        b * c * (p i * s i) + b * d * (p i * q i)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

theorem edgeWaveCoefficient_mulVec (m k : ℕ) (energy : ℝ) (z : EdgeGaussianInput m k → ℝ) :
    (edgeWaveCoefficient m k energy).mulVec z = edgeGaussianMap m k energy z := by
  ext bv
  change finiteLinearForm (forestRowExtension bv.1 _) z = _
  rw [forestRowExtension_linearForm, gaussianBranchCoefficient_linearForm]
  rfl

theorem edgeWaveCoefficient_gram (m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) :
    edgeWaveCoefficient m k energy * (edgeWaveCoefficient m k energy).transpose =
      fun v w => sphericalCovariance (m + 2) energy (edgeBallDistance m k v w) := by
  have hc : |energy / (m + 2 : ℝ)| < 1 := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < m + 2)]
    exact (div_lt_one (by positivity)).mpr he
  let R := physicalEdgeMatrix (energy / (m + 2))
  have hR (a b : Bool) : (∑ i, R a i * R b i) = if a = b then 1 else energy / (m + 2) :=
    physicalEdgeMatrix_gram_entry _ hc a b
  ext v w
  change (∑ s, forestRowExtension v.1 _ s * forestRowExtension w.1 _ s) = _
  by_cases hside : v.1 = w.1
  · rw [hside, forestRowExtension_gram_same]
    have hnorm (a : Bool) : (∑ i, R a i ^ 2) = 1 := by
      simpa only [pow_two, if_pos rfl] using hR a a
    have hcov (a : Bool) : (∑ i, R a i * R (!a) i) = energy / (m + 2) := by
      have hne : a ≠ !a := by cases a <;> decide
      simpa only [if_neg hne] using hR a (!a)
    have h := gaussianBranchCoefficient_gram m k energy he (R w.1) (R (!w.1))
      (hnorm w.1) (hnorm (!w.1)) (hcov w.1) v.2 w.2
    simpa only [edgeBallDistance, if_pos hside] using h
  · rw [forestRowExtension_gram_distinct _ _ hside]
    simp_rw [gaussianBranchCoefficient_old]
    rw [sum_two_linear_product_general]
    have hl : (!v.1) = w.1 := by cases hv : v.1 <;> cases hw : w.1 <;> simp_all
    have hr : (!w.1) = v.1 := by cases hv : v.1 <;> cases hw : w.1 <;> simp_all
    rw [hl, hr, hR, hR, hR, hR, if_neg hside, if_pos rfl, if_pos rfl, if_neg (Ne.symm hside),
      mul_one, mul_one]
    have h := branchMean_edge_cross_covariance (m + 2) (by omega) energy
      (branchDepth (m + 1) k v.2) (branchDepth (m + 1) k w.2)
    norm_num only [Nat.cast_add, Nat.cast_ofNat] at h
    rw [show (m : ℝ) + 2 - 1 = (m : ℝ) + 1 by ring] at h
    simpa only [edgeBallDistance, if_neg hside, add_assoc] using h

theorem edgeGaussianBallLaw_eq_waveFactor (m k : ℕ) (energy : ℝ) :
    edgeGaussianBallLaw m k energy = linearImageGaussian (edgeWaveCoefficient m k energy) := by
  unfold edgeGaussianBallLaw linearImageGaussian
  congr 1
  exact (funext (edgeWaveCoefficient_mulVec m k energy)).symm

theorem edgeGaussianBallLaw_wave_kernel (m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) :
    HasGaussianCovariance (edgeGaussianBallLaw m k energy)
      (fun v w => sphericalCovariance (m + 2) energy (edgeBallDistance m k v w)) := by
  rw [edgeGaussianBallLaw_eq_waveFactor, ← edgeWaveCoefficient_gram m k energy he]
  exact linearImageGaussian_characteristic _

end GaussianWave.BS
