import GaussianWave.BS.GaussianEdgeBallKernel

/-!
# Orthogonal energy decomposition of the Gaussian reconstruction

The recursive squared norm separates all independent centered sibling-noise
blocks.  This is the finite linear-algebra route to the Gaussian reference
determinant; no covariance eigenvalue or entropy asymptotic is assumed.
-/
noncomputable section
open scoped BigOperators
namespace GaussianWave.BS

def branchEnergyCoefficients (q energy : ℝ) : ℕ → ℝ × ℝ × ℝ
  | 0 => (1, 0, 0)
  | k + 1 =>
      let a := (branchEnergyCoefficients q energy k).1
      let b := (branchEnergyCoefficients q energy k).2.1
      let c := (branchEnergyCoefficients q energy k).2.2
      (1 + a * energy ^ 2 / q + 2 * b * energy + q * c,
        -a * energy / q - b, a / q)

def branchMeanEnergy (q energy : ℝ) (k : ℕ) (root parent : ℝ) : ℝ :=
  (branchEnergyCoefficients q energy k).1 * root ^ 2 +
    2 * (branchEnergyCoefficients q energy k).2.1 * root * parent +
    (branchEnergyCoefficients q energy k).2.2 * parent ^ 2

def branchNoiseEnergy (m : ℕ) (energy : ℝ) : (k : ℕ) → (BranchNoise (m + 1) k → ℝ) → ℝ
  | 0, _ => 0
  | k + 1, z => siblingVariance (m + 2) energy *
      (branchEnergyCoefficients (m + 1) energy k).1 *
        ∑ a, centeredNoise (fun i => z (Sum.inl i)) a ^ 2 +
      ∑ a, branchNoiseEnergy m energy k (fun j => z (Sum.inr (a, j)))

theorem sum_centered_shift_square (m : ℕ) (mean scale : ℝ) (z : Fin (m + 1) → ℝ) :
    (∑ a, (mean + scale * centeredNoise z a) ^ 2) =
      (m + 1 : ℝ) * mean ^ 2 + scale ^ 2 * ∑ a, centeredNoise z a ^ 2 := by
  have he (a : Fin (m + 1)) : (mean + scale * centeredNoise z a) ^ 2 =
      mean ^ 2 + (2 * mean * scale) * centeredNoise z a + scale ^ 2 * centeredNoise z a ^ 2 := by ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, sum_centeredNoise (m + 1) (by omega),
    mul_zero, add_zero, Nat.cast_add, Nat.cast_one]

theorem sum_branchMeanEnergy (m k : ℕ) (energy root parent scale : ℝ)
    (z : Fin (m + 1) → ℝ) :
    (∑ a, branchMeanEnergy (m + 1) energy k
      ((energy * root - parent) / (m + 1) + scale * centeredNoise z a) root) =
      branchMeanEnergy (m + 1) energy (k + 1) root parent - root ^ 2 +
        (branchEnergyCoefficients (m + 1) energy k).1 * scale ^ 2 *
          ∑ a, centeredNoise z a ^ 2 := by
  have he (a : Fin (m + 1)) : branchMeanEnergy (m + 1) energy k
      ((energy * root - parent) / (m + 1) + scale * centeredNoise z a) root =
      (branchEnergyCoefficients (m + 1) energy k).1 *
          (((energy * root - parent) / (m + 1) + scale * centeredNoise z a) ^ 2) +
        (2 * (branchEnergyCoefficients (m + 1) energy k).2.1 * root) *
          ((energy * root - parent) / (m + 1) + scale * centeredNoise z a) +
        (branchEnergyCoefficients (m + 1) energy k).2.2 * root ^ 2 := by
    unfold branchMeanEnergy
    ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [sum_centered_shift_square]
  simp only [sum_centeredNoise (m + 1) (by omega), mul_zero, add_zero]
  unfold branchMeanEnergy
  simp only [branchEnergyCoefficients, Nat.cast_add, Nat.cast_one]
  have hq : (m : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hq]
  ring

/-- Every centered sibling block is orthogonal, in the ambient finite-ball
Euclidean norm, to all the other innovation blocks and to the boundary mean. -/
theorem gaussianBranchBuild_energy (m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) (parent root : ℝ) (z : BranchNoise (m + 1) k → ℝ) :
    (∑ v, gaussianBranchBuild m k energy parent root z v ^ 2) =
      branchMeanEnergy (m + 1) energy k root parent + branchNoiseEnergy m energy k z := by
  induction k generalizing parent root with
  | zero => simp [gaussianBranchBuild, branchBuild, BranchVertex, branchMeanEnergy,
      branchEnergyCoefficients, branchNoiseEnergy]
  | succ k ih =>
      change (∑ v : Unit ⊕ (Fin (m + 1) × BranchVertex (m + 1) k),
        gaussianBranchBuild m (k + 1) energy parent root z v ^ 2) = _
      rw [Fintype.sum_sum_type]
      simp only [Fintype.sum_prod_type]
      have hroot : (∑ u : Unit, gaussianBranchBuild m (k + 1) energy parent root z (Sum.inl u) ^ 2) = root ^ 2 := by
        simp [gaussianBranchBuild, branchBuild]
      rw [hroot]
      simp_rw [gaussianBranchBuild_child, ih]
      rw [Finset.sum_add_distrib, sum_branchMeanEnergy]
      have hv : 0 ≤ siblingVariance (m + 2) energy :=
        (siblingVariance_pos (m + 2) (by omega) energy (by
          simpa only [Nat.cast_add, Nat.cast_ofNat] using he)).le
      rw [Real.sq_sqrt hv]
      change _ = branchMeanEnergy (m + 1) energy (k + 1) root parent +
        (siblingVariance (m + 2) energy * (branchEnergyCoefficients (m + 1) energy k).1 *
          (∑ a, centeredNoise (fun i => z (Sum.inl i)) a ^ 2) +
          ∑ a, branchNoiseEnergy m energy k (fun j => z (Sum.inr (a, j))))
      ring

theorem branchNoiseEnergy_zero (m k : ℕ) (energy : ℝ) :
    branchNoiseEnergy m energy k 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have ih' : branchNoiseEnergy m energy k (fun _ => 0) = 0 := ih
      change siblingVariance (m + 2) energy * (branchEnergyCoefficients (m + 1) energy k).1 *
        (∑ a, centeredNoise (fun _ => 0) a ^ 2) +
          (∑ a : Fin (m + 1), branchNoiseEnergy m energy k (fun _ => 0)) = 0
      simp only [centeredNoise, Finset.sum_const_zero, zero_div, sub_self, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, ih', add_zero]

theorem gaussianBranchBuild_zero_value (m k : ℕ) (energy parent root : ℝ)
    (v : BranchVertex (m + 1) k) :
    gaussianBranchBuild m k energy parent root 0 v =
      branchMeanA (m + 1) energy (branchDepth (m + 1) k v) * root +
        branchMeanB (m + 1) energy (branchDepth (m + 1) k v) * parent := by
  change branchBuild m k energy parent root
    (branchNoiseInnovationLinear m k (Real.sqrt (siblingVariance (m + 2) energy)) 0) v = _
  rw [map_zero]
  exact branchBuild_zero_value _ _ _ _ _ _

theorem sum_branchDepth (q k : ℕ) (f : ℕ → ℝ) :
    (∑ v : BranchVertex q k, f (branchDepth q k v)) =
      ∑ n ∈ Finset.range (k + 1), (q : ℝ) ^ n * f n := by
  induction k generalizing f with
  | zero => simp [BranchVertex, branchDepth]
  | succ k ih =>
      change (∑ v : Unit ⊕ (Fin q × BranchVertex q k), f (branchDepth q (k + 1) v)) = _
      simp only [Fintype.sum_sum_type, branchDepth, Sum.elim_inl, Sum.elim_inr,
        Fintype.sum_unique, Fintype.sum_prod_type]
      rw [ih (fun n => f (n + 1))]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      conv_rhs => rw [Finset.sum_range_succ']
      simp only [pow_zero, one_mul, pow_succ', ← Finset.mul_sum]
      simp only [Finset.mul_sum, mul_assoc]
      ring

/-- The three boundary quadratic coefficients are actual finite sums of the
radial conditional-mean profiles. -/
theorem branchMeanEnergy_eq_profile_sum (m k : ℕ) (energy : ℝ)
    (he : |energy| < (m + 2 : ℝ)) (root parent : ℝ) :
    branchMeanEnergy (m + 1) energy k root parent =
      ∑ n ∈ Finset.range (k + 1), (m + 1 : ℝ) ^ n *
        (branchMeanA (m + 1) energy n * root + branchMeanB (m + 1) energy n * parent) ^ 2 := by
  have h := gaussianBranchBuild_energy m k energy he parent root 0
  rw [branchNoiseEnergy_zero, add_zero] at h
  simp_rw [gaussianBranchBuild_zero_value] at h
  calc
    _ = ∑ v : BranchVertex (m + 1) k,
        (branchMeanA (m + 1) energy (branchDepth (m + 1) k v) * root +
          branchMeanB (m + 1) energy (branchDepth (m + 1) k v) * parent) ^ 2 := h.symm
    _ = _ := by
      simpa only [Nat.cast_add, Nat.cast_one] using sum_branchDepth (m + 1) k
        (fun n => (branchMeanA (m + 1) energy n * root + branchMeanB (m + 1) energy n * parent) ^ 2)

end GaussianWave.BS
