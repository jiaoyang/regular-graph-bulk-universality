import GaussianWave.BS.GaussianBallConstruction

/-!
# Exact radial propagation of conditional means

The two profiles are the coefficients of a descendant's conditional mean in
the value at its branch root and the value at the preceding parent.  The
identities below calculate cross-branch covariances from the actual wave
recurrence; they are deterministic algebra and assert no Gaussianity of an
unknown process.
-/
noncomputable section
open scoped BigOperators
namespace GaussianWave.BS

def branchMeanA (q energy : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => energy / q
  | n + 2 => (energy * branchMeanA q energy (n + 1) - branchMeanA q energy n) / q

def branchMeanB (q energy : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => -1 / q
  | n + 2 => (energy * branchMeanB q energy (n + 1) - branchMeanB q energy n) / q

theorem branchMean_succ (q energy : ℝ) (n : ℕ) :
    branchMeanA q energy (n + 1) = energy / q * branchMeanA q energy n + branchMeanB q energy n ∧
      branchMeanB q energy (n + 1) = -branchMeanA q energy n / q := by
  induction n with
  | zero => simp [branchMeanA, branchMeanB]
  | succ n ih =>
      constructor
      · change (energy * branchMeanA q energy (n + 1) - branchMeanA q energy n) / q = _
        rw [ih.2]
        ring
      · change (energy * branchMeanB q energy (n + 1) - branchMeanB q energy n) / q = _
        rw [ih.1, ih.2]
        ring

def branchDepth (q : ℕ) : (k : ℕ) → BranchVertex q k → ℕ
  | 0, _ => 0
  | k + 1, v => Sum.elim (fun _ => 0) (fun av => branchDepth q k av.2 + 1) v

theorem siblingFill_zero_noise (m : ℕ) (total : ℝ) :
    siblingFill m total 0 = fun _ => total / (m + 1) := by
  ext a
  refine Fin.cases ?_ (fun i => ?_) a <;> simp [siblingFill]

/-- The actual finite reconstruction with zero innovations has the stated
two-coefficient conditional mean at every descendant. -/
theorem branchBuild_zero_value (m k : ℕ) (energy parent root : ℝ)
    (v : BranchVertex (m + 1) k) :
    branchBuild m k energy parent root 0 v =
      branchMeanA (m + 1) energy (branchDepth (m + 1) k v) * root +
        branchMeanB (m + 1) energy (branchDepth (m + 1) k v) * parent := by
  induction k generalizing parent root with
  | zero => cases v; simp [branchBuild, branchDepth, branchMeanA, branchMeanB]
  | succ k ih =>
      cases v with
      | inl u => simp [branchBuild, branchDepth, branchMeanA, branchMeanB]
      | inr av =>
          change branchBuild m k energy root
            (siblingFill m (energy * root - parent) 0 av.1) 0 av.2 = _
          rw [siblingFill_zero_noise, ih]
          change branchMeanA (m + 1) energy (branchDepth (m + 1) k av.2) *
              ((energy * root - parent) / (m + 1)) +
            branchMeanB (m + 1) energy (branchDepth (m + 1) k av.2) * root =
              branchMeanA (m + 1) energy (branchDepth (m + 1) k av.2 + 1) * root +
                branchMeanB (m + 1) energy (branchDepth (m + 1) k av.2 + 1) * parent
          rw [(branchMean_succ _ _ _).1, (branchMean_succ _ _ _).2]
          ring

theorem branchBuild_mean_noise_decomposition (m k : ℕ) (energy parent root : ℝ)
    (z : BranchInnovation (m + 1) k → ℝ) (v : BranchVertex (m + 1) k) :
    branchBuild m k energy parent root z v =
      branchMeanA (m + 1) energy (branchDepth (m + 1) k v) * root +
        branchMeanB (m + 1) energy (branchDepth (m + 1) k v) * parent +
        branchBuild m k energy 0 0 z v := by
  have h := congrFun (branchBuild_add m k energy parent 0 root 0 0 z) v
  simp only [add_zero, zero_add, Pi.add_apply] at h
  rw [branchBuild_zero_value] at h
  exact h

theorem gaussianBranchBuild_mean_noise_decomposition (m k : ℕ) (energy parent root : ℝ)
    (z : BranchNoise (m + 1) k → ℝ) (v : BranchVertex (m + 1) k) :
    gaussianBranchBuild m k energy parent root z v =
      branchMeanA (m + 1) energy (branchDepth (m + 1) k v) * root +
        branchMeanB (m + 1) energy (branchDepth (m + 1) k v) * parent +
        gaussianBranchBuild m k energy 0 0 z v :=
  branchBuild_mean_noise_decomposition _ _ _ _ _ _ _

theorem branchMean_propagates_spherical (d : ℕ) (energy : ℝ) (t n : ℕ) :
    branchMeanA ((d : ℝ) - 1) energy n * sphericalCovariance d energy (t + 1) +
      branchMeanB ((d : ℝ) - 1) energy n * sphericalCovariance d energy t =
      sphericalCovariance d energy (t + n + 1) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [branchMeanA, branchMeanB]
  | one =>
      change energy / ((d : ℝ) - 1) * sphericalCovariance d energy (t + 1) +
        -1 / ((d : ℝ) - 1) * sphericalCovariance d energy t = _
      rw [show t + 1 + 1 = t + 2 by omega, sphericalCovariance]
      ring
  | more n hn hn1 =>
      change ((energy * branchMeanA ((d : ℝ) - 1) energy (n + 1) -
          branchMeanA ((d : ℝ) - 1) energy n) / ((d : ℝ) - 1)) * _ +
        ((energy * branchMeanB ((d : ℝ) - 1) energy (n + 1) -
          branchMeanB ((d : ℝ) - 1) energy n) / ((d : ℝ) - 1)) * _ = _
      calc
        _ = (energy *
            (branchMeanA ((d : ℝ) - 1) energy (n + 1) * sphericalCovariance d energy (t + 1) +
              branchMeanB ((d : ℝ) - 1) energy (n + 1) * sphericalCovariance d energy t) -
            (branchMeanA ((d : ℝ) - 1) energy n * sphericalCovariance d energy (t + 1) +
              branchMeanB ((d : ℝ) - 1) energy n * sphericalCovariance d energy t)) /
              ((d : ℝ) - 1) := by ring
        _ = (energy * sphericalCovariance d energy (t + (n + 1) + 1) -
            sphericalCovariance d energy (t + n + 1)) / ((d : ℝ) - 1) := by rw [hn, hn1]
        _ = sphericalCovariance d energy (t + (n + 2) + 1) := by
          rw [show t + (n + 2) + 1 = (t + n + 1) + 2 by omega, sphericalCovariance]
          congr 2

theorem branchMean_root_covariance (d : ℕ) (energy : ℝ) (n : ℕ) :
    branchMeanA ((d : ℝ) - 1) energy n * (energy / d) +
      branchMeanB ((d : ℝ) - 1) energy n = sphericalCovariance d energy (n + 1) := by
  simpa only [sphericalCovariance_one, sphericalCovariance_zero, mul_one, Nat.zero_add] using
    branchMean_propagates_spherical d energy 0 n

theorem branchMean_inside_covariance (d : ℕ) (hd : 2 ≤ d) (energy : ℝ) (n : ℕ) :
    branchMeanA ((d : ℝ) - 1) energy n +
      branchMeanB ((d : ℝ) - 1) energy n * (energy / d) =
      sphericalCovariance d energy n := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hq : (d : ℝ) - 1 ≠ 0 := by linarith
  have hz : branchMeanA ((d : ℝ) - 1) energy 0 +
      branchMeanB ((d : ℝ) - 1) energy 0 * (energy / d) = 1 := by
    simp [branchMeanA, branchMeanB]
  have ho : (d : ℝ) * (branchMeanA ((d : ℝ) - 1) energy 1 +
      branchMeanB ((d : ℝ) - 1) energy 1 * (energy / d)) =
      energy * (branchMeanA ((d : ℝ) - 1) energy 0 +
        branchMeanB ((d : ℝ) - 1) energy 0 * (energy / d)) := by
    simp only [branchMeanA, branchMeanB]
    field_simp [hd0, hq]
    ring
  have hr (j : ℕ) :
      (branchMeanA ((d : ℝ) - 1) energy j + branchMeanB ((d : ℝ) - 1) energy j * (energy / d)) +
        ((d : ℝ) - 1) *
          (branchMeanA ((d : ℝ) - 1) energy (j + 2) +
            branchMeanB ((d : ℝ) - 1) energy (j + 2) * (energy / d)) =
        energy * (branchMeanA ((d : ℝ) - 1) energy (j + 1) +
          branchMeanB ((d : ℝ) - 1) energy (j + 1) * (energy / d)) := by
    change (_ + _) + ((d : ℝ) - 1) *
      (((energy * branchMeanA ((d : ℝ) - 1) energy (j + 1) -
          branchMeanA ((d : ℝ) - 1) energy j) / ((d : ℝ) - 1)) +
        ((energy * branchMeanB ((d : ℝ) - 1) energy (j + 1) -
          branchMeanB ((d : ℝ) - 1) energy j) / ((d : ℝ) - 1)) * (energy / d)) = _
    field_simp [hq]
    ring
  simpa only [one_mul] using covariance_eq_scaled_spherical d energy 1 hd0 hq
    (fun j => branchMeanA ((d : ℝ) - 1) energy j +
      branchMeanB ((d : ℝ) - 1) energy j * (energy / d)) hz ho hr n

/-- Distinct child branches have the required radial cross-covariance at
every pair of depths, once their initial sibling covariance is computed. -/
theorem branchMean_cross_covariance (d : ℕ) (energy : ℝ) (n m : ℕ) :
    branchMeanA ((d : ℝ) - 1) energy n * branchMeanA ((d : ℝ) - 1) energy m *
        sphericalCovariance d energy 2 +
      (branchMeanA ((d : ℝ) - 1) energy n * branchMeanB ((d : ℝ) - 1) energy m +
        branchMeanB ((d : ℝ) - 1) energy n * branchMeanA ((d : ℝ) - 1) energy m) *
        (energy / d) +
      branchMeanB ((d : ℝ) - 1) energy n * branchMeanB ((d : ℝ) - 1) energy m =
      sphericalCovariance d energy (n + m + 2) := by
  have hn := branchMean_propagates_spherical d energy 1 n
  have hr := branchMean_root_covariance d energy n
  have hm := branchMean_propagates_spherical d energy (n + 1) m
  simp only [sphericalCovariance_one] at hn
  have hn' : branchMeanA ((d : ℝ) - 1) energy n * sphericalCovariance d energy 2 +
      branchMeanB ((d : ℝ) - 1) energy n * (energy / d) =
      sphericalCovariance d energy (n + 2) := by
    simpa only [show 1 + n + 1 = n + 2 by omega] using hn
  calc
    _ = branchMeanA ((d : ℝ) - 1) energy m *
          (branchMeanA ((d : ℝ) - 1) energy n * sphericalCovariance d energy 2 +
            branchMeanB ((d : ℝ) - 1) energy n * (energy / d)) +
        branchMeanB ((d : ℝ) - 1) energy m *
          (branchMeanA ((d : ℝ) - 1) energy n * (energy / d) +
            branchMeanB ((d : ℝ) - 1) energy n) := by ring
    _ = branchMeanA ((d : ℝ) - 1) energy m * sphericalCovariance d energy (n + 2) +
        branchMeanB ((d : ℝ) - 1) energy m * sphericalCovariance d energy (n + 1) := by rw [hn', hr]
    _ = sphericalCovariance d energy (n + m + 2) := by
      simpa only [show n + 1 + 1 = n + 2 by omega,
        show n + 1 + m + 1 = n + m + 2 by omega] using hm

theorem branchMean_edge_cross_covariance (d : ℕ) (hd : 2 ≤ d) (energy : ℝ) (n m : ℕ) :
    branchMeanA ((d : ℝ) - 1) energy n * branchMeanA ((d : ℝ) - 1) energy m * (energy / d) +
      (branchMeanA ((d : ℝ) - 1) energy n * branchMeanB ((d : ℝ) - 1) energy m +
        branchMeanB ((d : ℝ) - 1) energy n * branchMeanA ((d : ℝ) - 1) energy m) +
      branchMeanB ((d : ℝ) - 1) energy n * branchMeanB ((d : ℝ) - 1) energy m * (energy / d) =
      sphericalCovariance d energy (n + m + 1) := by
  calc
    _ = branchMeanA ((d : ℝ) - 1) energy m *
          (branchMeanA ((d : ℝ) - 1) energy n * (energy / d) +
            branchMeanB ((d : ℝ) - 1) energy n) +
        branchMeanB ((d : ℝ) - 1) energy m *
          (branchMeanA ((d : ℝ) - 1) energy n +
            branchMeanB ((d : ℝ) - 1) energy n * (energy / d)) := by ring
    _ = branchMeanA ((d : ℝ) - 1) energy m * sphericalCovariance d energy (n + 1) +
        branchMeanB ((d : ℝ) - 1) energy m * sphericalCovariance d energy n := by
      rw [branchMean_root_covariance, branchMean_inside_covariance d hd]
    _ = sphericalCovariance d energy (n + m + 1) := branchMean_propagates_spherical d energy n m

end GaussianWave.BS
