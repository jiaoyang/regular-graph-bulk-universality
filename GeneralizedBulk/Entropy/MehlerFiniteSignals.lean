import GeneralizedBulk.Entropy.MehlerKernelCalculus

/-! The first two smoothing coefficients cancel for an actual normalized
finite signal with mean zero and identity covariance. -/
noncomputable section
open scoped BigOperators

namespace GeneralizedBulk.Entropy.Mehler
variable {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S]
variable (weight : S → ℝ) (signal : S → I → ℝ)

def finiteMixtureKernel (a : ℝ) (z : I → ℝ) : ℝ :=
  ∑ s, weight s * vectorKernel a (signal s) z

def finiteMixtureKernelD1 (a : ℝ) (z : I → ℝ) : ℝ :=
  ∑ s, weight s * kernelD1 (Fintype.card I) (∑ i, z i * signal s i)
    (∑ i, ((signal s i) ^ 2 + (z i) ^ 2)) a

def finiteMixtureKernelD2 (a : ℝ) (z : I → ℝ) : ℝ :=
  ∑ s, weight s * kernelD2 (Fintype.card I) (∑ i, z i * signal s i)
    (∑ i, ((signal s i) ^ 2 + (z i) ^ 2)) a

def finiteMixtureKernelD3 (a : ℝ) (z : I → ℝ) : ℝ :=
  ∑ s, weight s * kernelD3 (Fintype.card I) (∑ i, z i * signal s i)
    (∑ i, ((signal s i) ^ 2 + (z i) ^ 2)) a

theorem finiteMixtureKernel_nonneg (hweight : ∀ s, 0 ≤ weight s) (a : ℝ) (z : I → ℝ) :
    0 ≤ finiteMixtureKernel weight signal a z := by
  exact Finset.sum_nonneg (fun s _ => mul_nonneg (hweight s) (kernel_pos _ _ _ _).le)

theorem hasDerivAt_finiteMixtureKernel (a : ℝ) (ha : 1 - a ^ 2 ≠ 0) (z : I → ℝ) :
    HasDerivAt (fun t => finiteMixtureKernel weight signal t z)
      (finiteMixtureKernelD1 weight signal a z) a := by
  exact HasDerivAt.sum (fun s _ => (hasDerivAt_kernel _ _ _ a ha).const_mul (weight s))

theorem hasDerivAt_finiteMixtureKernelD1 (a : ℝ) (ha : 1 - a ^ 2 ≠ 0) (z : I → ℝ) :
    HasDerivAt (fun t => finiteMixtureKernelD1 weight signal t z)
      (finiteMixtureKernelD2 weight signal a z) a := by
  exact HasDerivAt.sum (fun s _ => (hasDerivAt_kernelD1 _ _ _ a ha).const_mul (weight s))

theorem hasDerivAt_finiteMixtureKernelD2 (a : ℝ) (ha : 1 - a ^ 2 ≠ 0) (z : I → ℝ) :
    HasDerivAt (fun t => finiteMixtureKernelD2 weight signal t z)
      (finiteMixtureKernelD3 weight signal a z) a := by
  exact HasDerivAt.sum (fun s _ => (hasDerivAt_kernelD2 _ _ _ a ha).const_mul (weight s))

variable (hnorm : ∑ s, weight s = 1)
variable (hmean : ∀ i, ∑ s, weight s * signal s i = 0)
variable (hcov : ∀ i j, ∑ s, weight s * signal s i * signal s j = if i = j then 1 else 0)

include hmean in
theorem weighted_cross (z : I → ℝ) :
    (∑ s, weight s * (∑ i, z i * signal s i)) = 0 := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have he (i : I) : (∑ s, weight s * (z i * signal s i)) =
      z i * ∑ s, weight s * signal s i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    ring
  simp_rw [he, hmean, mul_zero]
  simp

include hcov in
theorem weighted_cross_sq (z : I → ℝ) :
    (∑ s, weight s * (∑ i, z i * signal s i) ^ 2) = ∑ i, z i ^ 2 := by
  classical
  have hexpand (s : S) : (∑ i, z i * signal s i) ^ 2 =
      ∑ i, ∑ j, (z i * z j) * (signal s i * signal s j) := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [hexpand, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  have he (j : I) : (∑ s, weight s * ((z i * z j) * (signal s i * signal s j))) =
      (z i * z j) * ∑ s, weight s * signal s i * signal s j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    ring
  simp_rw [he, hcov]
  simp [pow_two]

include hnorm hcov in
theorem weighted_energy (z : I → ℝ) :
    (∑ s, weight s * (∑ i, ((signal s i) ^ 2 + (z i) ^ 2))) =
      (Fintype.card I : ℝ) + ∑ i, (z i) ^ 2 := by
  simp_rw [Finset.mul_sum, mul_add]
  rw [Finset.sum_comm]
  have he (i : I) : (∑ s, (weight s * (signal s i) ^ 2 + weight s * (z i) ^ 2)) =
      1 + (z i) ^ 2 := by
    rw [Finset.sum_add_distrib]
    have hc : (∑ s, weight s * (signal s i) ^ 2) = 1 := by
      simpa only [pow_two, mul_assoc, ite_true] using hcov i i
    rw [hc, ← Finset.sum_mul, hnorm, one_mul]
  simp_rw [he]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

include hnorm in
theorem finiteMixtureKernel_zero (z : I → ℝ) : finiteMixtureKernel weight signal 0 z = 1 := by
  simpa [finiteMixtureKernel, vectorKernel] using hnorm

include hmean in
theorem finiteMixtureKernelD1_zero (z : I → ℝ) : finiteMixtureKernelD1 weight signal 0 z = 0 := by
  simpa [finiteMixtureKernelD1] using weighted_cross weight signal hmean z

include hnorm hcov in
theorem finiteMixtureKernelD2_zero (z : I → ℝ) : finiteMixtureKernelD2 weight signal 0 z = 0 := by
  simp only [finiteMixtureKernelD2, kernelD2_zero]
  simp_rw [mul_add, mul_sub]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [weighted_cross_sq weight signal hcov z, weighted_energy weight signal hnorm hcov z,
    ← Finset.sum_mul, hnorm]
  ring

end GeneralizedBulk.Entropy.Mehler
