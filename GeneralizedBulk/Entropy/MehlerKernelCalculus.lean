import Mathlib

/-! Direct calculus of the genuine finite-dimensional Mehler density kernel. -/
noncomputable section
open scoped BigOperators ContDiff

namespace GeneralizedBulk.Entropy.Mehler

def logKernel (dim cross energy a : ℝ) : ℝ :=
  -(dim / 2) * Real.log (1 - a ^ 2) +
    (2 * a * cross - a ^ 2 * energy) / (2 * (1 - a ^ 2))

def logKernelD1 (dim cross energy a : ℝ) : ℝ :=
  dim * a / (1 - a ^ 2) + ((1 + a ^ 2) * cross - a * energy) / (1 - a ^ 2) ^ 2

def logKernelD2 (dim cross energy a : ℝ) : ℝ :=
  dim * (1 + a ^ 2) / (1 - a ^ 2) ^ 2 +
    ((6 * a + 2 * a ^ 3) * cross - (1 + 3 * a ^ 2) * energy) / (1 - a ^ 2) ^ 3

def logKernelD3 (dim cross energy a : ℝ) : ℝ :=
  dim * (6 * a + 2 * a ^ 3) / (1 - a ^ 2) ^ 3 +
    ((6 + 36 * a ^ 2 + 6 * a ^ 4) * cross - (12 * a + 12 * a ^ 3) * energy) /
      (1 - a ^ 2) ^ 4

def kernel (dim cross energy a : ℝ) : ℝ := Real.exp (logKernel dim cross energy a)

theorem kernel_pos (dim cross energy a : ℝ) : 0 < kernel dim cross energy a :=
  Real.exp_pos _

theorem hasDerivAt_logKernel (dim cross energy a : ℝ) (ha : 1 - a ^ 2 ≠ 0) :
    HasDerivAt (logKernel dim cross energy) (logKernelD1 dim cross energy a) a := by
  have hd := (hasDerivAt_const a (1 : ℝ)).sub ((hasDerivAt_id a).pow 2)
  have hn := (((hasDerivAt_id a).const_mul 2).mul_const cross).sub
    (((hasDerivAt_id a).pow 2).mul_const energy)
  convert ((hd.log ha).const_mul (-(dim / 2))).add
    (hn.div (hd.const_mul 2) (mul_ne_zero (by norm_num) ha)) using 1
  dsimp [logKernelD1]
  field_simp
  ring

theorem hasDerivAt_logKernelD1 (dim cross energy a : ℝ) (ha : 1 - a ^ 2 ≠ 0) :
    HasDerivAt (logKernelD1 dim cross energy) (logKernelD2 dim cross energy a) a := by
  have hid := hasDerivAt_id a
  have hd := (hasDerivAt_const a (1 : ℝ)).sub (hid.pow 2)
  have hn := (((hasDerivAt_const a (1 : ℝ)).add (hid.pow 2)).mul_const cross).sub
    (hid.mul_const energy)
  convert ((hid.const_mul dim).div hd ha).add
    (hn.div (hd.pow 2) (pow_ne_zero 2 ha)) using 1
  dsimp [logKernelD2]
  field_simp
  ring

theorem hasDerivAt_logKernelD2 (dim cross energy a : ℝ) (ha : 1 - a ^ 2 ≠ 0) :
    HasDerivAt (logKernelD2 dim cross energy) (logKernelD3 dim cross energy a) a := by
  have hid := hasDerivAt_id a
  have hd := (hasDerivAt_const a (1 : ℝ)).sub (hid.pow 2)
  have hn1 := ((hasDerivAt_const a (1 : ℝ)).add (hid.pow 2)).const_mul dim
  have hn2 := (((hid.const_mul 6).add ((hid.pow 3).const_mul 2)).mul_const cross).sub
    (((hasDerivAt_const a (1 : ℝ)).add ((hid.pow 2).const_mul 3)).mul_const energy)
  convert (hn1.div (hd.pow 2) (pow_ne_zero 2 ha)).add
    (hn2.div (hd.pow 3) (pow_ne_zero 3 ha)) using 1
  dsimp [logKernelD3]
  field_simp
  ring

def kernelD1 (dim cross energy a : ℝ) := kernel dim cross energy a * logKernelD1 dim cross energy a

def kernelD2 (dim cross energy a : ℝ) := kernel dim cross energy a *
  (logKernelD1 dim cross energy a ^ 2 + logKernelD2 dim cross energy a)

def kernelD3 (dim cross energy a : ℝ) := kernel dim cross energy a *
  (logKernelD1 dim cross energy a ^ 3 +
    3 * logKernelD1 dim cross energy a * logKernelD2 dim cross energy a +
    logKernelD3 dim cross energy a)

theorem hasDerivAt_kernel (dim cross energy a : ℝ) (ha : 1 - a ^ 2 ≠ 0) :
    HasDerivAt (kernel dim cross energy) (kernelD1 dim cross energy a) a := by
  simpa only [kernelD1, mul_comm] using (hasDerivAt_logKernel dim cross energy a ha).exp

theorem hasDerivAt_kernelD1 (dim cross energy a : ℝ) (ha : 1 - a ^ 2 ≠ 0) :
    HasDerivAt (kernelD1 dim cross energy) (kernelD2 dim cross energy a) a := by
  convert (hasDerivAt_kernel dim cross energy a ha).mul
    (hasDerivAt_logKernelD1 dim cross energy a ha) using 1
  dsimp [kernelD1, kernelD2]
  ring

theorem hasDerivAt_kernelD2 (dim cross energy a : ℝ) (ha : 1 - a ^ 2 ≠ 0) :
    HasDerivAt (kernelD2 dim cross energy) (kernelD3 dim cross energy a) a := by
  convert (hasDerivAt_kernel dim cross energy a ha).mul
    (((hasDerivAt_logKernelD1 dim cross energy a ha).pow 2).add
      (hasDerivAt_logKernelD2 dim cross energy a ha)) using 1
  dsimp [kernelD1, kernelD2, kernelD3]
  ring

@[simp] theorem kernel_zero (dim cross energy : ℝ) : kernel dim cross energy 0 = 1 := by
  simp [kernel, logKernel]
@[simp] theorem kernelD1_zero (dim cross energy : ℝ) : kernelD1 dim cross energy 0 = cross := by
  simp [kernelD1, logKernelD1]
@[simp] theorem kernelD2_zero (dim cross energy : ℝ) :
    kernelD2 dim cross energy 0 = cross ^ 2 - energy + dim := by
  simp [kernelD2, logKernelD1, logKernelD2]
  ring

variable {I : Type*} [Fintype I]

def vectorKernel (a : ℝ) (y z : I → ℝ) : ℝ :=
  kernel (Fintype.card I) (∑ i, z i * y i) (∑ i, (y i ^ 2 + z i ^ 2)) a

/-- The kernel used for smoothing an actual finite-dimensional signal. -/
theorem vectorKernel_formula (a : ℝ) (y z : I → ℝ) :
    vectorKernel a y z = Real.exp (
      -((Fintype.card I : ℝ) / 2) * Real.log (1 - a ^ 2) +
        (2 * a * (∑ i, z i * y i) - a ^ 2 * (∑ i, (y i ^ 2 + z i ^ 2))) /
          (2 * (1 - a ^ 2))) := rfl

end GeneralizedBulk.Entropy.Mehler
