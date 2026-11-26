import GeneralizedBulk.Entropy.MehlerDerivativeEnvelope

/-! A uniform, polynomial-in-signal bound for the actual third Mehler derivative. -/
noncomputable section
namespace GeneralizedBulk.Entropy.Mehler

def derivativeEnvelope (dim Y Z : ℝ) : ℝ :=
  2048 * (1 + dim) * (1 + Y ^ 2) * (1 + Z ^ 2)

theorem logKernel_derivatives_common_bound (dim cross energy a Y Z : ℝ)
    (hdim : 0 ≤ dim) (henergy : 0 ≤ energy) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hden : 1 / 2 ≤ 1 - a ^ 2) (hcross : |cross| ≤ Y * Z)
    (henergyBound : energy ≤ Y ^ 2 + Z ^ 2) :
    |logKernelD1 dim cross energy a| ≤ derivativeEnvelope dim Y Z ∧
    |logKernelD2 dim cross energy a| ≤ derivativeEnvelope dim Y Z ∧
    |logKernelD3 dim cross energy a| ≤ derivativeEnvelope dim Y Z := by
  let L := (1 + Y ^ 2) * (1 + Z ^ 2)
  have hL : 1 ≤ L := by
    dsimp [L]
    nlinarith [sq_nonneg Y, sq_nonneg Z, mul_nonneg (sq_nonneg Y) (sq_nonneg Z)]
  have hc : |cross| ≤ L := by
    apply hcross.trans
    dsimp [L]
    nlinarith [sq_nonneg (Y - Z), sq_nonneg Y, sq_nonneg Z,
      mul_nonneg (sq_nonneg Y) (sq_nonneg Z)]
  have he : energy ≤ 2 * L := by
    dsimp [L]
    nlinarith [sq_nonneg Y, sq_nonneg Z, mul_nonneg (sq_nonneg Y) (sq_nonneg Z)]
  let U := (1 + dim) * L
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hmU : dim ≤ U := by
    dsimp [U]
    nlinarith [mul_nonneg hdim (show 0 ≤ L - 1 by linarith)]
  have hLU : L ≤ U := by dsimp [U]; nlinarith [mul_nonneg hdim (show 0 ≤ L by linarith)]
  have hcU : |cross| ≤ U := hc.trans hLU
  have heU : energy ≤ 2 * U := he.trans (by linarith)
  have haeU : a * energy ≤ 2 * U :=
    (mul_le_mul_of_nonneg_right ha1 henergy).trans (by simpa using heU)
  have h1 := logKernelD1_abs_bound dim cross energy a hdim henergy ha ha1 hden
  have h2 := logKernelD2_abs_bound dim cross energy a hdim henergy ha ha1 hden
  have h3 := logKernelD3_abs_bound dim cross energy a hdim henergy ha ha1 hden
  have hEq : derivativeEnvelope dim Y Z = 2048 * U := by
    dsimp [derivativeEnvelope, U, L]
    ring
  rw [hEq]
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem derivativeEnvelope_ge_one (dim Y Z : ℝ) (hdim : 0 ≤ dim) :
    1 ≤ derivativeEnvelope dim Y Z := by
  have h1 : (1 : ℝ) ≤ 1 + dim := by linarith
  have h2 : (1 : ℝ) ≤ 1 + Y ^ 2 := by nlinarith [sq_nonneg Y]
  have h3 : (1 : ℝ) ≤ 1 + Z ^ 2 := by nlinarith [sq_nonneg Z]
  unfold derivativeEnvelope
  calc
    (1 : ℝ) ≤ 2048 * 1 * 1 * 1 := by norm_num
    _ ≤ _ := by gcongr

/-- This coarser signal polynomial suffices for the polynomial graph rates:
the HY sup norm is only polylogarithmic in graph size. -/
theorem kernelD3_abs_uniform_bound (dim cross energy a Y Z : ℝ)
    (hdim : 0 ≤ dim) (henergy : 0 ≤ energy) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hden : 1 / 2 ≤ 1 - a ^ 2) (hZ : 0 ≤ Z)
    (hcross : |cross| ≤ Y * Z) (henergyBound : energy ≤ Y ^ 2 + Z ^ 2)
    (hsmall : a * Y ≤ 1 / 2) :
    |kernelD3 dim cross energy a| ≤
      5 * derivativeEnvelope dim Y Z ^ 3 * Real.exp (dim + Z) := by
  obtain ⟨h1, h2, h3⟩ := logKernel_derivatives_common_bound dim cross energy a Y Z
    hdim henergy ha ha1 hden hcross henergyBound
  let H := derivativeEnvelope dim Y Z
  have hH : 1 ≤ H := derivativeEnvelope_ge_one dim Y Z hdim
  have hb : |logKernelD1 dim cross energy a ^ 3 +
      3 * logKernelD1 dim cross energy a * logKernelD2 dim cross energy a +
      logKernelD3 dim cross energy a| ≤ 5 * H ^ 3 := by
    calc
      _ ≤ |logKernelD1 dim cross energy a| ^ 3 +
          3 * |logKernelD1 dim cross energy a| * |logKernelD2 dim cross energy a| +
          |logKernelD3 dim cross energy a| := by
        apply (abs_add _ _).trans
        have h := abs_add (logKernelD1 dim cross energy a ^ 3)
          (3 * logKernelD1 dim cross energy a * logKernelD2 dim cross energy a)
        rw [abs_pow, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)] at h
        linarith
      _ ≤ H ^ 3 + 3 * H * H + H := by gcongr
      _ ≤ _ := by nlinarith [sq_nonneg (H - 1), mul_nonneg (show 0 ≤ H - 1 by linarith) (sq_nonneg H)]
  unfold kernelD3
  rw [abs_mul, abs_of_pos (kernel_pos _ _ _ _)]
  calc
    _ ≤ Real.exp (dim + Z) * (5 * H ^ 3) := mul_le_mul
      (kernel_le_linear_envelope dim cross energy a Y Z hdim henergy ha hden hZ hcross hsmall)
      hb (abs_nonneg _) (Real.exp_pos _).le
    _ = _ := by ring

end GeneralizedBulk.Entropy.Mehler
