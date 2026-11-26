import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite microscopic resolvents and the bulk loop polynomial

These definitions give finite-particle resolvents and the bulk loop integrand.
The two-point kernel is a finite sum: it remains defined on the diagonal and
for parameters in opposite half-planes. Its agreement with the ordinary
divided difference requires distinct parameters, as it should.
-/

noncomputable section

open scoped BigOperators

namespace BourgadeHuang

inductive Beta where
  | one
  | two
  deriving DecidableEq, Repr

def Beta.value : Beta → ℂ
  | .one => 1
  | .two => 2

@[simp] theorem Beta.value_one : Beta.one.value = 1 := rfl
@[simp] theorem Beta.value_two : Beta.two.value = 2 := rfl

/-- The finite, centered microscopic Stieltjes transform in (4.9). -/
def microscopicResolvent {N : ℕ} (x : Fin N → ℝ) (center : ℝ) (w : ℂ) : ℂ :=
  (∑ i, ((x i : ℂ) - w)⁻¹) - (center : ℂ)

/-- The explicit derivative; `hasDerivAt_microscopicResolvent` verifies it. -/
def resolventDerivative {N : ℕ} (x : Fin N → ℝ) (w : ℂ) : ℂ :=
  ∑ i, (((x i : ℂ) - w)⁻¹) ^ 2

/-- The analytic extension of the divided difference of the resolvent. -/
def resolventKernel {N : ℕ} (x : Fin N → ℝ) (w v : ℂ) : ℂ :=
  ∑ i, ((x i : ℂ) - w)⁻¹ * ((x i : ℂ) - v)⁻¹

/-- The interaction term in (4.49), also well-defined when `w = v`. -/
def interaction {N : ℕ} (x : Fin N → ℝ) (w v : ℂ) : ℂ :=
  ∑ i, ((x i : ℂ) - w)⁻¹ * (((x i : ℂ) - v)⁻¹) ^ 2

theorem real_sub_ne_zero (a : ℝ) {w : ℂ} (hw : w.im ≠ 0) :
    (a : ℂ) - w ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im, zero_sub] at hi
  exact hw (neg_eq_zero.mp hi)

theorem hasDerivAt_reciprocal (a : ℝ) {w : ℂ} (hw : w.im ≠ 0) :
    HasDerivAt (fun z : ℂ => ((a : ℂ) - z)⁻¹) ((((a : ℂ) - w)⁻¹) ^ 2) w := by
  have h := ((hasDerivAt_const w (a : ℂ)).sub (hasDerivAt_id w)).inv
    (real_sub_ne_zero a hw)
  convert h using 1
  simp [div_eq_mul_inv, inv_pow]

theorem hasDerivAt_microscopicResolvent {N : ℕ} (x : Fin N → ℝ)
    (center : ℝ) {w : ℂ} (hw : w.im ≠ 0) :
    HasDerivAt (microscopicResolvent x center) (resolventDerivative x w) w := by
  have h : HasDerivAt (fun z : ℂ => ∑ i, ((x i : ℂ) - z)⁻¹)
      (∑ i, (((x i : ℂ) - w)⁻¹) ^ 2) w := by
    exact HasDerivAt.sum fun i _ => hasDerivAt_reciprocal (x i) hw
  exact h.sub_const (center : ℂ)

theorem deriv_microscopicResolvent {N : ℕ} (x : Fin N → ℝ)
    (center : ℝ) {w : ℂ} (hw : w.im ≠ 0) :
    deriv (microscopicResolvent x center) w = resolventDerivative x w :=
  (hasDerivAt_microscopicResolvent x center hw).deriv

theorem resolventKernel_eq_dividedDifference {N : ℕ} (x : Fin N → ℝ)
    (center : ℝ) {w v : ℂ} (hw : w.im ≠ 0) (hv : v.im ≠ 0) (hwv : w ≠ v) :
    resolventKernel x w v =
      (microscopicResolvent x center w - microscopicResolvent x center v) / (w - v) := by
  have ht (i : Fin N) :
      ((x i : ℂ) - w)⁻¹ * ((x i : ℂ) - v)⁻¹ =
        (((x i : ℂ) - w)⁻¹ - ((x i : ℂ) - v)⁻¹) / (w - v) := by
    field_simp [real_sub_ne_zero (x i) hw, real_sub_ne_zero (x i) hv,
      sub_ne_zero.mpr hwv]
  unfold resolventKernel microscopicResolvent
  simp_rw [ht]
  simp only [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_sub_distrib]
  ring

@[simp] theorem resolventKernel_diagonal {N : ℕ} (x : Fin N → ℝ) (w : ℂ) :
    resolventKernel x w w = resolventDerivative x w := by
  simp [resolventKernel, resolventDerivative, pow_two]

theorem hasDerivAt_resolventKernel {N : ℕ} (x : Fin N → ℝ) (w : ℂ)
    {v : ℂ} (hv : v.im ≠ 0) :
    HasDerivAt (resolventKernel x w) (interaction x w v) v := by
  exact HasDerivAt.sum fun i _ =>
    (hasDerivAt_reciprocal (x i) hv).const_mul (((x i : ℂ) - w)⁻¹)

theorem deriv_resolventKernel {N : ℕ} (x : Fin N → ℝ) (w : ℂ)
    {v : ℂ} (hv : v.im ≠ 0) :
    deriv (resolventKernel x w) v = interaction x w v :=
  (hasDerivAt_resolventKernel x w hv).deriv

theorem interaction_eq_quotient {N : ℕ} (x : Fin N → ℝ) (center : ℝ)
    {w v : ℂ} (hw : w.im ≠ 0) (hv : v.im ≠ 0) (hwv : w ≠ v) :
    interaction x w v =
      ((microscopicResolvent x center w - microscopicResolvent x center v) -
        (w - v) * resolventDerivative x v) / (w - v) ^ 2 := by
  have ht (i : Fin N) :
      ((x i : ℂ) - w)⁻¹ * (((x i : ℂ) - v)⁻¹) ^ 2 =
        ((((x i : ℂ) - w)⁻¹ - ((x i : ℂ) - v)⁻¹) -
          (w - v) * (((x i : ℂ) - v)⁻¹) ^ 2) / (w - v) ^ 2 := by
    field_simp [real_sub_ne_zero (x i) hw, real_sub_ne_zero (x i) hv,
      sub_ne_zero.mpr hwv]
    ring
  unfold interaction
  simp_rw [ht]
  simp only [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_sub_distrib, ← Finset.mul_sum,
    microscopicResolvent, resolventDerivative]
  ring

/-- The differentiated divided difference in (4.49), away from the diagonal.
`deriv_resolventKernel` supplies its analytic extension on the diagonal. -/
theorem deriv_dividedDifference {N : ℕ} (x : Fin N → ℝ) (center : ℝ)
    {w v : ℂ} (hw : w.im ≠ 0) (hv : v.im ≠ 0) (hwv : w ≠ v) :
    deriv (fun z =>
      (microscopicResolvent x center w - microscopicResolvent x center z) / (w - z)) v =
      interaction x w v := by
  have hs := hasDerivAt_microscopicResolvent x center hv
  have hd := ((hasDerivAt_const v (microscopicResolvent x center w)).sub hs).div
    ((hasDerivAt_const v w).sub (hasDerivAt_id v)) (sub_ne_zero.mpr hwv)
  have hd' := hd.deriv
  simp only [id_eq] at hd'
  rw [hd', interaction_eq_quotient x center hw hv hwv]
  ring

theorem interaction_diagonal {N : ℕ} (x : Fin N → ℝ) (w : ℂ) :
    interaction x w w = ∑ i, (((x i : ℂ) - w)⁻¹) ^ 3 := by
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem microscopicResolvent_reflection {N : ℕ} (x : Fin N → ℝ)
    (center : ℝ) (w : ℂ) :
    microscopicResolvent x center (star w) = star (microscopicResolvent x center w) := by
  simp [microscopicResolvent, map_sum]

/-- The real centering leaves the upper half-plane positivity unchanged. -/
theorem microscopicResolvent_im_nonneg {N : ℕ} (x : Fin N → ℝ)
    (center : ℝ) {w : ℂ} (hw : 0 ≤ w.im) :
    0 ≤ (microscopicResolvent x center w).im := by
  simp only [microscopicResolvent, Complex.sub_im, Complex.ofReal_im, sub_zero,
    Complex.im_sum]
  apply Finset.sum_nonneg
  intro i _
  rw [Complex.inv_im, Complex.sub_im, Complex.ofReal_im, zero_sub, neg_neg]
  exact div_nonneg hw (Complex.normSq_nonneg _)

theorem microscopicResolvent_im_eq {N : ℕ} (x : Fin N → ℝ)
    (center : ℝ) (w : ℂ) :
    (microscopicResolvent x center w).im =
      w.im * ∑ i, (Complex.normSq ((x i : ℂ) - w))⁻¹ := by
  simp [microscopicResolvent, Complex.im_sum, Complex.inv_im, div_eq_mul_inv,
    Finset.mul_sum]

/-- The first estimate in the proof of Lemma 4.9. -/
theorem norm_resolventDerivative_le_im {N : ℕ} (x : Fin N → ℝ)
    (center : ℝ) {w : ℂ} (hw : 0 < w.im) :
    ‖resolventDerivative x w‖ ≤ (microscopicResolvent x center w).im / w.im := by
  calc
    ‖resolventDerivative x w‖ ≤ ∑ i, ‖(((x i : ℂ) - w)⁻¹) ^ 2‖ :=
      norm_sum_le _ _
    _ = ∑ i, (Complex.normSq ((x i : ℂ) - w))⁻¹ := by
      simp only [norm_pow, Complex.sq_norm, Complex.normSq_inv]
    _ = (microscopicResolvent x center w).im / w.im := by
      rw [microscopicResolvent_im_eq]
      field_simp [ne_of_gt hw]

theorem norm_resolventDerivative_le_norm {N : ℕ} (x : Fin N → ℝ)
    (center : ℝ) {w : ℂ} (hw : 0 < w.im) :
    ‖resolventDerivative x w‖ ≤ ‖microscopicResolvent x center w‖ / w.im :=
  (norm_resolventDerivative_le_im x center hw).trans
    (div_le_div_of_nonneg_right (Complex.im_le_norm _) hw.le)

theorem norm_reciprocal_le_im (a : ℝ) {w : ℂ} (hw : w.im ≠ 0) :
    ‖((a : ℂ) - w)⁻¹‖ ≤ 1 / |w.im| := by
  have h : |w.im| ≤ ‖(a : ℂ) - w‖ := by
    simpa using Complex.abs_im_le_norm ((a : ℂ) - w)
  simpa only [norm_inv, one_div] using
    one_div_le_one_div_of_le (abs_pos.mpr hw) h

/-- The deterministic bound (4.51), used before taking exceptional-event moments. -/
theorem norm_microscopicResolvent_le {N : ℕ} (x : Fin N → ℝ)
    (center : ℝ) {w : ℂ} (hw : w.im ≠ 0) :
    ‖microscopicResolvent x center w‖ ≤ (N : ℝ) / |w.im| + |center| := by
  calc
    ‖microscopicResolvent x center w‖ ≤
        ‖∑ i, ((x i : ℂ) - w)⁻¹‖ + ‖(center : ℂ)‖ := norm_sub_le _ _
    _ ≤ (∑ i, ‖((x i : ℂ) - w)⁻¹‖) + |center| := by
      simpa using add_le_add_right (norm_sum_le Finset.univ
        (fun i : Fin N => ((x i : ℂ) - w)⁻¹)) ‖(center : ℂ)‖
    _ ≤ (∑ _i : Fin N, (1 / |w.im|)) + |center| := by
      exact add_le_add_right (Finset.sum_le_sum (fun i _ =>
        norm_reciprocal_le_im (x i) hw)) _
    _ = (N : ℝ) / |w.im| + |center| := by simp [div_eq_mul_inv]

/-- The physical, normalized Stieltjes transform. -/
def physicalStieltjes {N : ℕ} (eigenvalues : Fin N → ℝ) (z : ℂ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ i, ((eigenvalues i : ℂ) - z)⁻¹

def rescaledParticles {N : ℕ} (eigenvalues : Fin N → ℝ) (E σ : ℝ) : Fin N → ℝ :=
  fun i => (N : ℝ) * σ * (eigenvalues i - E)

def spectralParameter (N : ℕ) (E σ : ℝ) (w : ℂ) : ℂ :=
  (E : ℂ) + w / ((N : ℂ) * (σ : ℂ))

/-- The normalization in (4.9), without any regularity or asymptotic assumption. -/
theorem microscopic_normalization {N : ℕ} (eigenvalues : Fin N → ℝ)
    (E σ U : ℝ) (w : ℂ) (hN : N ≠ 0) (hσ : σ ≠ 0) :
    microscopicResolvent (rescaledParticles eigenvalues E σ) (U / σ) w =
      (physicalStieltjes eigenvalues (spectralParameter N E σ w) - (U : ℂ)) / (σ : ℂ) := by
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hσc : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hσ
  have hd (i : Fin N) :
      ((rescaledParticles eigenvalues E σ i : ℝ) : ℂ) - w =
        ((N : ℂ) * (σ : ℂ)) *
          ((eigenvalues i : ℂ) - spectralParameter N E σ w) := by
    simp only [rescaledParticles, spectralParameter, Complex.ofReal_mul,
      Complex.ofReal_sub, Complex.ofReal_natCast]
    field_simp [hNc, hσc]
    ring
  unfold microscopicResolvent
  simp_rw [hd, mul_inv_rev]
  simp only [← Finset.sum_mul, Complex.ofReal_div]
  unfold physicalStieltjes
  rw [div_eq_mul_inv, div_eq_mul_inv]
  ring

/-- The product over all auxiliary parameters except the selected one. -/
def excludedProduct {n : ℕ} (f : Fin n → ℂ) (a : Fin n) : ℂ :=
  ∏ b ∈ Finset.univ.erase a, f b

/-- The random-variable integrand of (4.50), with `n` auxiliary parameters.
Thus `n = 0` is the first loop equation (the paper labels it by `n = 1`).
There are no quotients `w - aux a`, so coincident parameters are included. -/
def loopIntegrand {N n : ℕ} (β : Beta) (x : Fin N → ℝ) (center : ℝ)
    (w : ℂ) (aux : Fin n → ℂ) : ℂ :=
  (((2 - β.value) / β.value) * resolventDerivative x w +
      microscopicResolvent x center w ^ 2 + 1) *
    (∏ a, microscopicResolvent x center (aux a)) +
    (2 / β.value) * ∑ a, interaction x w (aux a) *
      excludedProduct (fun b => microscopicResolvent x center (aux b)) a

theorem loopIntegrand_no_aux {N : ℕ} (β : Beta) (x : Fin N → ℝ) (center : ℝ)
    (w : ℂ) (aux : Fin 0 → ℂ) :
    loopIntegrand β x center w aux =
      ((2 - β.value) / β.value) * resolventDerivative x w +
        microscopicResolvent x center w ^ 2 + 1 := by
  simp [loopIntegrand]

theorem beta_two_derivative_coefficient : (2 - Beta.two.value) / Beta.two.value = 0 := by
  norm_num [Beta.value]

theorem beta_one_derivative_coefficient : (2 - Beta.one.value) / Beta.one.value = 1 := by
  norm_num [Beta.value]

end BourgadeHuang
