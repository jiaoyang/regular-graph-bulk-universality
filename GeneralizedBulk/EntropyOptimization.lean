import Mathlib

/-!
# The deterministic one-scale entropy estimate

This module formalizes the real-variable optimization after the Gaussian
analysis has established its inequalities. The smoothing parameter is `x^2`,
so the quartic-chaos contribution and Taylor remainder have integer powers
`x^8` and `x^9`. It does not assume Gaussian maximality, Mehler expansion,
or fourth-chaos coercivity as external BS/HY results.
-/

noncomputable section
namespace GeneralizedBulk.Entropy

/-- The entropy deficit and fourth-chaos lower estimate bound the quartic norm
at any positive smoothing scale. The coefficient `A` will be `C * B^3`. -/
theorem one_scale_bound (epsilon delta kappa A x q : ℝ)
    (hkappa : 0 < kappa) (hx : 0 < x)
    (hsmall : delta ≤ epsilon)
    (hlower : kappa / 2 * x ^ 8 * q ^ 2 - A * x ^ 9 ≤ delta) :
    q ^ 2 ≤ (2 / kappa) * (epsilon / x ^ 8 + A * x) := by
  have hx8 : 0 < x ^ 8 := pow_pos hx _
  have hden : 0 < kappa * x ^ 8 := mul_pos hkappa hx8
  have h : kappa * x ^ 8 * q ^ 2 ≤ 2 * epsilon + 2 * A * x ^ 9 := by
    linarith
  calc
    q ^ 2 = (kappa * x ^ 8 * q ^ 2) / (kappa * x ^ 8) := by
      field_simp
    _ ≤ (2 * epsilon + 2 * A * x ^ 9) / (kappa * x ^ 8) :=
      div_le_div_of_nonneg_right h hden.le
    _ = (2 / kappa) * (epsilon / x ^ 8 + A * x) := by
      field_simp
      ring

/-- At the balancing scale the two error terms agree. -/
theorem balanced_scale_bound (epsilon delta kappa A x q : ℝ)
    (hkappa : 0 < kappa) (hx : 0 < x)
    (hsmall : delta ≤ epsilon)
    (hlower : kappa / 2 * x ^ 8 * q ^ 2 - A * x ^ 9 ≤ delta)
    (hbalance : epsilon = A * x ^ 9) :
    q ^ 2 ≤ 4 * A * x / kappa := by
  have heq : epsilon / x ^ 8 = A * x := by
    rw [hbalance]
    field_simp
    ring
  have h := one_scale_bound epsilon delta kappa A x q hkappa hx hsmall hlower
  rw [heq] at h
  convert h using 1
  ring

/-- The explicit positive ninth-root scale balances the error terms.
The expansion-domain restriction is deliberately left as a hypothesis for
the analytic application, rather than asserted by this algebraic lemma. -/
theorem ninth_root_balance (epsilon A : ℝ) (hepsilon : 0 < epsilon) (hA : 0 < A) :
    let x := (epsilon / A) ^ ((9 : ℝ)⁻¹)
    0 < x ∧ epsilon = A * x ^ 9 := by
  dsimp
  have hratio : 0 < epsilon / A := div_pos hepsilon hA
  refine ⟨Real.rpow_pos_of_pos hratio _, ?_⟩
  have hpow := Real.rpow_inv_natCast_pow hratio.le (show (9 : ℕ) ≠ 0 by decide)
  have h := (div_eq_iff (ne_of_gt hA)).mp hpow.symm
  simpa only [mul_comm] using h

/-- The optimized square-norm estimate. Substitution `A = C * B^3` is the
source of the manuscript's quartic exponent `epsilon^(1/18)` after taking
square roots. Gaussian analytic inequalities must hold at this chosen scale. -/
theorem optimized_bound (epsilon delta kappa A q : ℝ)
    (hkappa : 0 < kappa) (hepsilon : 0 < epsilon) (hA : 0 < A)
    (hsmall : delta ≤ epsilon)
    (hlower :
      kappa / 2 * ((epsilon / A) ^ ((9 : ℝ)⁻¹)) ^ 8 * q ^ 2 -
        A * ((epsilon / A) ^ ((9 : ℝ)⁻¹)) ^ 9 ≤ delta) :
    q ^ 2 ≤ 4 * A * (epsilon / A) ^ ((9 : ℝ)⁻¹) / kappa := by
  obtain ⟨hx, hb⟩ := ninth_root_balance epsilon A hepsilon hA
  exact balanced_scale_bound epsilon delta kappa A _ q hkappa hx hsmall hlower hb

/-- Separate the powers of the Taylor coefficient and the entropy deficit. -/
theorem balancing_power_identity (epsilon A : ℝ) (hepsilon : 0 < epsilon) (hA : 0 < A) :
    A * (epsilon / A) ^ ((9 : ℝ)⁻¹) =
      A ^ (8 / 9 : ℝ) * epsilon ^ (1 / 9 : ℝ) := by
  rw [show (9 : ℝ)⁻¹ = (1 / 9 : ℝ) by norm_num,
    Real.div_rpow hepsilon.le hA.le]
  have hsplit : A ^ (8 / 9 : ℝ) * A ^ (1 / 9 : ℝ) = A := by
    rw [← Real.rpow_add hA]
    norm_num
  calc
    A * (epsilon ^ (1 / 9 : ℝ) / A ^ (1 / 9 : ℝ)) =
        (A / A ^ (1 / 9 : ℝ)) * epsilon ^ (1 / 9 : ℝ) := by ring
    _ = _ := by
      congr 1
      exact (div_eq_iff (ne_of_gt (Real.rpow_pos_of_pos hA _))).2 hsplit.symm

/-- The exact one-eighteenth exponent for the nonnegative quartic norm. -/
theorem optimized_quartic_norm (epsilon delta kappa A q : ℝ)
    (hkappa : 0 < kappa) (hepsilon : 0 < epsilon) (hA : 0 < A) (hq : 0 ≤ q)
    (hsmall : delta ≤ epsilon)
    (hlower :
      kappa / 2 * ((epsilon / A) ^ ((9 : ℝ)⁻¹)) ^ 8 * q ^ 2 -
        A * ((epsilon / A) ^ ((9 : ℝ)⁻¹)) ^ 9 ≤ delta) :
    q ≤ (2 / Real.sqrt kappa) * A ^ (4 / 9 : ℝ) * epsilon ^ (1 / 18 : ℝ) := by
  have hb := optimized_bound epsilon delta kappa A q hkappa hepsilon hA hsmall hlower
  have hfactor : 4 * A * (epsilon / A) ^ ((9 : ℝ)⁻¹) / kappa =
      (4 / kappa) * A ^ (8 / 9 : ℝ) * epsilon ^ (1 / 9 : ℝ) := by
    calc
      _ = (4 / kappa) * (A * (epsilon / A) ^ ((9 : ℝ)⁻¹)) := by ring
      _ = _ := by rw [balancing_power_identity epsilon A hepsilon hA]; ring
  rw [hfactor] at hb
  have hA2 : (A ^ (4 / 9 : ℝ)) ^ 2 = A ^ (8 / 9 : ℝ) := by
    rw [← Real.rpow_mul_natCast hA.le]
    norm_num
  have he2 : (epsilon ^ (1 / 18 : ℝ)) ^ 2 = epsilon ^ (1 / 9 : ℝ) := by
    rw [← Real.rpow_mul_natCast hepsilon.le]
    norm_num
  have hsq : ((2 / Real.sqrt kappa) * A ^ (4 / 9 : ℝ) *
      epsilon ^ (1 / 18 : ℝ)) ^ 2 =
        (4 / kappa) * A ^ (8 / 9 : ℝ) * epsilon ^ (1 / 9 : ℝ) := by
    rw [mul_pow, mul_pow, div_pow, hA2, he2, Real.sq_sqrt hkappa.le]
    ring
  have hnonneg : 0 ≤ (2 / Real.sqrt kappa) * A ^ (4 / 9 : ℝ) *
      epsilon ^ (1 / 18 : ℝ) := by positivity
  exact (sq_le_sq₀ hq hnonneg).mp (by rw [hsq]; exact hb)

/-- Substitution of the bounded-law Taylor coefficient gives the source
exponent `B^(4/3) * epsilon^(1/18)` without asymptotic notation. -/
theorem bounded_law_power_identity (C B : ℝ) (hC : 0 < C) (hB : 0 < B) :
    (C * B ^ 3) ^ (4 / 9 : ℝ) = C ^ (4 / 9 : ℝ) * B ^ (4 / 3 : ℝ) := by
  rw [Real.mul_rpow hC.le (pow_nonneg hB.le _),
    ← Real.rpow_natCast_mul hB.le]
  norm_num

end GeneralizedBulk.Entropy
