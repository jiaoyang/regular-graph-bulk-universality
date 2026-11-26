import GeneralizedBulk.Entropy.SignalWickMoments

/-! Polarization converts the actual diagonal fourth-chaos estimate to raw
mixed four-linear-form Gaussian Wick discrepancies. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Mehler
open GeneralizedBulk.Entropy.Hermite

abbrev SignQuad := Bool × Bool × Bool × Bool

def boolSign (b : Bool) : ℝ := if b then 1 else -1

def quadSign (e : SignQuad) : ℝ := boolSign e.1 * boolSign e.2.1 * boolSign e.2.2.1 * boolSign e.2.2.2

def signedScalar (e : SignQuad) (a b c d : ℝ) : ℝ :=
  boolSign e.1 * a + boolSign e.2.1 * b + boolSign e.2.2.1 * c + boolSign e.2.2.2 * d

set_option maxHeartbeats 2000000 in
theorem fourth_polarization_real (a b c d : ℝ) :
    (∑ e : SignQuad, quadSign e * signedScalar e a b c d ^ 4) = 384 * a * b * c * d := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, quadSign, signedScalar, boolSign, Bool.false_eq_true, ↓reduceIte]
  ring

theorem abs_quadSign (e : SignQuad) : |quadSign e| = 1 := by
  rcases e with ⟨a, b, c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> norm_num [quadSign, boolSign]

variable {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S]

def signedRow (e : SignQuad) (u v w z : I → ℝ) : I → ℝ :=
  boolSign e.1 • u + boolSign e.2.1 • v + boolSign e.2.2.1 • w + boolSign e.2.2.2 • z

def rowVariance (u : I → ℝ) : ℝ := ∑ i, u i ^ 2

def gaussianFourthWick (u v w z : I → ℝ) : ℝ :=
  (u ⬝ᵥ v) * (w ⬝ᵥ z) + (u ⬝ᵥ w) * (v ⬝ᵥ z) + (u ⬝ᵥ z) * (v ⬝ᵥ w)

theorem rowVariance_eq_dot (u : I → ℝ) : rowVariance u = u ⬝ᵥ u := by simp only [rowVariance, dotProduct, pow_two]

theorem linearForm_signedRow (e : SignQuad) (u v w z x : I → ℝ) :
    linearForm (signedRow e u v w z) x =
      signedScalar e (linearForm u x) (linearForm v x) (linearForm w x) (linearForm z x) := by
  simp only [linearForm, signedRow, signedScalar, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]

set_option maxHeartbeats 2000000 in
/-- The Gaussian Wick contraction is polarized by the same exact finite
identity; this is deterministic inner-product algebra. -/
theorem fourth_polarization_wick (u v w z : I → ℝ) :
    (∑ e : SignQuad, quadSign e * (3 * rowVariance (signedRow e u v w z) ^ 2)) =
      384 * gaussianFourthWick u v w z := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, quadSign, signedRow, boolSign, Bool.false_eq_true, ↓reduceIte,
    rowVariance_eq_dot, dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct,
    smul_eq_mul, gaussianFourthWick]
  simp only [dotProduct_comm]
  ring

def diagonalFourthDiscrepancy (D : NormalizedFiniteSignal I S) (u : I → ℝ) : ℝ :=
  (∑ s, D.weight s * linearForm u (D.signal s) ^ 4) - 3 * rowVariance u ^ 2

def mixedFourthDiscrepancy (D : NormalizedFiniteSignal I S) (u v w z : I → ℝ) : ℝ :=
  (∑ s, D.weight s * linearForm u (D.signal s) * linearForm v (D.signal s) *
    linearForm w (D.signal s) * linearForm z (D.signal s)) - gaussianFourthWick u v w z

/-- The raw fourth moment minus the actual Gaussian Wick value is the
polarization of the proven diagonal discrepancies. -/
theorem fourth_discrepancy_polarization (D : NormalizedFiniteSignal I S) (u v w z : I → ℝ) :
    (∑ e : SignQuad, quadSign e * diagonalFourthDiscrepancy D (signedRow e u v w z)) =
      384 * mixedFourthDiscrepancy D u v w z := by
  have hraw : (∑ e : SignQuad, quadSign e * ∑ s, D.weight s * linearForm (signedRow e u v w z) (D.signal s) ^ 4) =
      384 * ∑ s, D.weight s * linearForm u (D.signal s) * linearForm v (D.signal s) *
        linearForm w (D.signal s) * linearForm z (D.signal s) := by
    calc
      _ = ∑ s, D.weight s * ∑ e : SignQuad, quadSign e * linearForm (signedRow e u v w z) (D.signal s) ^ 4 := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro s hs
        apply Finset.sum_congr rfl
        intro e he
        ring
      _ = _ := by
        simp_rw [linearForm_signedRow, fourth_polarization_real]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s hs
        ring
  simp only [diagonalFourthDiscrepancy, mul_sub, Finset.sum_sub_distrib]
  rw [hraw, fourth_polarization_wick]
  unfold mixedFourthDiscrepancy
  ring

/-- An explicit computable four-row coefficient controls every actual mixed
fourth Wick discrepancy by the proved fourth-chaos norm. -/
theorem mixed_fourth_moment_bound (D : NormalizedFiniteSignal I S) (u v w z : I → ℝ) :
    |mixedFourthDiscrepancy D u v w z| ≤
      ‖signalChaos D.weight D.signal 4‖ * Real.sqrt 24 *
        (∑ e : SignQuad, rowVariance (signedRow e u v w z) ^ 2) / 384 := by
  have hsum : |∑ e : SignQuad, quadSign e * diagonalFourthDiscrepancy D (signedRow e u v w z)| ≤
      ‖signalChaos D.weight D.signal 4‖ * Real.sqrt 24 *
        ∑ e : SignQuad, rowVariance (signedRow e u v w z) ^ 2 := by
    calc
      _ ≤ ∑ e : SignQuad, |quadSign e * diagonalFourthDiscrepancy D (signedRow e u v w z)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ e : SignQuad, |diagonalFourthDiscrepancy D (signedRow e u v w z)| := by
        simp only [abs_mul, abs_quadSign, one_mul]
      _ ≤ ∑ e : SignQuad, ‖signalChaos D.weight D.signal 4‖ * Real.sqrt 24 *
          rowVariance (signedRow e u v w z) ^ 2 := by
        exact Finset.sum_le_sum (fun e _ => linear_fourth_moment_bound D (signedRow e u v w z))
      _ = _ := (Finset.mul_sum _ _ _).symm
  rw [fourth_discrepancy_polarization, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 384)] at hsum
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 384)).mpr
  nlinarith


@[simp] theorem boolSign_sq (b : Bool) : boolSign b ^ 2 = 1 := by cases b <;> norm_num [boolSign]

theorem four_sum_sq_le (a b c d : ℝ) :
    (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d),
    sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]

theorem signedRow_variance_le (e : SignQuad) (u v w z : I → ℝ) :
    rowVariance (signedRow e u v w z) ≤
      4 * (rowVariance u + rowVariance v + rowVariance w + rowVariance z) := by
  have hi (i : I) : (signedRow e u v w z i) ^ 2 ≤ 4 * (u i ^ 2 + v i ^ 2 + w i ^ 2 + z i ^ 2) := by
    have hh := four_sum_sq_le (boolSign e.1 * u i) (boolSign e.2.1 * v i)
      (boolSign e.2.2.1 * w i) (boolSign e.2.2.2 * z i)
    simpa only [signedRow, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_pow, boolSign_sq, one_mul] using hh
  calc
    _ ≤ ∑ i, 4 * (u i ^ 2 + v i ^ 2 + w i ^ 2 + z i ^ 2) := Finset.sum_le_sum (fun i _ => hi i)
    _ = _ := by
      rw [← Finset.mul_sum]
      simp only [rowVariance, Finset.sum_add_distrib]

/-- Physical Gaussian root/leaf rows have variance one. For all such rows a
single universal constant controls every actual mixed fourth moment. -/
theorem mixed_fourth_moment_bound_unit_rows (D : NormalizedFiniteSignal I S) (u v w z : I → ℝ)
    (hu : rowVariance u ≤ 1) (hv : rowVariance v ≤ 1) (hw : rowVariance w ≤ 1) (hz : rowVariance z ≤ 1) :
    |mixedFourthDiscrepancy D u v w z| ≤ 64 * ‖signalChaos D.weight D.signal 4‖ := by
  have hq (e : SignQuad) : rowVariance (signedRow e u v w z) ^ 2 ≤ 256 := by
    have hn : 0 ≤ rowVariance (signedRow e u v w z) := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hb := signedRow_variance_le e u v w z
    nlinarith
  have hsum : (∑ e : SignQuad, rowVariance (signedRow e u v w z) ^ 2) ≤ 4096 := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun e _ => hq e)
    norm_num only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_bool,
      nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat] at hh
    exact hh
  have hroot : Real.sqrt 24 ≤ 6 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 24), Real.sqrt_nonneg (24 : ℝ)]
  have hnorm := norm_nonneg (signalChaos D.weight D.signal 4)
  have hsqrt := mul_le_mul_of_nonneg_left hroot hnorm
  have hprod := mul_le_mul_of_nonneg_left hsum
    (mul_nonneg hnorm (Real.sqrt_nonneg (24 : ℝ)))
  have hh := mixed_fourth_moment_bound D u v w z
  nlinarith

end GeneralizedBulk.Entropy.Mehler
