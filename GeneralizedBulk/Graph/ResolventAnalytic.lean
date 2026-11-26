import GeneralizedBulk.Graph.Resolvent

/-! The finite graph resolvent is actually analytic and has derivative `R²`. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace GeneralizedBulk.External.RegularSpectralData
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

theorem resolvent_square_eq_spectral (z : ℂ) (hz : z.im ≠ 0) :
    D.resolvent n ω z * D.resolvent n ω z = D.eigenvectorMatrix n ω *
      Matrix.diagonal (fun a => ((D.eigenvalue n ω a : ℂ) - z)⁻¹ ^ 2) *
        (D.eigenvectorMatrix n ω).transpose := by
  classical
  let U := D.eigenvectorMatrix n ω
  let B := Matrix.diagonal (fun a => ((D.eigenvalue n ω a : ℂ) - z)⁻¹)
  have hR : D.resolvent n ω z = U * B * U.transpose := D.resolvent_eq_spectral n ω z hz
  rw [hR]
  calc
    _ = U * (B * (U.transpose * U) * B) * U.transpose := by simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [show U.transpose * U = 1 from D.eigenvectorMatrix_transpose_mul n ω, mul_one]
      simp only [B, U, Matrix.diagonal_mul_diagonal, pow_two]

theorem resolvent_square_entry (z : ℂ) (hz : z.im ≠ 0) (v w : Fin (N n)) :
    (D.resolvent n ω z * D.resolvent n ω z) v w =
      ∑ a, ((D.eigenvalue n ω a : ℂ) - z)⁻¹ ^ 2 *
        (D.eigenvector n ω a v : ℂ) * (D.eigenvector n ω a w : ℂ) := by
  rw [D.resolvent_square_eq_spectral n ω z hz, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, eigenvectorMatrix, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- Entrywise complex differentiation of the genuine finite matrix inverse. -/
theorem hasDerivAt_resolvent_entry (z : ℂ) (hz : z.im ≠ 0) (v w : Fin (N n)) :
    HasDerivAt (fun u => D.resolvent n ω u v w)
      ((D.resolvent n ω z * D.resolvent n ω z) v w) z := by
  classical
  have hc (a : Fin (N n)) : HasDerivAt (fun u : ℂ => ((D.eigenvalue n ω a : ℂ) - u)⁻¹)
      (((D.eigenvalue n ω a : ℂ) - z)⁻¹ ^ 2) z := by
    have h := ((hasDerivAt_const z (D.eigenvalue n ω a : ℂ)).sub (hasDerivAt_id z)).inv
      (D.real_eigenvalue_sub_ne_zero n ω z hz a)
    convert h using 1 <;> simp only [id_eq, zero_sub, neg_neg, div_eq_mul_inv, inv_pow, one_mul]
  have hs := HasDerivAt.sum (u := Finset.univ) (fun a _ =>
    ((hc a).mul_const (D.eigenvector n ω a v : ℂ)).mul_const (D.eigenvector n ω a w : ℂ))
  rw [← D.resolvent_square_entry n ω z hz v w] at hs
  apply hs.congr_of_eventuallyEq
  filter_upwards [(isOpen_ne_fun Complex.continuous_im continuous_const).mem_nhds hz] with u hu
  exact D.resolvent_entry n ω u hu v w

/-- The entire finite resolvent matrix has the stated true derivative in its
finite product topology. -/
theorem hasDerivAt_resolvent (z : ℂ) (hz : z.im ≠ 0) :
    HasDerivAt (D.resolvent n ω) (D.resolvent n ω z * D.resolvent n ω z) z := by
  apply hasDerivAt_pi.mpr
  intro v
  apply hasDerivAt_pi.mpr
  intro w
  exact D.hasDerivAt_resolvent_entry n ω z hz v w

end GeneralizedBulk.External.RegularSpectralData
