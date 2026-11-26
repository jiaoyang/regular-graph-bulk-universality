import GeneralizedBulk.Graph.Resolvent
import GeneralizedBulk.Matrix.CovarianceDeterminant

/-! Real covariance factors and exact global log-determinants for the
actual finite adjacency resolvent noise. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Covariance
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

def realEigenvectorMatrix : Matrix (Fin (N n)) (Fin (N n)) ℝ :=
  fun v a => D.eigenvector n ω a v

theorem realEigenvectorMatrix_transpose_mul :
    (D.realEigenvectorMatrix n ω).transpose * D.realEigenvectorMatrix n ω = 1 := by
  ext a b
  exact D.orthonormal n ω a b

theorem realEigenvectorMatrix_mul_transpose :
    D.realEigenvectorMatrix n ω * (D.realEigenvectorMatrix n ω).transpose = 1 :=
  Matrix.mul_eq_one_comm.mpr (D.realEigenvectorMatrix_transpose_mul n ω)

def resolventDenominator (E eta : ℝ) (a : Fin (N n)) : ℝ :=
  (D.eigenvalue n ω a - E) ^ 2 + eta ^ 2

def resolventCovarianceWeight (E eta sigma : ℝ) (a : Fin (N n)) : ℝ :=
  eta / sigma / D.resolventDenominator n ω E eta a

/-- The actual real resolvent covariance, with the normalizing density sigma. -/
def resolventCovariance (E eta sigma : ℝ) : Matrix (Fin (N n)) (Fin (N n)) ℝ :=
  spectralCovariance (D.realEigenvectorMatrix n ω) (D.resolventCovarianceWeight n ω E eta sigma)

def resolventCovarianceFactor (E eta sigma : ℝ) : Matrix (Fin (N n)) (Fin (N n)) ℝ :=
  spectralFactor (D.realEigenvectorMatrix n ω) (D.resolventCovarianceWeight n ω E eta sigma)

theorem resolventDenominator_pos (E eta : ℝ) (heta : 0 < eta) (a : Fin (N n)) :
    0 < D.resolventDenominator n ω E eta a := by
  unfold resolventDenominator
  nlinarith [sq_nonneg (D.eigenvalue n ω a - E)]

theorem resolventCovarianceWeight_pos (E eta sigma : ℝ) (heta : 0 < eta) (hsigma : 0 < sigma)
    (a : Fin (N n)) : 0 < D.resolventCovarianceWeight n ω E eta sigma a :=
  div_pos (div_pos heta hsigma) (D.resolventDenominator_pos n ω E eta heta a)

theorem resolventCovariance_factor (E eta sigma : ℝ) (heta : 0 < eta) (hsigma : 0 < sigma) :
    D.resolventCovarianceFactor n ω E eta sigma *
      (D.resolventCovarianceFactor n ω E eta sigma).transpose = D.resolventCovariance n ω E eta sigma :=
  spectralFactor_covariance _ _ (fun a => (D.resolventCovarianceWeight_pos n ω E eta sigma heta hsigma a).le)

theorem resolventCovariance_posDef (E eta sigma : ℝ) (heta : 0 < eta) (hsigma : 0 < sigma) :
    (D.resolventCovariance n ω E eta sigma).PosDef :=
  spectralCovariance_posDef _ (D.realEigenvectorMatrix_transpose_mul n ω) _
    (D.resolventCovarianceWeight_pos n ω E eta sigma heta hsigma)

/-- This real covariance is precisely sigma^{-1} times the entrywise
imaginary part of the genuine matrix inverse. -/
theorem resolventCovariance_entry (E eta sigma : ℝ) (heta : 0 < eta) (v w : Fin (N n)) :
    D.resolventCovariance n ω E eta sigma v w =
      (D.resolvent n ω (⟨E, eta⟩ : ℂ) v w).im / sigma := by
  rw [D.resolvent_entry_im n ω _ (by exact heta.ne')]
  unfold resolventCovariance spectralCovariance
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply,
    realEigenvectorMatrix, resolventCovarianceWeight, resolventDenominator]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.ofReal_re,
    Complex.sub_im, Complex.ofReal_im, zero_sub, neg_sq]
  ring

/-- Exact finite global log-determinant; no limiting law or spectral
approximation is used. -/
theorem resolventCovariance_logdet (E eta sigma : ℝ) (heta : 0 < eta) (hsigma : 0 < sigma) :
    Real.log (D.resolventCovariance n ω E eta sigma).det =
      (N n : ℝ) * Real.log (eta / sigma) -
        ∑ a, Real.log (D.resolventDenominator n ω E eta a) := by
  rw [resolventCovariance, spectralCovariance_logdet _ (D.realEigenvectorMatrix_transpose_mul n ω) _
    (D.resolventCovarianceWeight_pos n ω E eta sigma heta hsigma)]
  simp only [resolventCovarianceWeight, Real.log_div (div_pos heta hsigma).ne'
    (D.resolventDenominator_pos n ω E eta heta _).ne', Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The explicit real factor is nonsingular, so the actual Gaussian entropy
formula applies without a supplied square-root or invertibility assumption. -/
theorem resolventCovarianceFactor_det_ne_zero (E eta sigma : ℝ) (heta : 0 < eta) (hsigma : 0 < sigma) :
    (D.resolventCovarianceFactor n ω E eta sigma).det ≠ 0 := by
  have h := (D.resolventCovariance_posDef n ω E eta sigma heta hsigma).det_pos
  rw [← D.resolventCovariance_factor n ω E eta sigma heta hsigma,
    Matrix.det_mul, Matrix.det_transpose] at h
  intro hz
  simp only [hz, zero_mul, lt_self_iff_false] at h

end GeneralizedBulk.External.RegularSpectralData
