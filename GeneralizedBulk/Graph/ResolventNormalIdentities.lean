import GeneralizedBulk.Graph.ResolventCovariance
import GeneralizedBulk.Matrix.SpectralAlgebra

/-! Exact normal resolvent covariance identities, before any local-law error. -/
noncomputable section
open scoped BigOperators Matrix
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Covariance
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

def centeredAdjacency (E : ℝ) : Matrix (Fin (N n)) (Fin (N n)) ℝ :=
  D.adjacency n ω - E • 1

def realResolventPart (E eta : ℝ) : Matrix (Fin (N n)) (Fin (N n)) ℝ :=
  spectralCovariance (D.realEigenvectorMatrix n ω)
    (fun a => (D.eigenvalue n ω a - E) / D.resolventDenominator n ω E eta a)

theorem real_adjacency_spectral :
    D.adjacency n ω = spectralCovariance (D.realEigenvectorMatrix n ω) (D.eigenvalue n ω) := by
  have hmul : D.adjacency n ω * D.realEigenvectorMatrix n ω =
      D.realEigenvectorMatrix n ω * Matrix.diagonal (D.eigenvalue n ω) := by
    ext v a
    simp only [Matrix.mul_diagonal]
    simp only [Matrix.mul_apply, realEigenvectorMatrix]
    exact (D.eigen_equation n ω a v).trans (mul_comm _ _)
  unfold spectralCovariance
  rw [← hmul, Matrix.mul_assoc, D.realEigenvectorMatrix_mul_transpose n ω, Matrix.mul_one]

theorem centeredAdjacency_spectral (E : ℝ) :
    D.centeredAdjacency n ω E = spectralCovariance (D.realEigenvectorMatrix n ω)
      (fun a => D.eigenvalue n ω a - E) := by
  rw [centeredAdjacency, D.real_adjacency_spectral n ω,
    ← spectralCovariance_const _ (D.realEigenvectorMatrix_transpose_mul n ω) E,
    ← spectralCovariance_sub]
  rfl

/-- T Im(T-i eta)^{-1}=eta Re(T-i eta)^{-1}, with the actual
normalization sigma included. -/
theorem centeredAdjacency_mul_covariance (E eta sigma : ℝ) :
    D.centeredAdjacency n ω E * D.resolventCovariance n ω E eta sigma =
      (eta / sigma) • D.realResolventPart n ω E eta := by
  rw [D.centeredAdjacency_spectral n ω, resolventCovariance,
    spectralCovariance_mul _ (D.realEigenvectorMatrix_transpose_mul n ω), realResolventPart,
    ← spectralCovariance_smul]
  apply congrArg (spectralCovariance _)
  funext a
  dsimp [resolventCovarianceWeight]
  ring

/-- The exact quadratic normal covariance identity. This isolates the small
normal variance without an inverse or Schur-complement approximation. -/
theorem centeredAdjacency_covariance_centeredAdjacency (E eta sigma : ℝ) (heta : 0 < eta) :
    D.centeredAdjacency n ω E * D.resolventCovariance n ω E eta sigma * D.centeredAdjacency n ω E =
      (eta / sigma) • 1 - eta ^ 2 • D.resolventCovariance n ω E eta sigma := by
  rw [D.centeredAdjacency_spectral n ω, resolventCovariance,
    spectralCovariance_mul _ (D.realEigenvectorMatrix_transpose_mul n ω),
    spectralCovariance_mul _ (D.realEigenvectorMatrix_transpose_mul n ω),
    ← spectralCovariance_const _ (D.realEigenvectorMatrix_transpose_mul n ω) (eta / sigma),
    ← spectralCovariance_smul, ← spectralCovariance_sub]
  apply congrArg (spectralCovariance _)
  funext a
  dsimp [resolventCovarianceWeight]
  have hd := (D.resolventDenominator_pos n ω E eta heta a).ne'
  have heq : (D.eigenvalue n ω a - E) ^ 2 + eta ^ 2 = D.resolventDenominator n ω E eta a := rfl
  apply (eq_sub_iff_add_eq).mpr
  calc
    _ = ((D.eigenvalue n ω a - E) ^ 2 + eta ^ 2) * (eta / sigma / D.resolventDenominator n ω E eta a) := by ring
    _ = eta / sigma := by
      rw [heq]
      calc
        _ = (eta / sigma) * (D.resolventDenominator n ω E eta a * (D.resolventDenominator n ω E eta a)⁻¹) := by ring
        _ = _ := by rw [mul_inv_cancel₀ hd, mul_one]

/-- The normal identities are for the real part of the genuine finite inverse. -/
theorem realResolventPart_entry (E eta : ℝ) (heta : 0 < eta) (v w : Fin (N n)) :
    D.realResolventPart n ω E eta v w = (D.resolvent n ω (⟨E, eta⟩ : ℂ) v w).re := by
  rw [D.resolvent_entry n ω _ (by exact heta.ne')]
  unfold realResolventPart spectralCovariance
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, realEigenvectorMatrix,
    Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero, Complex.inv_re, Complex.sub_re, Complex.sub_im,
    Complex.normSq_apply, resolventDenominator, zero_sub, neg_sq]
  apply Finset.sum_congr rfl
  intro a ha
  ring

end GeneralizedBulk.External.RegularSpectralData
