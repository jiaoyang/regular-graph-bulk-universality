import GeneralizedBulk.Graph.EmpiricalQuartic

/-! Raw physical eigenvector-star fourth moments are controlled by the actual
empirical Gaussian fourth-chaos vector. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Entropy.Channel GeneralizedBulk.Entropy.Mehler GeneralizedBulk.Entropy.Hermite
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

def empiricalPhysicalRowCoordinates {k : ℕ} (hd : 2 ≤ d) (selection : Fin k → Fin (N n))
    (j : Fin k × Fin (d + 1)) : ScalarCoordinate d k → ℝ :=
  scalarCoordinates d k (coloredPhysicalRow d k hd (fun a => D.eigenvalue n ω (selection a)) j)

def empiricalGaussianCovariance {k : ℕ} (selection : Fin k → Fin (N n))
    (j l : Fin k × Fin (d + 1)) : ℝ :=
  (if j.1 = l.1 then 1 else 0) * starWaveCovariance d (D.eigenvalue n ω (selection j.1)) j.2 l.2

theorem empiricalPhysicalRowCoordinates_covariance {k : ℕ} (hd : 3 ≤ d) (selection : Fin k → Fin (N n))
    (hbulk : ∀ a, (D.eigenvalue n ω (selection a) / d) ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (j l : Fin k × Fin (d + 1)) :
    empiricalPhysicalRowCoordinates D n ω (by omega) selection j ⬝ᵥ
      empiricalPhysicalRowCoordinates D n ω (by omega) selection l =
      D.empiricalGaussianCovariance n ω selection j l := by
  exact (scalarCoordinates_dot d k _ _).trans
    (coloredPhysicalRow_gram d k (by omega) _ (D.empiricalEigenvalue_abs_lt_d n ω hd selection hbulk) j l)

theorem starWaveCovariance_self (d : ℕ) (energy : ℝ) (j : Fin (d + 1)) :
    starWaveCovariance d energy j j = 1 := by
  induction j using Fin.cases with
  | zero => simp [starWaveCovariance]
  | succ i => simp [starWaveCovariance]

theorem empiricalPhysicalRowCoordinates_variance {k : ℕ} (hd : 3 ≤ d) (selection : Fin k → Fin (N n))
    (hbulk : ∀ a, (D.eigenvalue n ω (selection a) / d) ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (j : Fin k × Fin (d + 1)) :
    rowVariance (D.empiricalPhysicalRowCoordinates n ω (by omega) selection j) = 1 := by
  rw [rowVariance_eq_dot, D.empiricalPhysicalRowCoordinates_covariance n ω hd selection hbulk j j]
  simp only [empiricalGaussianCovariance, ↓reduceIte, one_mul, starWaveCovariance_self]

theorem empiricalBulkSignal_weight {k : ℕ} (hd : 3 ≤ d) (selection : Fin k → Fin (N n))
    (hinj : Function.Injective selection)
    (hbulk : ∀ a, (D.eigenvalue n ω (selection a) / d) ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2) :
    (D.empiricalBulkSignal n ω hd selection hinj hbulk).weight = D.empiricalStarWeight n := rfl

theorem empiricalBulkSignal_physical_row {k : ℕ} (hd : 3 ≤ d) (selection : Fin k → Fin (N n))
    (hinj : Function.Injective selection)
    (hbulk : ∀ a, (D.eigenvalue n ω (selection a) / d) ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (s : EmpiricalStarSample d (N n)) (j : Fin k × Fin (d + 1)) :
    linearForm (D.empiricalPhysicalRowCoordinates n ω (by omega) selection j)
      ((D.empiricalBulkSignal n ω hd selection hinj hbulk).signal s) =
      D.starSample n ω (fun a => D.eigenvector n ω (selection a)) s j := by
  change linearForm (scalarCoordinates d k (coloredPhysicalRow d k (by omega)
    (fun a => D.eigenvalue n ω (selection a)) j))
    ((D.empiricalNormalizedSignal n ω (by omega) selection hinj
      (D.empiricalEigenvalue_abs_lt_d n ω hd selection hbulk)).signal s) = _
  rw [D.empiricalNormalizedSignal_values]
  exact (scalarCoordinates_dot d k _ _).trans
    (D.empiricalWhiteStar_row n ω (by omega) selection (D.empiricalEigenvalue_abs_lt_d n ω hd selection hbulk) s j)

/-- The source's actual normalized eigenvector fourth moments, simultaneously
in every selected color and root/leaf slot, have the Gaussian Wick discrepancy
bounded by the actual empirical fourth-chaos norm. -/
theorem empirical_mixed_fourth_wick_bound {k : ℕ} (hd : 3 ≤ d) (selection : Fin k → Fin (N n))
    (hinj : Function.Injective selection)
    (hbulk : ∀ a, (D.eigenvalue n ω (selection a) / d) ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (j1 j2 j3 j4 : Fin k × Fin (d + 1)) :
    |(∑ s : EmpiricalStarSample d (N n), D.empiricalStarWeight n s *
      D.starSample n ω (fun a => D.eigenvector n ω (selection a)) s j1 *
      D.starSample n ω (fun a => D.eigenvector n ω (selection a)) s j2 *
      D.starSample n ω (fun a => D.eigenvector n ω (selection a)) s j3 *
      D.starSample n ω (fun a => D.eigenvector n ω (selection a)) s j4) -
      (D.empiricalGaussianCovariance n ω selection j1 j2 * D.empiricalGaussianCovariance n ω selection j3 j4 +
       D.empiricalGaussianCovariance n ω selection j1 j3 * D.empiricalGaussianCovariance n ω selection j2 j4 +
       D.empiricalGaussianCovariance n ω selection j1 j4 * D.empiricalGaussianCovariance n ω selection j2 j3)| ≤
      64 * ‖signalChaos (D.empiricalBulkSignal n ω hd selection hinj hbulk).weight
        (D.empiricalBulkSignal n ω hd selection hinj hbulk).signal 4‖ := by
  have hv (j) : rowVariance (D.empiricalPhysicalRowCoordinates n ω (by omega) selection j) ≤ 1 :=
    (D.empiricalPhysicalRowCoordinates_variance n ω hd selection hbulk j).le
  have hh := mixed_fourth_moment_bound_unit_rows (D.empiricalBulkSignal n ω hd selection hinj hbulk)
    (D.empiricalPhysicalRowCoordinates n ω (by omega) selection j1)
    (D.empiricalPhysicalRowCoordinates n ω (by omega) selection j2)
    (D.empiricalPhysicalRowCoordinates n ω (by omega) selection j3)
    (D.empiricalPhysicalRowCoordinates n ω (by omega) selection j4)
    (hv j1) (hv j2) (hv j3) (hv j4)
  unfold mixedFourthDiscrepancy gaussianFourthWick at hh
  simp_rw [D.empiricalBulkSignal_weight, D.empiricalBulkSignal_physical_row,
    D.empiricalPhysicalRowCoordinates_covariance n ω hd selection hbulk] at hh
  exact hh

end GeneralizedBulk.External.RegularSpectralData
