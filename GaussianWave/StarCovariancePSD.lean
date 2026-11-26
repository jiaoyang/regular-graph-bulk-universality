import GaussianWave.Covariance
import GaussianWave.Foundation

/-!
# Positivity of the canonical regular-tree star covariance

The quadratic form is decomposed explicitly into a square in the root/mean
leaf direction and a nonnegative transverse variance. This is the Gram-factor
argument, with the transverse simplex Gram matrix evaluated by a finite sum.
No finite graph eigenvalue or probabilistic covariance assumption is required.
-/
noncomputable section
open scoped BigOperators

namespace GaussianWave.RegularEigenData

lemma sum_star_leaf_kernel {d : ℕ} (β : ℝ) (f : Fin d → ℝ) (i : Fin d) :
    (∑ j, (if i = j then 1 else β) * f j) =
      (1 - β) * f i + β * ∑ j, f j := by
  classical
  have he (j : Fin d) : (if i = j then 1 else β) * f j =
      (if i = j then (1 - β) * f j else 0) + β * f j := by
    split_ifs <;> ring
  simp_rw [he, Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  simp

/-- Evaluate the complete root-and-leaf quadratic form before factoring. -/
lemma starWaveCovariance_quadratic_expansion (d : ℕ) (energy : ℝ)
    (t : Fin (d + 1) → ℝ) :
    finiteCovarianceQuadratic (starWaveCovariance d energy) t =
      t 0 ^ 2 + 2 * (energy / d) * t 0 * (∑ i : Fin d, t i.succ) +
      (1 - (energy ^ 2 - d) / ((d : ℝ) * (d - 1))) * (∑ i : Fin d, t i.succ ^ 2) +
      ((energy ^ 2 - d) / ((d : ℝ) * (d - 1))) * (∑ i : Fin d, t i.succ) ^ 2 := by
  classical
  let β := (energy ^ 2 - d) / ((d : ℝ) * (d - 1))
  let s := ∑ i : Fin d, t i.succ
  let q := ∑ i : Fin d, t i.succ ^ 2
  have he (i : Fin d) :
      (∑ j : Fin d, t i.succ * (if i = j then 1 else β) * t j.succ) =
        t i.succ * ((1 - β) * t i.succ + β * s) := by
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    congr 1
    exact sum_star_leaf_kernel β (fun j => t j.succ) i
  have hs : (∑ i : Fin d, (t i.succ * (energy / d) * t 0 +
      t i.succ * ((1 - β) * t i.succ + β * s))) =
      (energy / d) * t 0 * s + (1 - β) * q + β * s ^ 2 := by
    have he' (i : Fin d) : t i.succ * (energy / d) * t 0 +
        t i.succ * ((1 - β) * t i.succ + β * s) =
          (energy / d * t 0) * t i.succ + (1 - β) * t i.succ ^ 2 +
            (β * s) * t i.succ := by ring
    simp_rw [he', Finset.sum_add_distrib, ← Finset.mul_sum]
    dsimp [s, q]
    ring
  unfold finiteCovarianceQuadratic
  rw [Fin.sum_univ_succ]
  simp only [Fin.sum_univ_succ, starWaveCovariance, Fin.cases_zero, Fin.cases_succ,
    mul_one]
  change t 0 * t 0 + (∑ j : Fin d, t 0 * (energy / d) * t j.succ) +
    (∑ i : Fin d, (t i.succ * (energy / d) * t 0 +
      ∑ j : Fin d, t i.succ * (if i = j then 1 else β) * t j.succ)) = _
  simp_rw [he]
  rw [hs, ← Finset.mul_sum]
  dsimp [s, q, β]
  ring

/-- Explicit root/mean-leaf plus transverse-simplex Gram decomposition. -/
theorem starWaveCovariance_quadratic_factor (d : ℕ) (energy : ℝ)
    (hd : 2 ≤ d) (t : Fin (d + 1) → ℝ) :
    finiteCovarianceQuadratic (starWaveCovariance d energy) t =
      (t 0 + (energy / d) * ∑ i : Fin d, t i.succ) ^ 2 +
      ((d : ℝ) ^ 2 - energy ^ 2) / ((d : ℝ) * (d - 1)) *
        ((∑ i : Fin d, t i.succ ^ 2) - (∑ i : Fin d, t i.succ) ^ 2 / d) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hd1 : (d : ℝ) - 1 ≠ 0 := by linarith
  rw [starWaveCovariance_quadratic_expansion]
  field_simp
  ring

/-- Canonical variance-one star covariance is positive semidefinite for all
|energy|≤degree. In particular this applies throughout the bulk interval. -/
theorem starWaveCovariance_posSemidef (d : ℕ) (energy : ℝ)
    (hd : 2 ≤ d) (henergy : |energy| ≤ (d : ℝ)) :
    (starWaveCovariance d energy).PosSemidef := by
  classical
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  constructor
  · change (starWaveCovariance d energy).conjTranspose = starWaveCovariance d energy
    ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial]
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j <;> simp [starWaveCovariance]
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp [starWaveCovariance]
      · by_cases hij : i = j
        · subst j
          simp [starWaveCovariance]
        · simp [starWaveCovariance, hij, Ne.symm hij]
  · intro t
    have hq : 0 ≤ finiteCovarianceQuadratic (starWaveCovariance d energy) t := by
      rw [starWaveCovariance_quadratic_factor d energy hd t]
      have hnum : 0 ≤ (d : ℝ) ^ 2 - energy ^ 2 := by
        have he := abs_le.mp henergy
        nlinarith [sq_nonneg energy]
      have hcoeff : 0 ≤ ((d : ℝ) ^ 2 - energy ^ 2) / ((d : ℝ) * (d - 1)) :=
        div_nonneg hnum (mul_nonneg hd0.le hd1.le)
      have hcs : (∑ i : Fin d, t i.succ) ^ 2 ≤
          (d : ℝ) * ∑ i : Fin d, t i.succ ^ 2 := by
        simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin d => t i.succ)
      have htrans : 0 ≤ (∑ i : Fin d, t i.succ ^ 2) -
          (∑ i : Fin d, t i.succ) ^ 2 / d := by
        exact sub_nonneg.mpr ((div_le_iff₀ hd0).mpr (by nlinarith [hcs]))
      exact add_nonneg (sq_nonneg _) (mul_nonneg hcoeff htrans)
    simpa only [finiteCovarianceQuadratic, star_trivial, dotProduct, Matrix.mulVec,
      Finset.mul_sum, mul_assoc] using hq

end GaussianWave.RegularEigenData
