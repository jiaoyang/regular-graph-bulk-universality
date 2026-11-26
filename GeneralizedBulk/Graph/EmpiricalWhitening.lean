import GeneralizedBulk.Entropy.PhysicalStarFrame
import GeneralizedBulk.Graph.StarCovariance

/-! The actual normalized whitened empirical eigenvector-star signal. -/
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Entropy.Channel GeneralizedBulk.Entropy.Mehler

variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

abbrev EmpiricalStarSample (d : ℕ) (size : ℕ) := Fin size × Equiv.Perm (Fin d)

def empiricalStarWeight (D : RegularSpectralData d N Ω) : EmpiricalStarSample d (N n) → ℝ :=
  fun _ => (Fintype.card (EmpiricalStarSample d (N n)) : ℝ)⁻¹

theorem empiricalStarWeight_nonneg (s : EmpiricalStarSample d (N n)) :
    0 ≤ D.empiricalStarWeight n s := by unfold empiricalStarWeight; positivity

theorem empiricalStarWeight_total : (∑ s, D.empiricalStarWeight n s) = 1 := by
  classical
  have hcard : (Fintype.card (EmpiricalStarSample d (N n)) : ℝ) ≠ 0 := by
    simp [EmpiricalStarSample, Nat.ne_of_gt (D.size_pos n), Fintype.card_ne_zero]
  simp only [empiricalStarWeight, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_inv_cancel₀ hcard

theorem starSample_eigen_constraint {k : ℕ} (hd : 2 ≤ d) (selection : Fin k → Fin (N n))
    (s : EmpiricalStarSample d (N n)) (a : Fin k) :
    (∑ j : Fin d, D.starSample n ω (fun b => D.eigenvector n ω (selection b)) s (a, j.succ)) =
      ((d : ℝ) * (D.eigenvalue n ω (selection a) / d)) *
        D.starSample n ω (fun b => D.eigenvector n ω (selection b)) s (a, 0) := by
  classical
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hperm : (∑ i : Fin d, D.eigenvector n ω (selection a) (D.neighbor n ω s.1 (s.2 i))) =
      ∑ i : Fin d, D.eigenvector n ω (selection a) (D.neighbor n ω s.1 i) :=
    Equiv.sum_comp s.2 (fun i => D.eigenvector n ω (selection a) (D.neighbor n ω s.1 i))
  simp only [starSample, Fin.cases_succ, Fin.cases_zero]
  rw [← Finset.mul_sum, hperm, D.eigenvector_neighbor_sum n ω]
  field_simp [hd0]
  ring

def empiricalPhysicalStar {k : ℕ} (hd : 2 ≤ d) (selection : Fin k → Fin (N n))
    (s : EmpiricalStarSample d (N n)) (a : Fin k) :
    physicalStar d (D.eigenvalue n ω (selection a) / d) :=
  ⟨(WithLp.equiv 2 _).symm (fun j => Option.elim j
    (D.starSample n ω (fun b => D.eigenvector n ω (selection b)) s (a, 0))
    (fun i => D.starSample n ω (fun b => D.eigenvector n ω (selection b)) s (a, i.succ))), by
    change (∑ i : Fin d, D.starSample n ω (fun b => D.eigenvector n ω (selection b)) s (a, i.succ)) -
      ((d : ℝ) * (D.eigenvalue n ω (selection a) / d)) *
        D.starSample n ω (fun b => D.eigenvector n ω (selection b)) s (a, 0) = 0
    exact sub_eq_zero.mpr (D.starSample_eigen_constraint n ω hd selection s a)⟩

def empiricalWhiteStar {k : ℕ} (hd : 2 ≤ d) (selection : Fin k → Fin (N n))
    (s : EmpiricalStarSample d (N n)) : ColoredStar d k :=
  (WithLp.equiv 2 _).symm (fun a => inverseWhitening d (D.eigenvalue n ω (selection a) / d)
    (GeneralizedBulk.Gaussian.starRho d (D.eigenvalue n ω (selection a)))
    (D.empiricalPhysicalStar n ω hd selection s a))

theorem empiricalWhiteStar_row {k : ℕ} (hd : 2 ≤ d) (selection : Fin k → Fin (N n))
    (hE : ∀ a, |D.eigenvalue n ω (selection a)| < d) (s : EmpiricalStarSample d (N n))
    (j : Fin k × Fin (d + 1)) :
    @inner ℝ (ColoredStar d k) _
      (coloredPhysicalRow d k hd (fun a => D.eigenvalue n ω (selection a)) j)
      (D.empiricalWhiteStar n ω hd selection s) =
      D.starSample n ω (fun a => D.eigenvector n ω (selection a)) s j := by
  rcases j with ⟨a, j⟩
  rw [coloredPhysicalRow, blockVector_inner]
  change @inner ℝ (WhiteStar d) _ (GeneralizedBulk.Gaussian.starRow d hd (D.eigenvalue n ω (selection a)) j)
    (inverseWhitening d _ _ _) = _
  rw [starRow_inner_inverseWhitening d hd _ (hE a)]
  induction j using Fin.cases with
  | zero => rfl
  | succ i => rfl

theorem selected_eigen_nonconstant_of_bulk {k : ℕ} (selection : Fin k → Fin (N n))
    (hE : ∀ a, |D.eigenvalue n ω (selection a)| < d) (a : Fin k) :
    selection a ≠ ⟨0, D.size_pos n⟩ := by
  intro h
  have he := hE a
  rw [h, D.constant_eigenvalue n ω, abs_of_nonneg (Nat.cast_nonneg d)] at he
  exact (lt_irrefl (d : ℝ)) he

/-- The actual finite sampled star becomes a normalized signal through the
proved spanning-frame moment transport and the fixed scalar-adapted basis. -/
def empiricalNormalizedSignal {k : ℕ} (hd : 2 ≤ d) (selection : Fin k → Fin (N n))
    (hinj : Function.Injective selection) (hE : ∀ a, |D.eigenvalue n ω (selection a)| < d) :
    NormalizedFiniteSignal (ScalarCoordinate d k) (EmpiricalStarSample d (N n)) := by
  classical
  apply normalizedSignalOfSpanningFrame (D.empiricalStarWeight n)
    (D.empiricalWhiteStar n ω hd selection)
    (coloredPhysicalRow d k hd (fun a => D.eigenvalue n ω (selection a)))
    (coloredPhysicalRow_span d k hd _ hE) (scalarAdaptedBasis d k)
    (D.empiricalStarWeight_nonneg n) (D.empiricalStarWeight_total n)
  · intro j
    simp_rw [D.empiricalWhiteStar_row n ω hd selection hE]
    unfold empiricalStarWeight
    rw [← Finset.mul_sum]
    have h := D.integral_star_eigen_coordinate_zero n ω selection
      (fun a => D.selected_eigen_nonconstant_of_bulk n ω selection hE a) j.1 j.2
    rw [D.integral_starLaw n ω] at h
    exact h
  · intro j l
    simp_rw [D.empiricalWhiteStar_row n ω hd selection hE]
    rw [coloredPhysicalRow_gram d k hd _ hE]
    unfold empiricalStarWeight
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    have h := D.integral_star_orthonormal_eigen_covariance n ω hd selection hinj j.1 l.1 j.2 l.2
    rw [D.integral_starLaw n ω] at h
    exact h

end GeneralizedBulk.External.RegularSpectralData
