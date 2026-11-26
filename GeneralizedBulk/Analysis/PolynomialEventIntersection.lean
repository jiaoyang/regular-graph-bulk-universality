import Mathlib

/-! Polynomial exceptional-probability rates survive a genuine common event. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace GeneralizedBulk.Analysis

 theorem intersection_polynomial_failure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (N : ℕ → ℕ) (hN : ∀ n,0 < N n)
    (A B : ℕ → Set Ω) (a b C D : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hC : 0 < C) (hD : 0 < D)
    (hA : ∀ᶠ n in atTop,P.real (A n)ᶜ ≤ C*(N n : ℝ)^(-a))
    (hB : ∀ᶠ n in atTop,P.real (B n)ᶜ ≤ D*(N n : ℝ)^(-b)) :
    ∃ β M : ℝ,0 < β ∧ 0 < M ∧ ∀ᶠ n in atTop,
      P.real (A n ∩ B n)ᶜ ≤ M*(N n : ℝ)^(-β) := by
  refine ⟨min a b,C+D,lt_min ha hb,add_pos hC hD,?_⟩
  filter_upwards [hA,hB] with n hnA hnB
  have hN1 : (1 : ℝ) ≤ N n := by exact_mod_cast hN n
  have hma := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1
    (show -a ≤ -min a b by linarith [min_le_left a b])) hC.le
  have hmb := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1
    (show -b ≤ -min a b by linarith [min_le_right a b])) hD.le
  rw [Set.compl_inter]
  exact (measureReal_union_le _ _).trans ((add_le_add (hnA.trans hma) (hnB.trans hmb)).trans_eq (by ring))

end GeneralizedBulk.Analysis
