import GeneralizedBulk.Entropy.MatrixEntryBounds

/-! Elementary submultiplicative bounds for actual finite matrix entry sums. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.Entropy
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem matrixEntryL1_smul (c : ℝ) (A : Matrix I I ℝ) : matrixEntryL1 (c • A) = |c| * matrixEntryL1 A := by
  unfold matrixEntryL1
  simp only [Matrix.smul_apply, smul_eq_mul, abs_mul, Finset.mul_sum]

theorem matrixEntryL1_transpose (A : Matrix I I ℝ) : matrixEntryL1 A.transpose = matrixEntryL1 A := by
  unfold matrixEntryL1
  exact Finset.sum_comm

theorem matrixEntryL1_one : matrixEntryL1 (1 : Matrix I I ℝ) = Fintype.card I := by
  classical
  simp [matrixEntryL1, Matrix.one_apply, apply_ite]

theorem abs_matrix_entry_le_matrixEntryL1 (A : Matrix I I ℝ) (i j : I) : |A i j| ≤ matrixEntryL1 A := by
  exact (Finset.single_le_sum (fun t _ => abs_nonneg (A i t)) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun t _ => Finset.sum_nonneg (fun k _ => abs_nonneg (A t k))) (Finset.mem_univ i))

theorem matrixEntryL1_mul_le (A B : Matrix I I ℝ) : matrixEntryL1 (A*B) ≤ matrixEntryL1 A * matrixEntryL1 B := by
  have hrow (k : I) : (∑ j, |B k j|) ≤ matrixEntryL1 B :=
    Finset.single_le_sum (fun t _ => Finset.sum_nonneg (fun j _ => abs_nonneg (B t j))) (Finset.mem_univ k)
  calc
    _ ≤ ∑ i, ∑ j, ∑ k, |A i k| * |B k j| := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      simpa only [Matrix.mul_apply, abs_mul] using Finset.abs_sum_le_sum_abs (s := Finset.univ) (fun k => A i k * B k j)
    _ = ∑ i, ∑ k, |A i k| * ∑ j, |B k j| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
    _ ≤ ∑ i, ∑ k, |A i k| * matrixEntryL1 B := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hrow k) (abs_nonneg _))
    _ = _ := by simp only [matrixEntryL1, Finset.sum_mul]

theorem matrixEntryL1_sub_le (A B : Matrix I I ℝ) : matrixEntryL1 (A-B) ≤ matrixEntryL1 A + matrixEntryL1 B := by
  unfold matrixEntryL1
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  exact Finset.sum_le_sum (fun j _ => abs_sub (A i j) (B i j))


theorem matrixEntryL1_le_of_entrywise (A : Matrix I I ℝ) (e : ℝ) (hA : ∀ i j, |A i j| ≤ e) :
    matrixEntryL1 A ≤ (Fintype.card I : ℝ)^2*e := by
  calc
    _ ≤ ∑ _i : I, ∑ _j : I, e := Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hA i j))
    _ = _ := by simp; ring

end GeneralizedBulk.Entropy
