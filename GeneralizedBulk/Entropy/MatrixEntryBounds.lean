import GeneralizedBulk.Entropy.GaussianLogBounds

/-! Actual squared-action bounds control the coordinate matrix norms used by entropy stability. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.Entropy
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem abs_matrix_entry_le_of_action_energy (A : Matrix I I ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ x : I → ℝ, (∑ i, (A.mulVec x i) ^ 2) ≤ K ^ 2 * ∑ i, x i ^ 2) (i j : I) :
    |A i j| ≤ K := by
  have hh := hbound (Pi.single j 1)
  simp only [Matrix.mulVec_single_one, Matrix.transpose_apply] at hh
  have he : (∑ t : I, ((Pi.single j (1 : ℝ) : I → ℝ) t) ^ 2) = (1 : ℝ) := by simp [Pi.single_apply]
  rw [he, mul_one] at hh
  have hs : A i j ^ 2 ≤ K ^ 2 :=
    (Finset.single_le_sum (fun t _ => sq_nonneg (A t j)) (Finset.mem_univ i)).trans hh
  exact (sq_le_sq₀ (abs_nonneg _) hK).mp (by simpa only [sq_abs] using hs)

theorem matrixEntryL1_le_of_action_energy (A : Matrix I I ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ x : I → ℝ, (∑ i, (A.mulVec x i) ^ 2) ≤ K ^ 2 * ∑ i, x i ^ 2) :
    matrixEntryL1 A ≤ (Fintype.card I : ℝ) ^ 2 * K := by
  calc
    _ ≤ ∑ _i : I, ∑ _j : I, K := Finset.sum_le_sum (fun i _ =>
      Finset.sum_le_sum (fun j _ => abs_matrix_entry_le_of_action_energy A K hK hbound i j))
    _ = _ := by simp; ring

theorem matrixEntryL1_add_le (A B : Matrix I I ℝ) : matrixEntryL1 (A+B) ≤ matrixEntryL1 A + matrixEntryL1 B := by
  unfold matrixEntryL1
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  exact Finset.sum_le_sum (fun j _ => abs_add_le (A i j) (B i j))

theorem matrixEntryL1_sub_swap (A B : Matrix I I ℝ) : matrixEntryL1 (A-B) = matrixEntryL1 (B-A) := by
  unfold matrixEntryL1
  simp only [Matrix.sub_apply, abs_sub_comm]

end GeneralizedBulk.Entropy
