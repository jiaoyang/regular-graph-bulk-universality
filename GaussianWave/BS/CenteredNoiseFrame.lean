import GaussianWave.BS.ScoreProjection

/-!
# A genuine orthonormal factor for centered sibling noise

The chosen factor has `m` orthonormal columns in the zero-sum hyperplane of
`m+1` coordinates.  Existence follows from an actual orthogonal completion
of the normalized constant row, including the zero-dimensional case.
-/
noncomputable section
open scoped BigOperators
namespace GaussianWave.BS

theorem exists_centeredNoiseFrame (m : ℕ) :
    ∃ N : Matrix (Fin (m + 1)) (Fin m) ℝ,
      N.transpose * N = 1 ∧
      (∀ a b, (N * N.transpose) a b = (if a = b then 1 else 0) - 1 / (m + 1 : ℝ)) ∧
      ∀ j, (∑ a, N a j) = 0 := by
  let O : Matrix Unit (Fin (m + 1)) ℝ := fun _ _ => 1 / Real.sqrt (m + 1)
  have hs : Real.sqrt (m + 1 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hs2 : Real.sqrt (m + 1 : ℝ) ^ 2 = (m + 1) := Real.sq_sqrt (by positivity)
  have hO : O * O.transpose = 1 := by
    ext a b
    cases a; cases b
    simp only [Matrix.mul_apply, Matrix.transpose_apply, O, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Matrix.one_apply, if_pos rfl,
      Nat.cast_add, Nat.cast_one]
    rw [← pow_two, div_pow, one_pow, hs2]
    field_simp
  have hex := exists_orthogonal_row_completion O hO
  have hdim : Fintype.card (Fin (m + 1)) - Fintype.card Unit = m := by simp
  rw [hdim] at hex
  obtain ⟨R, hrow, hRR, hRtR⟩ := hex
  let N : Matrix (Fin (m + 1)) (Fin m) ℝ := fun a j => R (Sum.inr j) a
  refine ⟨N, ?_, ?_, ?_⟩
  · ext i j
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      Sum.inr.injEq, N] using congrArg (fun M => M (Sum.inr i) (Sum.inr j)) hRR
  · intro a b
    have h := congrArg (fun M => M a b) hRtR
    have hrow' (a : Fin (m + 1)) : R (Sum.inl ()) a = 1 / Real.sqrt (m + 1 : ℝ) :=
      congrFun (hrow ()) a
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type,
      Fintype.sum_unique, hrow', Matrix.one_apply] at h
    have hc : (1 / Real.sqrt (m + 1 : ℝ)) * (1 / Real.sqrt (m + 1 : ℝ)) =
        1 / (m + 1 : ℝ) := by rw [← pow_two, div_pow, one_pow, hs2]
    rw [hc] at h
    change (∑ j, R (Sum.inr j) a * R (Sum.inr j) b) = _
    linarith
  · intro j
    have h := congrArg (fun M => M (Sum.inl ()) (Sum.inr j)) hRR
    have hrow' (a : Fin (m + 1)) : R (Sum.inl ()) a = 1 / Real.sqrt (m + 1 : ℝ) :=
      congrFun (hrow ()) a
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hrow', Matrix.one_apply,
      Sum.inl_ne_inr, if_false, ← Finset.mul_sum] at h
    change (∑ a, R (Sum.inr j) a) = 0
    exact (mul_eq_zero.mp h).resolve_left (one_div_ne_zero hs)

def centeredNoiseFrame (m : ℕ) : Matrix (Fin (m + 1)) (Fin m) ℝ :=
  Classical.choose (exists_centeredNoiseFrame m)

theorem centeredNoiseFrame_columns (m : ℕ) :
    (centeredNoiseFrame m).transpose * centeredNoiseFrame m = 1 :=
  (Classical.choose_spec (exists_centeredNoiseFrame m)).1

theorem centeredNoiseFrame_gram (m : ℕ) (a b : Fin (m + 1)) :
    (centeredNoiseFrame m * (centeredNoiseFrame m).transpose) a b =
      (if a = b then 1 else 0) - 1 / (m + 1 : ℝ) :=
  (Classical.choose_spec (exists_centeredNoiseFrame m)).2.1 a b

theorem centeredNoiseFrame_sum (m : ℕ) (j : Fin m) :
    (∑ a, centeredNoiseFrame m a j) = 0 :=
  (Classical.choose_spec (exists_centeredNoiseFrame m)).2.2 j

theorem centeredNoiseFrame_mulVec_sum (m : ℕ) (z : Fin m → ℝ) :
    (∑ a, (centeredNoiseFrame m).mulVec z a) = 0 := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, centeredNoiseFrame_sum, zero_mul, Finset.sum_const_zero]

theorem centeredNoiseFrame_mulVec_energy (m : ℕ) (z : Fin m → ℝ) :
    (∑ a, ((centeredNoiseFrame m).mulVec z a) ^ 2) = ∑ j, z j ^ 2 := by
  calc
    _ = (centeredNoiseFrame m).mulVec z ⬝ᵥ ((centeredNoiseFrame m).mulVec z) := by
      simp only [dotProduct, pow_two]
    _ = z ⬝ᵥ ((centeredNoiseFrame m).transpose.mulVec ((centeredNoiseFrame m).mulVec z)) := by
      symm
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    _ = z ⬝ᵥ ((centeredNoiseFrame m).transpose * centeredNoiseFrame m).mulVec z := by
      rw [Matrix.mulVec_mulVec]
    _ = _ := by rw [centeredNoiseFrame_columns, Matrix.one_mulVec]; simp only [dotProduct, pow_two]

end GaussianWave.BS
