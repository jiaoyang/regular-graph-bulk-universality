import GeneralizedBulk.Entropy.GaussianEnvelope
import GeneralizedBulk.Entropy.MehlerFiniteSignals

/-! Exact moment and signal-size transport under the actual observation coordinates. -/
noncomputable section
open scoped BigOperators

namespace GeneralizedBulk.Entropy.Mehler
variable {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S]
variable (weight : S → ℝ) (signal : S → I → ℝ)
variable (hmean : ∀ i, ∑ s, weight s * signal s i = 0)
variable (hcov : ∀ i j, ∑ s, weight s * signal s i * signal s j = if i = j then 1 else 0)

include hmean in
theorem weighted_linear_mean (L : Matrix I I ℝ) (i : I) :
    (∑ s, weight s * L.mulVec (signal s) i) = 0 :=
  weighted_cross weight signal hmean (L i)

include hcov in
theorem weighted_bilinear (u v : I → ℝ) :
    (∑ s, weight s * (∑ i, u i * signal s i) * (∑ j, v j * signal s j)) =
      ∑ i, u i * v i := by
  classical
  have he (s : S) : weight s * (∑ i, u i * signal s i) * (∑ j, v j * signal s j) =
      ∑ i, ∑ j, (u i * v j) * (weight s * signal s i * signal s j) := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, hcov]
  simp

include hcov in
theorem weighted_orthogonal_covariance (L : Matrix I I ℝ) (hL : L * L.transpose = 1) (i j : I) :
    (∑ s, weight s * L.mulVec (signal s) i * L.mulVec (signal s) j) =
      if i = j then 1 else 0 := by
  rw [show (∑ s, weight s * L.mulVec (signal s) i * L.mulVec (signal s) j) =
      ∑ l, L i l * L j l from weighted_bilinear weight signal hcov (L i) (L j)]
  have he := congrFun (congrFun hL i) j
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using he

theorem orthogonal_entry_abs_le_one (L : Matrix I I ℝ) (hL : L * L.transpose = 1) (i j : I) :
    |L i j| ≤ 1 := by
  have he := congrFun (congrFun hL i) i
  have hrow : (∑ l, (L i l) ^ 2) = 1 := by
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, ite_true, pow_two] using he
  have hj := Finset.single_le_sum (fun l (_ : l ∈ Finset.univ) => sq_nonneg (L i l)) (Finset.mem_univ j)
  rw [hrow] at hj
  nlinarith [abs_nonneg (L i j), sq_abs (L i j)]

theorem coordinateL1_orthogonal_le (L : Matrix I I ℝ) (hL : L * L.transpose = 1) (y : I → ℝ) :
    coordinateL1 (L.mulVec y) ≤ (Fintype.card I : ℝ) * coordinateL1 y := by
  have hentry (i : I) : |L.mulVec y i| ≤ coordinateL1 y := by
    calc
      _ ≤ ∑ j, |L i j * y j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |y j| := by
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul]
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (orthogonal_entry_abs_le_one L hL i j) (abs_nonneg (y j))
  calc
    _ ≤ ∑ i : I, coordinateL1 y := Finset.sum_le_sum (fun i _ => hentry i)
    _ = _ := by simp

end GeneralizedBulk.Entropy.Mehler
