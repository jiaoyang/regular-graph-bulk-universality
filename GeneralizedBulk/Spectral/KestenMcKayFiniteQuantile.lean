import GeneralizedBulk.Spectral.KestenMcKayQuantile

/-! Concrete equal-mass finite Kesten–McKay quantile grids. -/
noncomputable section
open Set MeasureTheory
namespace GeneralizedBulk.KestenMcKay

def unitFraction (N : ℕ) (hN : 0 < N) (j : ℕ) : Icc (0 : ℝ) 1 :=
  ⟨(min j N : ℕ) / (N : ℝ), div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), by
    apply (div_le_one (Nat.cast_pos.mpr hN)).mpr
    exact_mod_cast Nat.min_le_right j N⟩

def quantileNode (d : ℝ) (hd : 3 ≤ d) (N : ℕ) (hN : 0 < N) (j : ℕ) : ℝ :=
  quantile d hd (unitFraction N hN j)

theorem monotone_quantileNode (d : ℝ) (hd : 3 ≤ d) (N : ℕ) (hN : 0 < N) :
    Monotone (quantileNode d hd N hN) := by
  intro i j hij
  apply (strictMono_quantile d hd).monotone
  change (min i N : ℕ) / (N : ℝ) ≤ (min j N : ℕ) / (N : ℝ)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  exact_mod_cast min_le_min_right N hij

theorem quantileNode_lower (d : ℝ) (hd : 3 ≤ d) (N : ℕ) (hN : 0 < N) :
    quantileNode d hd N hN 0 = -radius d := by
  convert quantile_lower d hd using 1
  apply congrArg (quantile d hd)
  apply Subtype.ext
  simp [unitFraction]

theorem quantileNode_upper (d : ℝ) (hd : 3 ≤ d) (N : ℕ) (hN : 0 < N) :
    quantileNode d hd N hN N = radius d := by
  convert quantile_upper d hd using 1
  apply congrArg (quantile d hd)
  apply Subtype.ext
  simp [unitFraction, (Nat.cast_pos.mpr hN : (0 : ℝ) < N).ne']

theorem quantileNode_cell_mass (d : ℝ) (hd : 3 ≤ d) (N : ℕ) (hN : 0 < N)
    (j : ℕ) (hj : j < N) :
    (∫ x in quantileNode d hd N hN j..quantileNode d hd N hN (j + 1), rawDensity d x) = 1 / (N : ℝ) := by
  rw [quantileNode, quantileNode, integral_quantile_cell]
  dsimp [unitFraction]
  rw [Nat.min_eq_left (by omega : j + 1 ≤ N), Nat.min_eq_left hj.le, Nat.cast_add, Nat.cast_one]
  ring

/-- Decreasing quantiles with upper-tail mass j/N, matching the ordered
nontrivial eigenvalue convention of the HY input. -/
def finiteQuantile (d : ℝ) (hd : 3 ≤ d) (N : ℕ) (hN : 0 < N) (j : Fin N) : ℝ :=
  quantileNode d hd N hN (N - j.val)

theorem cdf_finiteQuantile (d : ℝ) (hd : 3 ≤ d) (N : ℕ) (hN : 0 < N) (j : Fin N) :
    cdf d (finiteQuantile d hd N hN j) = 1 - (j.val : ℝ) / N := by
  rw [finiteQuantile, quantileNode, cdf_quantile]
  dsimp [unitFraction]
  rw [Nat.min_eq_left (Nat.sub_le N j.val), Nat.cast_sub j.isLt.le]
  have hn : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
  field_simp
  <;> ring

end GeneralizedBulk.KestenMcKay
