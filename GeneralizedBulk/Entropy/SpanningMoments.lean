import GeneralizedBulk.Entropy.NormalizedFiniteSignal

/-! Exact whitening moments can be checked on any spanning physical frame. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Mehler

variable {E I J S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype S]
variable (weight : S → ℝ) (sample : S → E) (row : J → E)
variable (hspan : Submodule.span ℝ (Set.range row) = ⊤)

include hspan in
theorem spanning_mean_zero (hmean : ∀ j, ∑ s, weight s * @inner ℝ E _ (row j) (sample s) = 0)
    (u : E) : (∑ s, weight s * @inner ℝ E _ u (sample s)) = 0 := by
  have hu : u ∈ Submodule.span ℝ (Set.range row) := by rw [hspan]; trivial
  induction hu using Submodule.span_induction with
  | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hmean j
  | zero => simp
  | add x y hx hy ihx ihy =>
    simp only [inner_add_left, mul_add, Finset.sum_add_distrib, ihx, ihy, add_zero]
  | smul c x hx ih =>
    simp only [real_inner_smul_left]
    calc
      _ = c * ∑ s, weight s * @inner ℝ E _ x (sample s) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s hs
        ring
      _ = 0 := by rw [ih, mul_zero]

include hspan in
theorem spanning_covariance
    (hcov : ∀ i j, (∑ s, weight s * @inner ℝ E _ (row i) (sample s) *
      @inner ℝ E _ (row j) (sample s)) = @inner ℝ E _ (row i) (row j))
    (u v : E) : (∑ s, weight s * @inner ℝ E _ u (sample s) * @inner ℝ E _ v (sample s)) =
      @inner ℝ E _ u v := by
  have hu : u ∈ Submodule.span ℝ (Set.range row) := by rw [hspan]; trivial
  have hv : v ∈ Submodule.span ℝ (Set.range row) := by rw [hspan]; trivial
  refine Submodule.span_induction₂ (p := fun x y _ _ =>
    (∑ s, weight s * @inner ℝ E _ x (sample s) * @inner ℝ E _ y (sample s)) =
      @inner ℝ E _ x y) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hu hv
  · intro x y hx hy
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, rfl⟩ := hy
    exact hcov i j
  · intro y hy
    simp
  · intro x hx
    simp
  · intro x y z hx hy hz ihx ihy
    simp only [inner_add_left, mul_add, add_mul, Finset.sum_add_distrib, ihx, ihy]
  · intro x y z hx hy hz ihy ihz
    simp only [inner_add_left, inner_add_right, mul_add, Finset.sum_add_distrib, ihy, ihz]
  · intro c x y hx hy ih
    simp only [real_inner_smul_left]
    calc
      _ = c * ∑ s, weight s * @inner ℝ E _ x (sample s) * @inner ℝ E _ y (sample s) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s hs
        ring
      _ = _ := by rw [ih]
  · intro c x y hx hy ih
    simp only [real_inner_smul_left, real_inner_smul_right]
    calc
      _ = c * ∑ s, weight s * @inner ℝ E _ x (sample s) * @inner ℝ E _ y (sample s) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s hs
        ring
      _ = _ := by rw [ih]

variable [Fintype I] [DecidableEq I]

/-- Finite physical-frame moment identities produce the literal normalized
whitened signal used by the actual Gaussian entropy theorems. -/
def normalizedSignalOfSpanningFrame (basis : OrthonormalBasis I ℝ E)
    (hweight : ∀ s, 0 ≤ weight s) (htotal : ∑ s, weight s = 1)
    (hmean : ∀ j, ∑ s, weight s * @inner ℝ E _ (row j) (sample s) = 0)
    (hcov : ∀ i j, (∑ s, weight s * @inner ℝ E _ (row i) (sample s) *
      @inner ℝ E _ (row j) (sample s)) = @inner ℝ E _ (row i) (row j)) :
    NormalizedFiniteSignal I S where
  weight := weight
  signal s i := @inner ℝ E _ (basis i) (sample s)
  nonneg := hweight
  total := htotal
  mean i := spanning_mean_zero weight sample row hspan hmean (basis i)
  covariance i j := by
    rw [spanning_covariance weight sample row hspan hcov]
    exact orthonormal_iff_ite.mp basis.orthonormal i j

end GeneralizedBulk.Entropy.Mehler
