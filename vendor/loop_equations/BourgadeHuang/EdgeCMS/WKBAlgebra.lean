import BourgadeHuang.EdgeCMS.Basic

/-! Exact square-root cancellation in the edge WKB gauge.  This file
contains algebraic identities only; analytic root branches and their
derivatives are treated separately. -/
noncomputable section
open scoped BigOperators

namespace BourgadeHuang.EdgeCMS
open CMS

/-- Exponent of the square-root pair factor. -/
def rootPairExponent {d : ℕ} (β : ℂ) (c : Fin d → ℂ) (i j : Fin d) : ℂ :=
  -(2 / β) * c i * c j

theorem rootPairExponent_symm {d : ℕ} (β : ℂ) (c : Fin d → ℂ) (i j : Fin d) :
    rootPairExponent β c i j = rootPairExponent β c j i := by
  unfold rootPairExponent
  ring

/-- Logarithmic derivative of the pair factor in coordinate `i`, where
`rᵢ²=zᵢ` and each square root can have either sign. -/
def rootPairCorrection {d : ℕ} (β : ℂ) (c r : Fin d → ℂ) (i j : Fin d) : ℂ :=
  -(c i * c j) / (β * r i * (r i + r j))

def rootCorrection {d : ℕ} (β : ℂ) (c r : Fin d → ℂ) (i : Fin d) : ℂ :=
  ∑ j ∈ Finset.univ.erase i, rootPairCorrection β c r i j

theorem root_sum_ne_zero {d : ℕ} (r : Fin d → ℂ) (z : Point d)
    (hroot : ∀ i, r i ^ 2 = z i) (hz : CollisionFree z) {i j : Fin d}
    (hij : i ≠ j) : r i + r j ≠ 0 := by
  intro h
  have he : r i = -r j := eq_neg_of_add_eq_zero_left h
  apply hij
  apply hz
  rw [← hroot i, ← hroot j, he]
  ring

/-- Cancellation of the entire order `R^(-1/2)` pair contribution in
the conjugated scalar potential. -/
theorem root_pair_linear_cancellation {d : ℕ} (β : ℂ) (c r : Fin d → ℂ)
    (z : Point d) (hβ : β ≠ 0) (hroot : ∀ i, r i ^ 2 = z i)
    (hr : ∀ i, r i ≠ 0) (hz : CollisionFree z) {i j : Fin d} (hij : i ≠ j) :
    2 * (c i * r i) * rootPairCorrection β c r i j +
      (2 / β) * (c i * c j * (c i * r i) - c i ^ 2 * (c j * r j)) /
        (z i - z j) = 0 := by
  have hs := root_sum_ne_zero r z hroot hz hij
  have hg := hz.sub_ne_zero hij
  unfold rootPairCorrection
  rw [← hroot i, ← hroot j]
  have hg' : r i ^ 2 - r j ^ 2 ≠ 0 := by simpa only [hroot] using hg
  field_simp [hβ, hr i, hs, hg']
  ring

theorem root_correction_linear_cancellation {d : ℕ} (β : ℂ) (c r : Fin d → ℂ)
    (z : Point d) (hβ : β ≠ 0) (hroot : ∀ i, r i ^ 2 = z i)
    (hr : ∀ i, r i ≠ 0) (hz : CollisionFree z) (i : Fin d) :
    2 * (c i * r i) * rootCorrection β c r i +
      (2 / β) * ∑ j ∈ Finset.univ.erase i,
        (c i * c j * (c i * r i) - c i ^ 2 * (c j * r j)) / (z i - z j) = 0 := by
  unfold rootCorrection
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro j hj
  simpa only [mul_div_assoc] using
    root_pair_linear_cancellation β c r z hβ hroot hr hz (Finset.ne_of_mem_erase hj).symm

end BourgadeHuang.EdgeCMS
