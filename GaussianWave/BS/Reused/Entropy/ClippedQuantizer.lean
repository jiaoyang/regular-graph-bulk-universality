import Mathlib

/-! The actual clipped integer-grid quantizer, its finite palette, and its
complete finite set of scalar jump boundaries. -/
noncomputable section
open scoped BigOperators Classical

namespace GaussianWave.BS.Reused.Entropy

def clipInteger (K : ℕ) (j : ℤ) : ℤ := max (-(K : ℤ)) (min ((K : ℤ)-1) j)

abbrev ClipLabel (K : ℕ) := (Finset.Icc (-(K : ℤ)) ((K : ℤ)-1) : Finset ℤ)

theorem clipInteger_lower (K : ℕ) (j : ℤ) : -(K : ℤ) ≤ clipInteger K j := le_max_left _ _

theorem clipInteger_upper (K : ℕ) (hK : 0 < K) (j : ℤ) : clipInteger K j ≤ (K : ℤ)-1 :=
  max_le (by omega) (min_le_left _ _)

theorem clipInteger_eq_self (K : ℕ) (j : ℤ) (hj0 : -(K : ℤ) ≤ j) (hj1 : j ≤ (K : ℤ)-1) :
    clipInteger K j = j := by rw [clipInteger,min_eq_right hj1,max_eq_right hj0]

theorem clipInteger_mono (K : ℕ) : Monotone (clipInteger K) :=
  fun x y hxy => max_le_max_left _ (min_le_min_left _ hxy)

def clipLabel (K : ℕ) (hK : 0 < K) (j : ℤ) : ClipLabel K :=
  ⟨clipInteger K j,Finset.mem_Icc.mpr ⟨clipInteger_lower K j,clipInteger_upper K hK j⟩⟩

theorem clipLabel_card (K : ℕ) : Fintype.card (ClipLabel K) = 2*K := by
  rw [Fintype.card_coe,Int.card_Icc]
  omega

def clipLabelEquivFin (K : ℕ) : ClipLabel K ≃ Fin (2*K) := Fintype.equivFinOfCardEq (clipLabel_card K)

def clippedGridLabel (a : ℝ) (K : ℕ) (hK : 0 < K) (x : ℝ) : ClipLabel K := clipLabel K hK ⌊x/a⌋

def codedClippedGridLabel (a : ℝ) (K : ℕ) (hK : 0 < K) (x : ℝ) : Fin (2*K) :=
  clipLabelEquivFin K (clippedGridLabel a K hK x)

theorem measurable_clippedGridLabel (a : ℝ) (K : ℕ) (hK : 0 < K) : Measurable (clippedGridLabel a K hK) :=
  (measurable_of_countable (clipLabel K hK)).comp (by fun_prop)

theorem measurable_codedClippedGridLabel (a : ℝ) (K : ℕ) (hK : 0 < K) : Measurable (codedClippedGridLabel a K hK) :=
  (measurable_of_finite (clipLabelEquivFin K)).comp (measurable_clippedGridLabel a K hK)


end GaussianWave.BS.Reused.Entropy
