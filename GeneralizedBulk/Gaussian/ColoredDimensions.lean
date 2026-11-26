import GeneralizedBulk.Gaussian.ExtendedWhitening
import GeneralizedBulk.Entropy.ColoredEdgeBasis

/-! Literal Gaussian channel dimensions and the exact balance required by
the entropy deficit. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Channel
open GeneralizedBulk.Gaussian

theorem card_scalarCoordinate (d k : ℕ) (hd : 0 < d) :
    Fintype.card (ScalarCoordinate d k) = k * d := by
  simp [ScalarCoordinate, Fintype.card_sigma, card_whiteCoordinate d hd]

theorem coloredObserved_balanced (d k : ℕ) (hd : 2 ≤ d) :
    (∑ i : Fin d, (Fintype.card (coloredObserved d k hd i) : ℝ)) =
      2 * (Fintype.card (ScalarCoordinate d k) : ℝ) := by
  simp only [card_coloredObserved, card_scalarCoordinate d k (by omega), Nat.cast_mul,
    Nat.cast_ofNat, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end GeneralizedBulk.Entropy.Channel
