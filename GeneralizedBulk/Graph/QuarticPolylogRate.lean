import GeneralizedBulk.Graph.HYEmpiricalFourthMoments

/-! Explicit polynomial-logarithmic loss in the actual graph quartic rate. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Entropy.Channel GeneralizedBulk.Entropy.Mehler

def empiricalWhiteningFactor (d k : ℕ) : ℝ :=
  (Fintype.card (ScalarCoordinate d k) : ℝ) * ((k : ℝ) * d * ((d : ℝ) + 1))

def empiricalQuarticPolylogConstant (d k : ℕ) (hd : 2 ≤ d) (κ C : ℝ) : ℝ :=
  (2 / Real.sqrt κ) *
    (NormalizedFiniteSignal.observationRemainderConstant (coloredObserved d k hd)) ^ (4 / 9 : ℝ) *
    (1 + ((((Fintype.card (ScalarCoordinate d k) : ℝ) + 1) * empiricalWhiteningFactor d k * C)) ^ 2) ^ 4

/-- The actual entropy quartic estimate loses only the eighth power of the
HY logarithmic bound. This is a proved numerical rate, not asymptotic notation. -/
theorem empiricalQuarticRate_polylog (d k : ℕ) (hd : 2 ≤ d) (κ C x epsilon : ℝ)
    (hκ : 0 < κ) (hx : 1 ≤ x) (hepsilon : 0 ≤ epsilon) (p : ℕ) :
    empiricalQuarticRate d k hd κ (empiricalWhitenedBound d k (C * x ^ p)) epsilon ≤
      empiricalQuarticPolylogConstant d k hd κ C * x ^ (8 * p) * epsilon ^ (1 / 18 : ℝ) := by
  let T := ((Fintype.card (ScalarCoordinate d k) : ℝ) + 1) * empiricalWhiteningFactor d k * C
  have hM : ((Fintype.card (ScalarCoordinate d k) : ℝ) + 1) * empiricalWhitenedBound d k (C * x ^ p) = T * x ^ p := by
    dsimp [T, empiricalWhitenedBound, empiricalWhiteningFactor]
    ring
  have hxp : 1 ≤ x ^ p := one_le_pow₀ hx
  have hbase : 1 + (T * x ^ p) ^ 2 ≤ (1 + T ^ 2) * (x ^ p) ^ 2 := by
    have hh := one_le_pow₀ hxp (n := 2)
    nlinarith
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + (T * x ^ p) ^ 2) hbase 4
  have hpower : (1 + (T * x ^ p) ^ 2) ^ 4 ≤ (1 + T ^ 2) ^ 4 * x ^ (8 * p) := by
    have heq : ((1 + T ^ 2) * (x ^ p) ^ 2) ^ 4 = (1 + T ^ 2) ^ 4 * x ^ (8 * p) := by
      rw [mul_pow, ← pow_mul, ← pow_mul]
      congr 2
      omega
    exact hpow.trans_eq heq
  have hfront : 0 ≤ (2 / Real.sqrt κ) *
      (NormalizedFiniteSignal.observationRemainderConstant (coloredObserved d k hd)) ^ (4 / 9 : ℝ) *
      epsilon ^ (1 / 18 : ℝ) := by
    exact mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (by
      exact (NormalizedFiniteSignal.observationRemainderConstant_pos (coloredObserved d k hd)).le) _))
      (Real.rpow_nonneg hepsilon _)
  have hh := mul_le_mul_of_nonneg_left hpower hfront
  unfold empiricalQuarticRate empiricalQuarticPolylogConstant
  rw [hM]
  convert hh using 1 <;> dsimp [T] <;> ring

end GeneralizedBulk.External.RegularSpectralData
