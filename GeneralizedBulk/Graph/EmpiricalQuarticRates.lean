import GeneralizedBulk.Graph.HYEmpiricalFourthMoments
import GeneralizedBulk.Entropy.EntropyScaleDomains

/-! Numeric closure of the actual empirical fourth-chaos/Wick estimate.
At polynomial entropy error and polylogarithmic HY signal bounds, the
proved fourth-moment discrepancy is uniformly polynomially small. -/
noncomputable section
open Filter Asymptotics
open scoped Topology
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Entropy.Channel GeneralizedBulk.Entropy.Mehler
open GeneralizedBulk.Entropy.ChannelRates

set_option maxHeartbeats 2000000 in
theorem empiricalQuarticRate_bigO (d k : ℕ) (hd : 2 ≤ d)
    (κ C γ : ℝ) (q : ℕ) (B : ℕ → ℝ) (hγ : 0 < γ)
    (hB : B =O[atTop] fun N => C*Real.log (N : ℝ)^q) :
    (fun N : ℕ => empiricalQuarticRate d k hd κ (B N) ((N : ℝ)^(-γ))) =O[atTop]
      fun N => (N : ℝ)^(-γ/24) := by
  have hb := hB.trans (polylog_bigO_nat_rpow C q (γ/576) (by linarith))
  have hm := hb.const_mul_left ((Fintype.card (ScalarCoordinate d k) : ℝ)+1)
  have hm2 := nat_rpow_pow_bigO hm 2
  have hbase : (fun N : ℕ => 1+(((Fintype.card (ScalarCoordinate d k) : ℝ)+1)*B N)^2) =O[atTop]
      fun N => (N : ℝ)^(γ/288) := by
    have hh := (nat_const_bigO_rpow 1 (γ/288) (by linarith)).add
      (hm2.trans (nat_rpow_bigO_mono ((γ/576)*2) (γ/288) (by linarith)))
    exact hh
  have hfourth := nat_rpow_pow_bigO hbase 4
  have hepsilon : (fun N : ℕ => ((N : ℝ)^(-γ))^(1/18 : ℝ)) =O[atTop]
      fun N => (N : ℝ)^(-γ/18) := by
    have h := isBigO_refl (fun N : ℕ => (N : ℝ)^(-γ/18)) atTop
    apply h.congr_left
    intro N
    rw [← Real.rpow_mul (Nat.cast_nonneg N)]
    congr 1
    ring
  have h := (nat_rpow_mul_bigO hfourth hepsilon
    (show (γ/288)*4+(-γ/18) ≤ -γ/24 by linarith)).const_mul_left
    ((2/Real.sqrt κ)*(NormalizedFiniteSignal.observationRemainderConstant (coloredObserved d k hd))^(4/9 : ℝ))
  convert h using 1
  funext N
  unfold empiricalQuarticRate
  ring

theorem eventually_empiricalQuarticRate_polynomial (d k : ℕ) (hd : 2 ≤ d)
    (κ C γ : ℝ) (q : ℕ) (B : ℕ → ℝ) (hγ : 0 < γ)
    (hB : B =O[atTop] fun N => C*Real.log (N : ℝ)^q) :
    ∀ᶠ N : ℕ in atTop,64*empiricalQuarticRate d k hd κ (B N) ((N : ℝ)^(-γ)) ≤
      (N : ℝ)^(-γ/36) := by
  apply nat_rpow_bigO_eventually_le ((empiricalQuarticRate_bigO d k hd κ C γ q B hγ hB).const_mul_left 64)
  linarith

theorem empiricalWhitenedBound_polylog_bigO (d k : ℕ) (C : ℝ) (q : ℕ) :
    (fun N : ℕ => empiricalWhitenedBound d k (C*Real.log (N : ℝ)^q)) =O[atTop]
      fun N => (((Fintype.card (ScalarCoordinate d k) : ℝ)*((k : ℝ)*d*((d : ℝ)+1)))*C)*Real.log (N : ℝ)^q := by
  apply IsBigO.of_bound 1
  exact Eventually.of_forall (fun N => by
    have heq : empiricalWhitenedBound d k (C*Real.log (N : ℝ)^q) =
        (((Fintype.card (ScalarCoordinate d k) : ℝ)*((k : ℝ)*d*((d : ℝ)+1)))*C)*Real.log (N : ℝ)^q := by
      unfold empiricalWhitenedBound
      ring
    rw [heq,one_mul])

end GeneralizedBulk.External.RegularSpectralData
