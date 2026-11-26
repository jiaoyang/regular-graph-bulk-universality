import GeneralizedBulk.Entropy.LocalEntropyRates

/-! Uniform scalar envelopes for the actual good/bad mixture entropy
comparison. The bad mass may vary arbitrarily with the graph and signal. -/
noncomputable section
open Filter Asymptotics
open scoped Topology

namespace GeneralizedBulk.Entropy.ChannelRates

theorem uniformMixtureAbsoluteEntropyBound_nonneg (I : Type*) [Fintype I]
    (κ U B : ℝ) : 0 ≤ uniformMixtureAbsoluteEntropyBound I κ U B := by
  unfold uniformMixtureAbsoluteEntropyBound mixtureAbsoluteEntropyEnvelope
  positivity

def restorationEnvelope (I : Type*) [Fintype I]
    (κ₀ U₀ κref Uref B c : ℝ) (q : ℕ) (N : ℕ) : ℝ :=
  2*(N : ℝ)^(-(1/2 : ℝ))*(
    uniformMixtureAbsoluteEntropyBound I (κ₀*(N : ℝ)^(-c)) (U₀*(N : ℝ)^c) (B*Real.log (N : ℝ)^q)+
    uniformMixtureAbsoluteEntropyBound I κref Uref (B*Real.log (N : ℝ)^q))+
    6*(N : ℝ)^(-(1/4 : ℝ))

theorem restoration_le_envelope (I : Type*) [Fintype I]
    (κ₀ U₀ κref Uref B c : ℝ) (q : ℕ) (N : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpsmall : p ≤ (N : ℝ)^(-(1/2 : ℝ))) :
    2*p*(uniformMixtureAbsoluteEntropyBound I (κ₀*(N : ℝ)^(-c)) (U₀*(N : ℝ)^c) (B*Real.log (N : ℝ)^q)+
      uniformMixtureAbsoluteEntropyBound I κref Uref (B*Real.log (N : ℝ)^q))+2*Real.binEntropy p ≤
      restorationEnvelope I κ₀ U₀ κref Uref B c q N := by
  have hroot : Real.sqrt p ≤ (N : ℝ)^(-(1/4 : ℝ)) := by
    have h := Real.sqrt_le_sqrt hpsmall
    have hs : Real.sqrt ((N : ℝ)^(-(1/2 : ℝ))) = (N : ℝ)^(-(1/4 : ℝ)) := by
      rw [Real.sqrt_eq_rpow,← Real.rpow_mul (Nat.cast_nonneg N)]
      congr 1
      norm_num
    exact h.trans_eq hs
  have hb := Finite.binEntropy_le_three_sqrt p hp hp1
  have hn := add_nonneg
    (uniformMixtureAbsoluteEntropyBound_nonneg I (κ₀*(N : ℝ)^(-c)) (U₀*(N : ℝ)^c) (B*Real.log (N : ℝ)^q))
    (uniformMixtureAbsoluteEntropyBound_nonneg I κref Uref (B*Real.log (N : ℝ)^q))
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpsmall (by norm_num : (0 : ℝ) ≤ 2)) hn
  unfold restorationEnvelope
  linarith

set_option maxHeartbeats 2000000 in
theorem restorationEnvelope_bigO (I : Type*) [Fintype I]
    (κ₀ U₀ κref Uref B c : ℝ) (hκ₀ : 0 < κ₀) (hU₀ : 0 < U₀)
    (hκref : 0 < κref) (hUref : 0 < Uref) (hc : 0 ≤ c) (hcsmall : c ≤ 1/16) (q : ℕ) :
    restorationEnvelope I κ₀ U₀ κref Uref B c q =O[atTop]
      fun N => (N : ℝ)^(-(1/4 : ℝ)) := by
  have hraw := rawMixtureAbsoluteEntropyBound_bigO I κ₀ U₀ B hκ₀ hU₀ q c hc
  have href : (fun N : ℕ => uniformMixtureAbsoluteEntropyBound I κref Uref (B*Real.log (N : ℝ)^q)) =O[atTop]
      fun N => (N : ℝ)^(1/32 : ℝ) := by
    simpa only [neg_zero,Real.rpow_zero,mul_one,mul_zero,zero_add] using
      rawMixtureAbsoluteEntropyBound_bigO I κref Uref B hκref hUref q 0 (by norm_num)
  have href' := href.trans (nat_rpow_bigO_mono (1/32) (2*c+1/32) (by linarith))
  have hmain := (nat_rpow_mul_bigO
    (isBigO_refl (fun N : ℕ => (N : ℝ)^(-(1/2 : ℝ))) atTop)
    (hraw.add href') (show -(1/2 : ℝ)+(2*c+1/32) ≤ -(1/4 : ℝ) by linarith)).const_mul_left 2
  have hlast := (isBigO_refl (fun N : ℕ => (N : ℝ)^(-(1/4 : ℝ))) atTop).const_mul_left 6
  convert hmain.add hlast using 1
  funext N
  unfold restorationEnvelope
  ring

def localComparisonExponent (localExponent height : ℝ) : ℝ :=
  min (1/8 : ℝ) (min localExponent height/8)

theorem localComparisonExponent_pos (localExponent height : ℝ)
    (hl : 0 < localExponent) (hh : 0 < height) :
    0 < localComparisonExponent localExponent height :=
  lt_min (by norm_num) (div_pos (lt_min hl hh) (by norm_num))

set_option maxHeartbeats 2000000 in
theorem eventually_uniform_local_entropy_comparison (I : Type*) [Fintype I]
    (κ₀ U₀ κref Uref B c C localExponent : ℝ)
    (hκ₀ : 0 < κ₀) (hU₀ : 0 < U₀) (hκref : 0 < κref) (hUref : 0 < Uref)
    (hc : 0 < c) (hcsmall : c ≤ 1/16) (hl : 0 < localExponent) (q : ℕ) :
    ∀ᶠ N : ℕ in atTop,∀ p : ℝ,0 ≤ p → p ≤ 1 → p ≤ (N : ℝ)^(-(1/2 : ℝ)) →
      2*p*(uniformMixtureAbsoluteEntropyBound I (κ₀*(N : ℝ)^(-c)) (U₀*(N : ℝ)^c) (B*Real.log (N : ℝ)^q)+
        uniformMixtureAbsoluteEntropyBound I κref Uref (B*Real.log (N : ℝ)^q))+
        2*Real.binEntropy p+localCovarianceEntropyError C B q localExponent c N ≤
          (N : ℝ)^(-localComparisonExponent localExponent c) := by
  let β := min localExponent c
  have hβ : 0 < β := lt_min hl hc
  let e := min (-(1/4 : ℝ)) (-β/4)
  have hrest := (restorationEnvelope_bigO I κ₀ U₀ κref Uref B c hκ₀ hU₀ hκref hUref hc.le hcsmall q).trans
    (nat_rpow_bigO_mono _ (max (-(1/4 : ℝ)) (-β/4)) (le_max_left _ _))
  have hcov := (localCovarianceEntropyError_bigO C B q localExponent c hl hc).trans
    (nat_rpow_bigO_mono _ (max (-(1/4 : ℝ)) (-β/4)) (le_max_right _ _))
  have hstrict : max (-(1/4 : ℝ)) (-β/4) < -localComparisonExponent localExponent c := by
    unfold localComparisonExponent
    rw [max_lt_iff]
    have hγ₁ := min_le_left (1/8 : ℝ) (β/8)
    have hγ₂ := min_le_right (1/8 : ℝ) (β/8)
    dsimp [β] at *
    constructor <;> linarith
  have hevent := nat_rpow_bigO_eventually_le (hrest.add hcov) hstrict
  filter_upwards [hevent] with N hN p hp hp1 hpsmall
  exact (add_le_add_right (restoration_le_envelope I κ₀ U₀ κref Uref B c q N p hp hp1 hpsmall) _).trans hN

end GeneralizedBulk.Entropy.ChannelRates
