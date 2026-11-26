import GeneralizedBulk.Entropy.AbsoluteEntropyRate
import GeneralizedBulk.Entropy.FiniteHolder

/-! Polynomial numeric rates for the actual good/bad-root restoration and
the proved HY covariance-mixture stability errors. -/
noncomputable section
open Filter Asymptotics
open scoped Topology

namespace GeneralizedBulk.Entropy.ChannelRates

theorem binaryEntropy_mass_bigO (p : ℕ → ℝ)
    (hp : ∀ᶠ N in atTop,0 ≤ p N ∧ p N ≤ 1)
    (hpoly : p =O[atTop] fun N => (N : ℝ)^(-(1/2 : ℝ))) :
    (fun N => Real.binEntropy (p N)) =O[atTop] fun N => (N : ℝ)^(-(1/4 : ℝ)) := by
  have hs := (nat_rpow_sqrt_bigO hpoly).const_mul_left 3
  apply (show (fun N => Real.binEntropy (p N)) =O[atTop] (fun N => 3*Real.sqrt (p N)) from ?_).trans
    (by convert hs using 1; funext N; congr 1; norm_num)
  apply Eventually.isBigO
  filter_upwards [hp] with N hp
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.binEntropy_nonneg hp.1 hp.2)]
  exact Finite.binEntropy_le_three_sqrt (p N) hp.1 hp.2

def rawRestorationError (I : Type*) [Fintype I] (κ₀ U₀ κref Uref B c : ℝ) (q : ℕ)
    (p : ℕ → ℝ) (N : ℕ) : ℝ :=
  2*p N*(uniformMixtureAbsoluteEntropyBound I (κ₀*(N : ℝ)^(-c)) (U₀*(N : ℝ)^c) (B*Real.log (N : ℝ)^q)+
    uniformMixtureAbsoluteEntropyBound I κref Uref (B*Real.log (N : ℝ)^q))+2*Real.binEntropy (p N)

set_option maxHeartbeats 2000000 in
theorem rawRestorationError_bigO (I : Type*) [Fintype I]
    (κ₀ U₀ κref Uref B c : ℝ) (hκ₀ : 0 < κ₀) (hU₀ : 0 < U₀) (hκref : 0 < κref) (hUref : 0 < Uref)
    (hc : 0 ≤ c) (hcsmall : c ≤ 1/16) (q : ℕ) (p : ℕ → ℝ)
    (hp : ∀ᶠ N in atTop,0 ≤ p N ∧ p N ≤ 1)
    (hpoly : p =O[atTop] fun N => (N : ℝ)^(-(1/2 : ℝ))) :
    rawRestorationError I κ₀ U₀ κref Uref B c q p =O[atTop] fun N => (N : ℝ)^(-(1/4 : ℝ)) := by
  have hraw := rawMixtureAbsoluteEntropyBound_bigO I κ₀ U₀ B hκ₀ hU₀ q c hc
  have href : (fun N : ℕ => uniformMixtureAbsoluteEntropyBound I κref Uref (B*Real.log (N : ℝ)^q)) =O[atTop]
      fun N => (N : ℝ)^(1/32 : ℝ) := by
    simpa only [neg_zero,Real.rpow_zero,mul_one,zero_mul,mul_zero,zero_add] using
      rawMixtureAbsoluteEntropyBound_bigO I κref Uref B hκref hUref q 0 (by norm_num)
  have href' := href.trans (nat_rpow_bigO_mono (1/32) (2*c+1/32) (by linarith))
  have hprod := (nat_rpow_mul_bigO hpoly (hraw.add href')
    (show -(1/2 : ℝ)+(2*c+1/32) ≤ -(1/4 : ℝ) by linarith)).const_mul_left 2
  have hbin := (binaryEntropy_mass_bigO p hp hpoly).const_mul_left 2
  convert hprod.add hbin using 1
  funext N
  unfold rawRestorationError
  ring

def localCovarianceEntropyError (C B : ℝ) (q : ℕ) (localExponent height : ℝ) (N : ℕ) : ℝ :=
  C*(1+(B*Real.log (N : ℝ)^q)^2)*((N : ℝ)^(-localExponent)+Real.sqrt ((N : ℝ)^(-height)))

set_option maxHeartbeats 2000000 in
theorem localCovarianceEntropyError_bigO (C B : ℝ) (q : ℕ) (localExponent height : ℝ)
    (hlocal : 0 < localExponent) (hheight : 0 < height) :
    localCovarianceEntropyError C B q localExponent height =O[atTop]
      fun N => (N : ℝ)^(-min localExponent height/4) := by
  let β := min localExponent height
  have hβ : 0 < β := lt_min hlocal hheight
  have hB := polylog_bigO_nat_rpow B q (β/16) (by linarith)
  have hB2 := nat_rpow_pow_bigO hB 2
  have hcoef : (fun N : ℕ => 1+(B*Real.log (N : ℝ)^q)^2) =O[atTop] fun N => (N : ℝ)^(β/8) := by
    have hh := (nat_const_bigO_rpow 1 (β/8) (by linarith)).add
      (hB2.trans (nat_rpow_bigO_mono ((β/16)*2) (β/8) (by ring_nf; rfl)))
    exact hh
  have hl : (fun N : ℕ => (N : ℝ)^(-localExponent)) =O[atTop] fun N => (N : ℝ)^(-β/2) :=
    nat_rpow_bigO_mono _ _ (by have h := min_le_left localExponent height; dsimp [β]; linarith)
  have hh := nat_rpow_sqrt_bigO (isBigO_refl (fun N : ℕ => (N : ℝ)^(-height)) atTop)
  have hh' := hh.trans (nat_rpow_bigO_mono ((-height)/2) (-β/2) (by
    have h := min_le_right localExponent height
    dsimp [β]
    linarith))
  have hprod := (nat_rpow_mul_bigO hcoef (hl.add hh') (show β/8+(-β/2) ≤ -β/4 by linarith)).const_mul_left C
  convert hprod using 1
  funext N
  unfold localCovarianceEntropyError
  ring

end GeneralizedBulk.Entropy.ChannelRates
