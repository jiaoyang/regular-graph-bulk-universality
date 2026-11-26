import GeneralizedBulk.Entropy.GaussianMixtureAbsoluteEntropy
import GeneralizedBulk.Entropy.ChannelRateTools

/-! Scalar polynomial growth of the proved absolute Gaussian-mixture
entropy bound. All constants are independent of the number of components. -/
noncomputable section
open Filter Asymptotics
open scoped Topology

namespace GeneralizedBulk.Entropy.ChannelRates

set_option maxHeartbeats 2000000 in
theorem uniformMixtureAbsoluteEntropyBound_bigO (I : Type*) [Fintype I]
    (κ U B : ℕ → ℝ) (c a : ℝ) (hc : 0 ≤ c) (ha : 0 ≤ a)
    (hκ : ∀ᶠ N in atTop,0 < κ N) (hU0 : ∀ᶠ N in atTop,0 ≤ U N)
    (hκInv : (fun N => (κ N)⁻¹) =O[atTop] fun N => (N : ℝ)^c)
    (hU : U =O[atTop] fun N => (N : ℝ)^c)
    (hB : B =O[atTop] fun N => (N : ℝ)^a)
    (hlog : (fun N => |Real.log (κ N)|+|Real.log (U N)|) =O[atTop]
      fun N => (N : ℝ)^(c+2*a)) :
    (fun N => uniformMixtureAbsoluteEntropyBound I (κ N) (U N) (B N)) =O[atTop]
      fun N => (N : ℝ)^(2*c+4*a) := by
  let m : ℝ := Fintype.card I
  have hB2 : (fun N => B N^2) =O[atTop] fun N => (N : ℝ)^(2*a) := by
    have h := nat_rpow_pow_bigO hB 2
    convert h using 1
    funext N
    congr 1
    ring
  have h1B2 := (nat_const_bigO_rpow 1 (2*a) (by positivity)).add hB2
  have hmain := nat_rpow_mul_bigO (hκInv.const_mul_left (m^4*m)) h1B2 (le_refl (c+2*a))
  have hR := ((hlog.const_mul_left (m/2)).add
    (nat_const_bigO_rpow (m/2*|Real.log (2*Real.pi)|) (c+2*a) (by positivity))).add hmain
  have hB2' := (hB2.const_mul_left 2).trans (nat_rpow_bigO_mono (2*a) (c+2*a) (by linarith))
  have hU' := (hU.const_mul_left (2*m^4)).trans (nat_rpow_bigO_mono c (c+2*a) (by linarith))
  have hS := ((nat_const_bigO_rpow 1 (c+2*a) (by positivity)).add hB2').add hU'
  have h := (nat_rpow_mul_bigO hR hS (show (c+2*a)+(c+2*a) ≤ 2*c+4*a by linarith)).const_mul_left (1+m^2)
  apply h.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [hκ,hU0] with N hκ hU0
  unfold uniformMixtureAbsoluteEntropyBound mixtureAbsoluteEntropyEnvelope
  have hsκ : 0 ≤ (Fintype.card I : ℝ)/(κ N) := div_nonneg (Nat.cast_nonneg _) hκ.le
  simp only [mul_pow,Real.sq_sqrt hsκ,Real.sq_sqrt hU0]
  dsimp only [m]
  ring

theorem polylog_bigO_nat_rpow (C : ℝ) (q : ℕ) (a : ℝ) (ha : 0 < a) :
    (fun N : ℕ => C*Real.log (N : ℝ)^q) =O[atTop] fun N => (N : ℝ)^a := by
  have h := ((isLittleO_log_rpow_rpow_atTop (q : ℝ) ha).comp_tendsto tendsto_natCast_atTop_atTop).isBigO
  simpa only [Function.comp_apply,Real.rpow_natCast] using h.const_mul_left C

set_option maxHeartbeats 1500000 in
theorem absolute_log_scaled_nat_rpow_bigO (C c a : ℝ) (hC : 0 < C) (ha : 0 < a) :
    (fun N : ℕ => |Real.log (C*(N : ℝ)^c)|) =O[atTop] fun N => (N : ℝ)^a := by
  have hlog := ((isLittleO_log_rpow_atTop ha).comp_tendsto tendsto_natCast_atTop_atTop).isBigO
  have hsum := (nat_const_bigO_rpow (Real.log C) a ha.le).add (hlog.const_mul_left c)
  have habs := hsum.norm_left
  apply habs.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : 0 < (N : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hN
  rw [Real.log_mul hC.ne' (Real.rpow_pos_of_pos hn c).ne',Real.log_rpow hn]
  simp only [Real.norm_eq_abs,Function.comp_apply]

set_option maxHeartbeats 2000000 in
theorem rawMixtureAbsoluteEntropyBound_bigO (I : Type*) [Fintype I]
    (κ₀ U₀ C : ℝ) (hκ₀ : 0 < κ₀) (hU₀ : 0 < U₀) (q : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    (fun N : ℕ => uniformMixtureAbsoluteEntropyBound I (κ₀*(N : ℝ)^(-c)) (U₀*(N : ℝ)^c)
      (C*Real.log (N : ℝ)^q)) =O[atTop] fun N => (N : ℝ)^(2*c+1/32) := by
  have hi : (fun N : ℕ => (κ₀*(N : ℝ)^(-c))⁻¹) =O[atTop] fun N => (N : ℝ)^c := by
    have h := (isBigO_refl (fun N : ℕ => (N : ℝ)^c) atTop).const_mul_left κ₀⁻¹
    convert h using 1
    funext N
    rw [mul_inv_rev,Real.rpow_neg (Nat.cast_nonneg N),inv_inv,mul_comm]
  have hU := (isBigO_refl (fun N : ℕ => (N : ℝ)^c) atTop).const_mul_left U₀
  have hlogs := (absolute_log_scaled_nat_rpow_bigO κ₀ (-c) (c+1/64) hκ₀ (by linarith)).add
    (absolute_log_scaled_nat_rpow_bigO U₀ c (c+1/64) hU₀ (by linarith))
  have h := uniformMixtureAbsoluteEntropyBound_bigO I _ _ _ c (1/128) hc (by norm_num)
    (by filter_upwards [eventually_ge_atTop 1] with N hN; exact mul_pos hκ₀ (Real.rpow_pos_of_pos (by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hN) _))
    (Filter.Eventually.of_forall (fun N => mul_nonneg hU₀.le (Real.rpow_nonneg (Nat.cast_nonneg N) c)))
    hi hU (polylog_bigO_nat_rpow C q (1/128) (by norm_num))
    (by convert hlogs using 1; funext N; congr 1; ring)
  convert h using 1
  funext N
  congr 1
  ring

end GeneralizedBulk.Entropy.ChannelRates
