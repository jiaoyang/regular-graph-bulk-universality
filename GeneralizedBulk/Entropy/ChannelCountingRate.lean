import GeneralizedBulk.Entropy.ChannelParameters
import GeneralizedBulk.Graph.GaussianChannelEntropy

/-! Polynomial control of all configuration-counting costs for the growing
actual palette. -/
noncomputable section
open Filter Asymptotics
open scoped Topology

namespace GeneralizedBulk.Entropy.ChannelRates
open GeneralizedBulk.Graph.Configuration

theorem log_linear_nat_bigO (d : ℕ) (θ : ℝ) (hθ : 0 < θ) :
    (fun N : ℕ => Real.log ((N*d+1 : ℕ) : ℝ)) =O[atTop] fun N => (N : ℝ)^θ := by
  have hl := ((isLittleO_log_rpow_atTop hθ).comp_tendsto tendsto_natCast_atTop_atTop).isBigO
  have hc := nat_const_bigO_rpow (Real.log (d+1 : ℕ)) θ hθ.le
  apply (show (fun N : ℕ => Real.log ((N*d+1 : ℕ) : ℝ)) =O[atTop]
      (fun N : ℕ => Real.log (d+1 : ℕ)+Real.log (N : ℝ)) from ?_).trans (hc.add hl)
  apply Eventually.isBigO
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.log_natCast_nonneg _)]
  have hnp : 0 < (N : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hN
  have hnr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have harg : ((N*d+1 : ℕ) : ℝ) ≤ ((d+1 : ℕ) : ℝ)*(N : ℝ) := by push_cast; nlinarith
  have h := Real.log_le_log (show (0 : ℝ) < ((N*d+1 : ℕ) : ℝ) by positivity) harg
  rwa [Real.log_mul (by positivity : ((d+1 : ℕ) : ℝ) ≠ 0) (ne_of_gt hnp)] at h

def scalarCountingError (k d M : ℕ) (C θ : ℝ) (N : ℕ) : ℝ :=
  (((channelPalette k θ N : ℝ)^2/2+2)*(|C|+Real.log ((N*d+1 : ℕ) : ℝ))+
    3*(channelPalette k θ N : ℝ)^(d+1)*Real.log (N+1 : ℕ)+(N : ℝ)^(1/4 : ℝ)+
    (2*M+1 : ℕ)*Real.log ((N*d+1 : ℕ) : ℝ))/(N : ℝ)

set_option maxHeartbeats 2000000 in
theorem scalarCountingError_bigO (k d M : ℕ) (C θ : ℝ) (hθ : 0 < θ) :
    scalarCountingError k d M C θ =O[atTop]
      fun N => (N : ℝ)^(6*(k+1)*(d+1)*θ+θ-3/4) := by
  let L : ℝ := 6*(k+1)*(d+1)*θ
  let E : ℝ := L+θ+1/4
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hq := channelPalette_bigO k θ hθ.le
  have hq2 := nat_rpow_pow_bigO hq 2
  have hq2' : (fun N => (channelPalette k θ N : ℝ)^2) =O[atTop] fun N => (N : ℝ)^L := by
    apply hq2.trans
    apply nat_rpow_bigO_mono
    dsimp [L]
    push_cast
    have hk : (k : ℝ) ≤ ((k : ℝ)+1)*((d : ℝ)+1) := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ k by positivity) (show (0 : ℝ) ≤ d by positivity)]
    have hh := mul_le_mul_of_nonneg_left hk (show 0 ≤ 6*θ by positivity)
    nlinarith only [hh]
  have hqp := nat_rpow_pow_bigO hq (d+1)
  have hqp' : (fun N => (channelPalette k θ N : ℝ)^(d+1)) =O[atTop] fun N => (N : ℝ)^L := by
    apply hqp.trans
    apply nat_rpow_bigO_mono
    dsimp [L]
    push_cast
    have hk : 3*(k : ℝ) ≤ 6*((k : ℝ)+1) := by nlinarith [show (0 : ℝ) ≤ k by positivity]
    have hh := mul_le_mul_of_nonneg_right hk (show 0 ≤ ((d : ℝ)+1)*θ by positivity)
    nlinarith only [hh]
  have hcoef := ((hq2'.const_mul_left (1/2 : ℝ)).add (nat_const_bigO_rpow 2 L hL))
  have hlog := log_linear_nat_bigO d θ hθ
  have hlocal := (nat_const_bigO_rpow |C| θ hθ.le).add hlog
  have hfirst := nat_rpow_mul_bigO hcoef hlocal (le_refl (L+θ))
  have hlog1 : (fun N : ℕ => Real.log (N+1 : ℕ)) =O[atTop] fun N => (N : ℝ)^θ := by
    simpa only [Nat.mul_one] using log_linear_nat_bigO 1 θ hθ
  have hsecond := (nat_rpow_mul_bigO hqp' hlog1 (le_refl (L+θ))).const_mul_left 3
  have hrepair := (hlog.const_mul_left ((2*M+1 : ℕ) : ℝ)).trans
    (nat_rpow_bigO_mono θ E (by dsimp [E]; linarith))
  have ht : (fun N : ℕ => (N : ℝ)^(1/4 : ℝ)) =O[atTop] fun N => (N : ℝ)^E :=
    nat_rpow_bigO_mono _ _ (by dsimp [E]; linarith)
  have hfirst' := hfirst.trans (nat_rpow_bigO_mono (L+θ) E (by dsimp [E]; linarith))
  have hsecond' := hsecond.trans (nat_rpow_bigO_mono (L+θ) E (by dsimp [E]; linarith))
  have hsum := ((hfirst'.add hsecond').add ht).add hrepair
  have hinv : (fun N : ℕ => (N : ℝ)⁻¹) =O[atTop] fun N => (N : ℝ)^(-1 : ℝ) := by
    simpa only [Real.rpow_neg_one] using (isBigO_refl (fun N : ℕ => (N : ℝ)⁻¹) atTop)
  have hprod := nat_rpow_mul_bigO hsum hinv (show E+(-1) ≤ L+θ-3/4 by dsimp [E]; linarith)
  convert hprod using 1
  funext N
  unfold scalarCountingError
  ring

theorem scalarCountingError_bigO_small (k d M : ℕ) (C θ : ℝ) (hθ : 0 < θ)
    (hsmall : 6*(k+1)*(d+1)*θ+2*θ ≤ 3/4) :
    scalarCountingError k d M C θ =O[atTop] fun N => (N : ℝ)^(-θ) := by
  exact (scalarCountingError_bigO k d M C θ hθ).trans (nat_rpow_bigO_mono _ _ (by linarith))

theorem actual_counting_error_le_scalar (k d M : ℕ) (C θ : ℝ) (N m : ℕ) (hNd : N*d = 2*m) :
    channelCountingError N d (channelPalette k θ N) m C ((N : ℝ)^(1/4 : ℝ)) M/(N : ℝ) ≤
      scalarCountingError k d M C θ N := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  unfold channelCountingError
  rw [show 2*(m : ℝ)+1 = ((N*d+1 : ℕ) : ℝ) from by exact_mod_cast congrArg Nat.succ hNd.symm]
  have hC := mul_le_mul_of_nonneg_left (le_abs_self C) (show 0 ≤ (channelPalette k θ N : ℝ)^2/2+2 by positivity)
  unfold paletteLog simplicityCost
  push_cast
  nlinarith only [hC]

end GeneralizedBulk.Entropy.ChannelRates
