import GeneralizedBulk.Entropy.ClippingErrorBounds

/-! The actual Gaussian clipping entropy error decays faster than every
polynomial under the explicit conservative channel parameters. -/
noncomputable section
open Filter Asymptotics
open scoped Topology NNReal

namespace GeneralizedBulk.Entropy.ChannelRates

set_option maxHeartbeats 1500000 in
theorem channel_clipping_exponent_lower (θ : ℝ) (hθ : 0 < θ) :
    ∀ᶠ N : ℕ in atTop,(1/16 : ℝ)*(N : ℝ)^(4*θ-channelNoiseExponent θ) ≤
      ((channelCutoff θ N : ℝ)*channelMesh θ N-channelNoiseBound θ N)^2/
        (4*(channelNoiseVariance θ N : ℝ)) := by
  have ha : 0 < 2*θ-channelNoiseExponent θ := by unfold channelNoiseExponent; linarith
  have hp := ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  filter_upwards [hp,eventually_ge_atTop 1] with N hp hN
  have hnp : 0 < (N : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hN
  have hH : 0 < channelNoiseBound θ N := Real.rpow_pos_of_pos hnp _
  have hprod : (N : ℝ)^(2*θ-channelNoiseExponent θ)*channelNoiseBound θ N = (N : ℝ)^(2*θ) := by
    unfold channelNoiseBound
    rw [← Real.rpow_add hnp]
    congr 1
    ring
  have hsmall : 2*channelNoiseBound θ N ≤ (N : ℝ)^(2*θ) := by
    rw [← hprod]
    exact mul_le_mul_of_nonneg_right hp hH.le
  have hK := channelCutoff_mesh_lower θ N (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hgap : (1/2 : ℝ)*(N : ℝ)^(2*θ) ≤
      (channelCutoff θ N : ℝ)*channelMesh θ N-channelNoiseBound θ N := by linarith
  have hbase : 0 ≤ (1/2 : ℝ)*(N : ℝ)^(2*θ) := by positivity
  have hsq := (sq_le_sq₀ hbase (hbase.trans hgap)).mpr hgap
  have hdiv := div_le_div_of_nonneg_right hsq (show 0 ≤ 4*(channelNoiseVariance θ N : ℝ) by positivity)
  convert hdiv using 1
  have hpow : ((N : ℝ)^(2*θ))^2 = (N : ℝ)^(4*θ) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hnp.le]
    congr 1
    norm_num
    <;> ring
  change (1/16 : ℝ)*(N : ℝ)^(4*θ-channelNoiseExponent θ) =
    ((1/2 : ℝ)*(N : ℝ)^(2*θ))^2/(4*(N : ℝ)^(channelNoiseExponent θ))
  rw [mul_pow,hpow,Real.rpow_sub hnp]
  ring

set_option maxHeartbeats 2000000 in
theorem channel_gaussianClippingError_bigO (dim : ℕ → ℕ) (r : ℝ) (hr : 0 ≤ r)
    (hdim : (fun N => (dim N : ℝ)) =O[atTop] fun N => (N : ℝ)^r)
    (θ : ℝ) (hθ : 0 < θ) (s : ℝ) :
    (fun N => gaussianClippingError (dim N) (channelMesh θ N) (channelNoiseBound θ N)
      (channelNoiseVariance θ N) (channelCutoff θ N)) =O[atTop] fun N => (N : ℝ)^s := by
  let p := 2*r+2*channelNoiseExponent θ+2*θ+r/2
  let α := 4*θ-channelNoiseExponent θ
  have hα : 0 < α := by dsimp [α,channelNoiseExponent]; linarith
  have hP := nat_rpow_mul_bigO (clippingPolynomialPrefactor_bigO dim r hr hdim θ hθ.le)
    (nat_rpow_sqrt_bigO (hdim.const_mul_left 2)) (show 2*r+2*channelNoiseExponent θ+2*θ+r/2 ≤ p by rfl)
  have he := (stretched_exp_littleO_nat_rpow α (1/16) (s-p) hα (by norm_num)).isBigO
  have hprod := nat_rpow_mul_bigO hP he (show p+(s-p) ≤ s by linarith)
  apply (show (fun N => gaussianClippingError (dim N) (channelMesh θ N) (channelNoiseBound θ N)
      (channelNoiseVariance θ N) (channelCutoff θ N)) =O[atTop]
      (fun N => clippingPolynomialPrefactor (dim N) (channelMesh θ N) (channelNoiseBound θ N) (channelNoiseVariance θ N)*
        Real.sqrt (2*(dim N : ℝ))*Real.exp (-(1/16 : ℝ)*(N : ℝ)^α)) from ?_).trans hprod
  apply Eventually.isBigO
  filter_upwards [channel_clipping_exponent_lower θ hθ] with N htail
  rw [Real.norm_eq_abs,abs_of_nonneg (gaussianClippingError_nonneg _ _ _ _ _)]
  apply (gaussianClippingError_le_polynomial_exp _ _ _ _ _).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (clippingPolynomialPrefactor_nonneg _ _ _ _) (Real.sqrt_nonneg _))
  apply Real.exp_le_exp.mpr
  change (1/16 : ℝ)*(N : ℝ)^α ≤ _ at htail
  simpa only [neg_div,neg_mul] using neg_le_neg htail

end GeneralizedBulk.Entropy.ChannelRates
