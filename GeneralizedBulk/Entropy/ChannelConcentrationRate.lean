import GeneralizedBulk.Entropy.ChannelParameters

/-! Polynomial rates for a conservative majorant of the actual edge-profile
and entropy-concentration errors. -/
noncomputable section
open Filter Asymptotics
open scoped Topology

namespace GeneralizedBulk.Entropy.ChannelRates

def scalarEdgeError (k : ℕ) (θ : ℝ) (N : ℕ) : ℝ :=
  64*(k+1)*((channelCutoff θ N : ℝ)+(2*(channelCutoff θ N : ℝ))^(2*k))*
    (N : ℝ)^(channelNoiseExponent θ/2-1/4)

def scalarEdgeEntropyError (k : ℕ) (θ : ℝ) (N : ℕ) : ℝ :=
  (3+(channelPalette k θ N : ℝ)^2)*Real.sqrt (scalarEdgeError k θ N/2)

theorem scalarEdgeError_bigO (k : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) :
    scalarEdgeError k θ =O[atTop] fun N => (N : ℝ)^(6*(k+1)*θ+channelNoiseExponent θ/2-1/4) := by
  have hK := channelCutoff_bigO θ hθ
  have hK' := hK.trans (nat_rpow_bigO_mono (3*θ) (6*(k+1)*θ) (by nlinarith [show (0 : ℝ) ≤ k by positivity]))
  have hp := nat_rpow_pow_bigO (hK.const_mul_left 2) (2*k)
  have hp' := hp.trans (nat_rpow_bigO_mono (3*θ*(2*k : ℕ)) (6*(k+1)*θ) (by push_cast; nlinarith [show (0 : ℝ) ≤ k by positivity]))
  have hs := (hK'.add hp').const_mul_left (64*(k+1) : ℝ)
  have hr : (fun N : ℕ => (N : ℝ)^(channelNoiseExponent θ/2-1/4)) =O[atTop]
      (fun N : ℕ => (N : ℝ)^(channelNoiseExponent θ/2-1/4)) := isBigO_refl _ _
  exact nat_rpow_mul_bigO hs hr (by ring_nf; exact le_refl _)

theorem scalarEdgeEntropyError_bigO (k : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) :
    scalarEdgeEntropyError k θ =O[atTop]
      fun N => (N : ℝ)^((9*k+3)*θ+channelNoiseExponent θ/4-1/8) := by
  have hq := nat_rpow_pow_bigO (channelPalette_bigO k θ hθ) 2
  have hc := nat_const_bigO_rpow 3 (6*k*θ) (by positivity)
  have hq' : (fun N => (channelPalette k θ N : ℝ)^2) =O[atTop] fun N => (N : ℝ)^(6*k*θ) := by
    convert hq using 1
    funext N
    congr 1
    ring
  have hsum := hc.add hq'
  have hroot := nat_rpow_sqrt_bigO ((scalarEdgeError_bigO k θ hθ).const_mul_left (1/2 : ℝ))
  have hroot' : (fun N => Real.sqrt (scalarEdgeError k θ N/2)) =O[atTop]
      fun N => (N : ℝ)^((6*(k+1)*θ+channelNoiseExponent θ/2-1/4)/2) := by
    simpa only [div_eq_mul_inv,mul_comm,one_mul] using hroot
  exact nat_rpow_mul_bigO hsum hroot' (by push_cast; ring_nf; exact le_refl _)

theorem scalarEdgeEntropyError_bigO_small (k : ℕ) (θ : ℝ) (hθ : 0 ≤ θ)
    (hsmall : 10*(k+1)*θ ≤ 1/16) :
    scalarEdgeEntropyError k θ =O[atTop] fun N => (N : ℝ)^(-θ) := by
  apply (scalarEdgeEntropyError_bigO k θ hθ).trans
  apply nat_rpow_bigO_mono
  unfold channelNoiseExponent
  push_cast
  nlinarith [show (0 : ℝ) ≤ k by positivity]

end GeneralizedBulk.Entropy.ChannelRates
