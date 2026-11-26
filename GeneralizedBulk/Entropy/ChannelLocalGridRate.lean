import GeneralizedBulk.Entropy.ChannelParameters
import GeneralizedBulk.Entropy.GaussianQuantizedEntropy

/-! The local Gaussian grid error has a polynomially vanishing rate for
the actual chosen mesh and covariance floor. -/
noncomputable section
open Filter Asymptotics
open scoped Topology

namespace GeneralizedBulk.Entropy.ChannelRates

theorem gaussianLocalGridError_bigO (m : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) :
    (fun N => gaussianLocalGridError m (channelMesh θ N) (channelCovarianceFloor θ N)) =O[atTop]
      fun N => (N : ℝ)^(-θ) := by
  have hi : (fun N => (channelCovarianceFloor θ N)⁻¹) =O[atTop]
      fun N : ℕ => (N : ℝ)^(channelNoiseExponent θ) := by
    have h : (fun N : ℕ => (N : ℝ)^(channelNoiseExponent θ)) =O[atTop]
        (fun N : ℕ => (N : ℝ)^(channelNoiseExponent θ)) := isBigO_refl _ _
    convert h using 1
    funext N
    simp only [channelCovarianceFloor,Real.rpow_neg (Nat.cast_nonneg N),inv_inv]
  have hm : (fun N => channelMesh θ N^2) =O[atTop] fun N => (N : ℝ)^((-θ)*2) :=
    nat_rpow_pow_bigO (isBigO_refl (fun N : ℕ => (N : ℝ)^(-θ)) atTop) 2
  have hprod := nat_rpow_mul_bigO hi hm (show channelNoiseExponent θ+(-θ)*2 ≤ -θ by
    unfold channelNoiseExponent
    linarith)
  have h := hprod.const_mul_left (((2 : ℝ)^m/2)*(m : ℝ)*(m : ℝ))
  convert h using 1
  funext N
  unfold gaussianLocalGridError
  ring

end GeneralizedBulk.Entropy.ChannelRates
