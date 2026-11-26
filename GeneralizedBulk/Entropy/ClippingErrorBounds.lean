import GeneralizedBulk.Entropy.GaussianQuantizedEntropy
import GeneralizedBulk.Entropy.ChannelParameters

/-! Polynomial prefactors and actual Gaussian exponential decay for the
finite-to-countable clipping entropy error. -/
noncomputable section
open Filter Asymptotics
open scoped Topology NNReal

namespace GeneralizedBulk.Entropy.ChannelRates

def clippingPolynomialPrefactor (m : ℕ) (a H : ℝ) (c : ℝ≥0) : ℝ :=
  4+linearIntegerEntropyConstant m+(m : ℝ)^2*(2*(H^2+(c : ℝ))/a^2+2)

theorem clippingPolynomialPrefactor_nonneg (m : ℕ) (a H : ℝ) (c : ℝ≥0) :
    0 ≤ clippingPolynomialPrefactor m a H c := by
  unfold clippingPolynomialPrefactor
  exact add_nonneg (add_nonneg (by norm_num) (linearIntegerEntropyConstant_nonneg m)) (by positivity)

theorem gridClippingLossConstant_le_polynomial (m : ℕ) (a H : ℝ) (c : ℝ≥0) :
    gridClippingLossConstant m a (H^2+(c : ℝ)) ≤ clippingPolynomialPrefactor m a H c := by
  have hx : 0 ≤ (m : ℝ)^2*(2*(H^2+(c : ℝ))/a^2+2) := by positivity
  have hs := Real.sq_sqrt hx
  have hn := sq_nonneg (Real.sqrt ((m : ℝ)^2*(2*(H^2+(c : ℝ))/a^2+2))-1/2)
  unfold gridClippingLossConstant clippingPolynomialPrefactor
  nlinarith

theorem sqrt_exp_half (x : ℝ) : Real.sqrt (Real.exp x) = Real.exp (x/2) := by
  apply (Real.sqrt_eq_iff_eq_sq (Real.exp_pos x).le (Real.exp_pos (x/2)).le).mpr
  rw [← Real.exp_nat_mul]
  congr 1
  ring

theorem gaussianClippingError_le_polynomial_exp (m : ℕ) (a H : ℝ) (c : ℝ≥0) (K : ℕ) :
    gaussianClippingError m a H c K ≤ clippingPolynomialPrefactor m a H c*
      Real.sqrt (2*(m : ℝ))*Real.exp (-((K : ℝ)*a-H)^2/(4*(c : ℝ))) := by
  unfold gaussianClippingError
  rw [Real.sqrt_mul (by positivity : 0 ≤ 2*(m : ℝ)),sqrt_exp_half]
  have he : (-((K : ℝ)*a-H)^2/(2*(c : ℝ)))/2 = -((K : ℝ)*a-H)^2/(4*(c : ℝ)) := by ring
  rw [he]
  exact mul_le_mul_of_nonneg_right (gridClippingLossConstant_le_polynomial m a H c)
    (by positivity) |>.trans_eq (by ring)

set_option maxHeartbeats 1500000 in
theorem clippingPolynomialPrefactor_bigO (dim : ℕ → ℕ) (r : ℝ) (hr : 0 ≤ r)
    (hdim : (fun N => (dim N : ℝ)) =O[atTop] fun N => (N : ℝ)^r)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    (fun N => clippingPolynomialPrefactor (dim N) (channelMesh θ N) (channelNoiseBound θ N)
      (channelNoiseVariance θ N)) =O[atTop] fun N => (N : ℝ)^(2*r+2*channelNoiseExponent θ+2*θ) := by
  let c := channelNoiseExponent θ
  have hc : 0 ≤ c := by dsimp [c,channelNoiseExponent]; linarith
  have hH : channelNoiseBound θ =O[atTop] fun N : ℕ => (N : ℝ)^c := isBigO_refl _ _
  have hH2 := nat_rpow_pow_bigO hH 2
  have hsum : (fun N => channelNoiseBound θ N^2+(channelNoiseVariance θ N : ℝ)) =O[atTop]
      fun N => (N : ℝ)^(2*c) := by
    have hH2' : (fun N => channelNoiseBound θ N^2) =O[atTop] fun N => (N : ℝ)^(2*c) := by
      convert hH2 using 1
      funext N
      congr 1
      ring
    exact hH2'.add (hH.trans (nat_rpow_bigO_mono c (2*c) (by linarith)))
  have hinv : (fun N => (channelMesh θ N)^(-2 : ℤ)) =O[atTop] fun N : ℕ => (N : ℝ)^(2*θ) := by
    have h : (fun N : ℕ => (N : ℝ)^(2*θ)) =O[atTop] (fun N : ℕ => (N : ℝ)^(2*θ)) := isBigO_refl _ _
    convert h using 1
    funext N
    unfold channelMesh
    rw [← Real.rpow_intCast,← Real.rpow_mul (Nat.cast_nonneg N)]
    congr 1
    norm_num
    <;> ring
  have hfrac := (nat_rpow_mul_bigO hsum hinv (le_refl (2*c+2*θ))).const_mul_left 2
  have hfrac' : (fun N => 2*(channelNoiseBound θ N^2+(channelNoiseVariance θ N : ℝ))/(channelMesh θ N)^2) =O[atTop]
      fun N => (N : ℝ)^(2*c+2*θ) := by
    convert hfrac using 1
    funext N
    simp only [zpow_neg,zpow_ofNat,div_eq_mul_inv]
    ring
  have hinside := hfrac'.add (nat_const_bigO_rpow 2 (2*c+2*θ) (by positivity))
  have hdim2 := nat_rpow_pow_bigO hdim 2
  have hmain := nat_rpow_mul_bigO hdim2 hinside (show r*2+(2*c+2*θ) ≤ 2*r+2*c+2*θ by ring_nf; rfl)
  have hconst := nat_const_bigO_rpow 5 (2*r+2*c+2*θ) (by positivity)
  have hlinear := (hdim.const_mul_left (Real.log integerReferenceMass)).trans
    (nat_rpow_bigO_mono r (2*r+2*c+2*θ) (by nlinarith))
  have htotal := (hconst.add hlinear).add hmain
  convert htotal using 1
  funext N
  unfold clippingPolynomialPrefactor linearIntegerEntropyConstant
  ring

end GeneralizedBulk.Entropy.ChannelRates
