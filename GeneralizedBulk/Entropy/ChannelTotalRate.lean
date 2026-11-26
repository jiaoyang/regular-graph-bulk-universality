import GeneralizedBulk.Entropy.ChannelClippingRate
import GeneralizedBulk.Entropy.ChannelLocalGridRate
import GeneralizedBulk.Entropy.ChannelConcentrationBound
import GeneralizedBulk.Entropy.ChannelCountingRate

/-! A genuine polynomial rate for the complete, explicit correlated graph
entropy error, including all clipping and configuration-counting costs. -/
noncomputable section
open Filter Asymptotics
open scoped Topology Classical NNReal Matrix.L2OpNorm

namespace GeneralizedBulk.Entropy.ChannelRates
open GeneralizedBulk.Graph.Configuration

def scalarChannelError (k d M : ℕ) (C θ : ℝ) (N : ℕ) : ℝ :=
  gaussianClippingError (k*N) (channelMesh θ N) (channelNoiseBound θ N) (channelNoiseVariance θ N) (channelCutoff θ N)/(N : ℝ)+
    gaussianLocalGridError (k*(d+1)) (channelMesh θ N) (channelCovarianceFloor θ N)+
    (d : ℝ)/2*gaussianClippingError (k*2) (channelMesh θ N) (channelNoiseBound θ N) (channelNoiseVariance θ N) (channelCutoff θ N)+
    (d : ℝ)/2*scalarEdgeEntropyError k θ N+scalarCountingError k d M C θ N

set_option maxHeartbeats 2000000 in
theorem actual_gaussianChannelError_le_scalar {k N d m : ℕ} {J : Type*} [Fintype J] [DecidableEq J]
    (A : Matrix (Fin k × Fin N) J ℝ) (θ : ℝ) (hN : 0 < N) (hNd : N*d = 2*m)
    (hA : ‖A*A.transpose‖ ≤ channelNoiseBound θ N) (C : ℝ) (M : ℕ) :
    gaussianChannelError (d := d) A (channelCovarianceFloor θ N) (channelPalette k θ N) m C ((N : ℝ)^(1/4 : ℝ)) M
      (channelNoiseBound θ N) (channelNoiseVariance θ N) (channelMesh θ N) (channelDither N)
      (channelCovarianceFloor θ N) (channelCutoff θ N)/(N : ℝ) ≤ scalarChannelError k d M C θ N := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hm : (m : ℝ)/(N : ℝ) = (d : ℝ)/2 := by
    apply (div_eq_div_iff (ne_of_gt hn) (by norm_num : (2 : ℝ) ≠ 0)).mpr
    have h : (N : ℝ)*(d : ℝ) = 2*(m : ℝ) := by exact_mod_cast hNd
    linarith
  let R := edgeProfileConcentrationError (B := Fin (2*channelCutoff θ N)) A
    (clippedGridBoundaries (channelMesh θ N) (channelCutoff θ N)) (channelDither N) (channelCovarianceFloor θ N)
  let q := channelPalette k θ N
  have hR : R ≤ scalarEdgeError k θ N := actual_edgeProfileError_le_scalar A θ hN hA
  have hroot := Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hR (by norm_num : (0 : ℝ) ≤ 2))
  have hcoef : 0 ≤ 3+Real.log (q*q : ℕ) := by linarith [Real.log_natCast_nonneg (q*q)]
  have hlog : 3+Real.log (q*q : ℕ) ≤ 3+(q : ℝ)^2 := by
    have h := Real.log_le_self (Nat.cast_nonneg (q*q))
    simpa only [Nat.cast_mul,pow_two] using add_le_add_left h 3
  have hEntropy : (3+Real.log (q*q : ℕ))*Real.sqrt (R/2) ≤ scalarEdgeEntropyError k θ N := by
    exact (mul_le_mul_of_nonneg_left hroot hcoef).trans
      (mul_le_mul_of_nonneg_right hlog (Real.sqrt_nonneg _))
  have hEntropy' := mul_le_mul_of_nonneg_left hEntropy (show 0 ≤ (d : ℝ)/2 by positivity)
  have hcount := actual_counting_error_le_scalar k d M C θ N m hNd
  have heq : gaussianChannelError (d := d) A (channelCovarianceFloor θ N) (channelPalette k θ N) m C ((N : ℝ)^(1/4 : ℝ)) M
      (channelNoiseBound θ N) (channelNoiseVariance θ N) (channelMesh θ N) (channelDither N)
      (channelCovarianceFloor θ N) (channelCutoff θ N)/(N : ℝ) =
      gaussianClippingError (k*N) (channelMesh θ N) (channelNoiseBound θ N) (channelNoiseVariance θ N) (channelCutoff θ N)/(N : ℝ)+
        gaussianLocalGridError (k*(d+1)) (channelMesh θ N) (channelCovarianceFloor θ N)+
        (d : ℝ)/2*gaussianClippingError (k*2) (channelMesh θ N) (channelNoiseBound θ N) (channelNoiseVariance θ N) (channelCutoff θ N)+
        (d : ℝ)/2*(3+Real.log (q*q : ℕ))*Real.sqrt (R/2)+
        channelCountingError N d (channelPalette k θ N) m C ((N : ℝ)^(1/4 : ℝ)) M/(N : ℝ) := by
    unfold gaussianChannelError
    calc
      _ = gaussianClippingError (k*N) (channelMesh θ N) (channelNoiseBound θ N) (channelNoiseVariance θ N) (channelCutoff θ N)/(N : ℝ)+
        gaussianLocalGridError (k*(d+1)) (channelMesh θ N) (channelCovarianceFloor θ N)+
        ((m : ℝ)/(N : ℝ))*gaussianClippingError (k*2) (channelMesh θ N) (channelNoiseBound θ N) (channelNoiseVariance θ N) (channelCutoff θ N)+
        ((m : ℝ)/(N : ℝ))*(3+Real.log (q*q : ℕ))*Real.sqrt (R/2)+
        channelCountingError N d (channelPalette k θ N) m C ((N : ℝ)^(1/4 : ℝ)) M/(N : ℝ) := by
          dsimp only [q,R]
          field_simp [ne_of_gt hn]
          <;> ring
      _ = _ := by rw [hm]
  rw [heq]
  unfold scalarChannelError
  nlinarith only [hcount,hEntropy']

set_option maxHeartbeats 1500000 in
theorem scalarChannelError_bigO (k d M : ℕ) (C θ : ℝ) (hθ : 0 < θ)
    (hsmall1 : 10*(k+1)*θ ≤ 1/16) (hsmall2 : 6*(k+1)*(d+1)*θ+2*θ ≤ 3/4) :
    scalarChannelError k d M C θ =O[atTop] fun N => (N : ℝ)^(-θ) := by
  have hdG : (fun N : ℕ => ((k*N : ℕ) : ℝ)) =O[atTop] fun N => (N : ℝ)^(1 : ℝ) := by
    simpa only [Nat.cast_mul,Real.rpow_one] using (isBigO_refl (fun N : ℕ => (N : ℝ)) atTop).const_mul_left (k : ℝ)
  have hclipG := channel_gaussianClippingError_bigO (fun N => k*N) 1 (by norm_num) hdG θ hθ (1-θ)
  have hinv : (fun N : ℕ => (N : ℝ)⁻¹) =O[atTop] fun N => (N : ℝ)^(-1 : ℝ) := by
    simpa only [Real.rpow_neg_one] using (isBigO_refl (fun N : ℕ => (N : ℝ)⁻¹) atTop)
  have hglobal := nat_rpow_mul_bigO hclipG hinv (show (1-θ)+(-1) ≤ -θ by linarith)
  have hlocal := gaussianLocalGridError_bigO (k*(d+1)) θ hθ.le
  have hdE : (fun _N : ℕ => ((k*2 : ℕ) : ℝ)) =O[atTop] fun N => (N : ℝ)^(0 : ℝ) := by
    simpa only [Real.rpow_zero] using (isBigO_const_const ((k*2 : ℕ) : ℝ) one_ne_zero atTop)
  have hedge := (channel_gaussianClippingError_bigO (fun _N => k*2) 0 (by norm_num) hdE θ hθ (-θ)).const_mul_left ((d : ℝ)/2)
  have hconc := (scalarEdgeEntropyError_bigO_small k θ hθ.le hsmall1).const_mul_left ((d : ℝ)/2)
  have hcount := scalarCountingError_bigO_small k d M C θ hθ hsmall2
  have h := (((hglobal.add hlocal).add hedge).add hconc).add hcount
  convert h using 1 <;> (funext N; unfold scalarChannelError; ring)

theorem channelTheta_small (k d : ℕ) :
    10*(k+1)*channelTheta k d ≤ 1/16 ∧
      6*(k+1)*(d+1)*channelTheta k d+2*channelTheta k d ≤ 3/4 := by
  have hk : (0 : ℝ) < (k : ℝ)+1 := by positivity
  have hd : (0 : ℝ) < (d : ℝ)+1 := by positivity
  have ht := channelTheta_pos k d
  have he : ((k : ℝ)+1)*((d : ℝ)+1)*channelTheta k d = 1/1000 := by
    unfold channelTheta
    field_simp
    <;> ring
  have h1 : channelTheta k d ≤ 1/1000 := by
    have hs : (1 : ℝ) ≤ ((k : ℝ)+1)*((d : ℝ)+1) := by nlinarith [mul_nonneg (show (0 : ℝ) ≤ k by positivity) (show (0 : ℝ) ≤ d by positivity)]
    have hh := mul_le_mul_of_nonneg_right hs ht.le
    nlinarith only [he,hh]
  have h2 : ((k : ℝ)+1)*channelTheta k d ≤ 1/1000 := by
    have hh := mul_nonneg (show (0 : ℝ) ≤ d by positivity) (show 0 ≤ ((k : ℝ)+1)*channelTheta k d by positivity)
    nlinarith only [he,hh]
  constructor <;> push_cast
  · nlinarith only [h2]
  · nlinarith only [he,h1]

theorem scalarChannelError_eventually_le_polynomial (k d M : ℕ) (C : ℝ) :
    ∀ᶠ N : ℕ in atTop,scalarChannelError k d M C (channelTheta k d) N ≤
      (N : ℝ)^(-channelTheta k d/2) := by
  have hsmall := channelTheta_small k d
  apply nat_rpow_bigO_eventually_le
    (scalarChannelError_bigO k d M C (channelTheta k d) (channelTheta_pos k d) hsmall.1 hsmall.2)
  linarith [channelTheta_pos k d]

end GeneralizedBulk.Entropy.ChannelRates
