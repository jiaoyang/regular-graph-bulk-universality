import GeneralizedBulk.Entropy.ChannelConcentrationRate
import GeneralizedBulk.Entropy.CorrelatedColoringEntropy
import GeneralizedBulk.Entropy.ClippedQuantizer

/-! The polynomial concentration majorant dominates the actual Gaussian
edge-profile error for the chosen mesh, cutoff, and dither parameters. -/
noncomputable section
open scoped BigOperators Classical Matrix.L2OpNorm

namespace GeneralizedBulk.Entropy.ChannelRates
open GeneralizedBulk.Gaussian

theorem channel_dither_denominator (N : ℕ) (hN : 0 < N) :
    (N : ℝ)*channelDither N^2 = (N : ℝ)^(1/2 : ℝ) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  calc
    _ = (N : ℝ)^(1 : ℝ)*(N : ℝ)^((-(1/4 : ℝ))*2) := by
      rw [Real.rpow_one]
      unfold channelDither
      rw [← Real.rpow_natCast,← Real.rpow_mul hn.le]
      norm_num
    _ = _ := by rw [← Real.rpow_add hn]; congr 1 <;> norm_num

theorem channel_variance_sqrt (k : ℕ) (θ : ℝ) (N : ℕ) (hN : 0 < N) :
    Real.sqrt (channelNoiseBound θ N*((k : ℝ)/((N : ℝ)*channelDither N^2))) =
      Real.sqrt (k : ℝ)*(N : ℝ)^(channelNoiseExponent θ/2-1/4) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hc : 0 ≤ channelNoiseBound θ N*((k : ℝ)/((N : ℝ)*channelDither N^2)) := by
    unfold channelNoiseBound
    positivity
  apply (Real.sqrt_eq_iff_eq_sq hc (by positivity)).mpr
  have hWsq : ((N : ℝ)^(channelNoiseExponent θ/2-1/4))^2 =
      (N : ℝ)^(channelNoiseExponent θ-1/2) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hn.le]
    congr 1
    ring
  rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg k),hWsq,channel_dither_denominator N hN]
  unfold channelNoiseBound
  rw [div_eq_mul_inv,← Real.rpow_neg hn.le]
  calc
    _ = (k : ℝ)*((N : ℝ)^(channelNoiseExponent θ)*(N : ℝ)^(-(1/2 : ℝ))) := by ring
    _ = _ := by rw [← Real.rpow_add hn]; congr 2 <;> ring

theorem channel_transition_denominator_lower (θ : ℝ) (N : ℕ) :
    (N : ℝ)^(-channelNoiseExponent θ/2) ≤
      Real.sqrt (2*Real.pi*channelCovarianceFloor θ N) := by
  apply Real.le_sqrt_of_sq_le
  have hp : ((N : ℝ)^(-channelNoiseExponent θ/2))^2 = channelCovarianceFloor θ N := by
    unfold channelCovarianceFloor
    rw [← Real.rpow_natCast,← Real.rpow_mul (Nat.cast_nonneg N)]
    congr 1
    ring
  rw [hp]
  have hn : 0 ≤ channelCovarianceFloor θ N := Real.rpow_nonneg (Nat.cast_nonneg N) _
  nlinarith [Real.pi_gt_three]

set_option maxHeartbeats 2000000 in
theorem actual_edgeProfileError_le_scalar {k N : ℕ} {J : Type*} [Fintype J] [DecidableEq J]
    (A : Matrix (Fin k × Fin N) J ℝ) (θ : ℝ) (Npos : 0 < N)
    (hA : ‖A*A.transpose‖ ≤ channelNoiseBound θ N) :
    edgeProfileConcentrationError (B := Fin (2*channelCutoff θ N)) A
      (clippedGridBoundaries (channelMesh θ N) (channelCutoff θ N))
        (channelDither N) (channelCovarianceFloor θ N) ≤ scalarEdgeError k θ N := by
  let K := channelCutoff θ N
  let P : ℝ := (2*(K : ℝ))^(2*k)
  let W : ℝ := (N : ℝ)^(channelNoiseExponent θ/2-1/4)
  have hn : 0 < (N : ℝ) := by exact_mod_cast Npos
  have hD : 0 < channelDither N := Real.rpow_pos_of_pos hn _
  have hB : 0 < (N : ℝ)^(-channelNoiseExponent θ/2) := Real.rpow_pos_of_pos hn _
  have hden := channel_transition_denominator_lower θ N
  have hcard : ((clippedGridBoundaries (channelMesh θ N) K).card : ℝ) ≤ 2*(K : ℝ) := by
    exact_mod_cast clippedGridBoundaries_card_le (channelMesh θ N) K
  have hfirst : 32*k*((clippedGridBoundaries (channelMesh θ N) K).card : ℝ)*channelDither N/
      Real.sqrt (2*Real.pi*channelCovarianceFloor θ N) ≤ 64*k*(K : ℝ)*W := by
    calc
      _ ≤ (64*k*(K : ℝ)*channelDither N)/Real.sqrt (2*Real.pi*channelCovarianceFloor θ N) := by
        apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
        nlinarith [mul_le_mul_of_nonneg_left hcard (show 0 ≤ 32*(k : ℝ)*channelDither N by positivity)]
      _ ≤ (64*k*(K : ℝ)*channelDither N)/(N : ℝ)^(-channelNoiseExponent θ/2) :=
        div_le_div_of_nonneg_left (by positivity) hB hden
      _ = _ := by
        have hinv : ((N : ℝ)^(-channelNoiseExponent θ/2))⁻¹ = (N : ℝ)^(channelNoiseExponent θ/2) := by
          rw [show -channelNoiseExponent θ/2 = -(channelNoiseExponent θ/2) from by ring,
            Real.rpow_neg hn.le,inv_inv]
        unfold W channelDither
        rw [div_eq_mul_inv,hinv]
        rw [mul_assoc (64*k*(K : ℝ)),← Real.rpow_add hn]
        congr 2
        ring
  have hroot := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hA
    (show 0 ≤ (k : ℝ)/((N : ℝ)*channelDither N^2) by positivity))
  rw [channel_variance_sqrt k θ N Npos] at hroot
  have hsecond := mul_le_mul_of_nonneg_left hroot (show 0 ≤ P by positivity)
  change P*Real.sqrt (‖A*A.transpose‖*((k : ℝ)/((N : ℝ)*channelDither N^2))) ≤
    P*(Real.sqrt (k : ℝ)*W) at hsecond
  have hsqrt : Real.sqrt (k : ℝ) ≤ (k : ℝ)+1 := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg k),Real.sqrt_nonneg (k : ℝ),sq_nonneg (Real.sqrt (k : ℝ)-1/2)]
  have hcoeff : 64*k*(K : ℝ)+P*Real.sqrt (k : ℝ) ≤ 64*(k+1)*((K : ℝ)+P) := by
    have hh := mul_le_mul_of_nonneg_left hsqrt (show 0 ≤ P by positivity)
    nlinarith [show (0 : ℝ) ≤ K by positivity,show 0 ≤ P by positivity,show (0 : ℝ) ≤ k by positivity]
  have hh := mul_le_mul_of_nonneg_right hcoeff (show 0 ≤ W by positivity)
  unfold edgeProfileConcentrationError scalarEdgeError
  simp only [Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]
  change 32*k*((clippedGridBoundaries (channelMesh θ N) K).card : ℝ)*channelDither N/
    Real.sqrt (2*Real.pi*channelCovarianceFloor θ N)+
    P*Real.sqrt (‖A*A.transpose‖*((k : ℝ)/((N : ℝ)*channelDither N^2))) ≤ 64*(k+1)*((K : ℝ)+P)*W
  nlinarith only [hfirst,hsecond,hh]

end GeneralizedBulk.Entropy.ChannelRates
