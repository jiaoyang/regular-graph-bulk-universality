import GeneralizedBulk.Entropy.ChannelRateTools

/-! Conservative explicit scalar parameter choices for the graph-channel
entropy construction. -/
noncomputable section
open Filter Asymptotics
open scoped Topology BigOperators NNReal

namespace GeneralizedBulk.Entropy.ChannelRates

def channelMesh (θ : ℝ) (N : ℕ) : ℝ := (N : ℝ)^(-θ)
def channelCutoff (θ : ℝ) (N : ℕ) : ℕ := Nat.ceil ((N : ℝ)^(3*θ))
def channelDither (N : ℕ) : ℝ := (N : ℝ)^(-(1/4 : ℝ))
def channelNoiseExponent (θ : ℝ) : ℝ := θ/8
def channelNoiseBound (θ : ℝ) (N : ℕ) : ℝ := (N : ℝ)^(channelNoiseExponent θ)
def channelNoiseVariance (θ : ℝ) (N : ℕ) : ℝ≥0 := ⟨channelNoiseBound θ N,Real.rpow_nonneg (Nat.cast_nonneg N) _⟩
def channelCovarianceFloor (θ : ℝ) (N : ℕ) : ℝ := (N : ℝ)^(-channelNoiseExponent θ)
def channelPalette (k : ℕ) (θ : ℝ) (N : ℕ) : ℕ := (2*channelCutoff θ N)^k
def channelTheta (k d : ℕ) : ℝ := 1/(1000*(k+1)*(d+1))

theorem channelTheta_pos (k d : ℕ) : 0 < channelTheta k d := by unfold channelTheta; positivity

theorem channelCutoff_bigO (θ : ℝ) (hθ : 0 ≤ θ) :
    (fun N => (channelCutoff θ N : ℝ)) =O[atTop] fun N => (N : ℝ)^(3*θ) :=
  ceil_nat_rpow_bigO _ (by linarith)

theorem channelPalette_bigO (k : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) :
    (fun N => (channelPalette k θ N : ℝ)) =O[atTop] fun N => (N : ℝ)^(3*(k : ℝ)*θ) := by
  have h := nat_rpow_pow_bigO ((channelCutoff_bigO θ hθ).const_mul_left 2) k
  convert h using 1
  · funext N
    simp only [channelPalette,Nat.cast_pow,Nat.cast_mul,Nat.cast_ofNat]
  · funext N
    congr 1
    ring

theorem channelCutoff_pos (θ : ℝ) (N : ℕ) (hN : 0 < N) : 0 < channelCutoff θ N := by
  apply Nat.ceil_pos.mpr
  exact Real.rpow_pos_of_pos (by exact_mod_cast hN) _

theorem channelMesh_pos (θ : ℝ) (N : ℕ) (hN : 0 < N) : 0 < channelMesh θ N :=
  Real.rpow_pos_of_pos (by exact_mod_cast hN) _

theorem channelCutoff_mesh_lower (θ : ℝ) (N : ℕ) (hN : 0 < N) :
    (N : ℝ)^(2*θ) ≤ (channelCutoff θ N : ℝ)*channelMesh θ N := by
  have h := mul_le_mul_of_nonneg_right (Nat.le_ceil ((N : ℝ)^(3*θ)))
    (Real.rpow_nonneg (Nat.cast_nonneg N) (-θ))
  unfold channelCutoff channelMesh
  have hnp : 0 < (N : ℝ) := by exact_mod_cast hN
  convert h using 1
  rw [← Real.rpow_add hnp]
  congr 1
  ring

theorem channel_mean_within_clipping (θ : ℝ) (hθ : 0 ≤ θ) (N : ℕ) (hN : 1 ≤ N) :
    channelNoiseBound θ N ≤ (channelCutoff θ N : ℝ)*channelMesh θ N := by
  apply (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
    (show channelNoiseExponent θ ≤ 2*θ by unfold channelNoiseExponent; linarith)).trans
  exact channelCutoff_mesh_lower θ N (lt_of_lt_of_le Nat.zero_lt_one hN)

end GeneralizedBulk.Entropy.ChannelRates
