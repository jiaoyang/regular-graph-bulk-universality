import GeneralizedBulk.Entropy.ChannelTotalRate
import GeneralizedBulk.Graph.GaussianChannelNormalized
import GeneralizedBulk.Entropy.AffineEntropyFormula

/-! The actual correlated graph Gaussian channel has a polynomial entropy
error on one common good graph event, uniformly over every bounded signal
and every scalar contraction of that signal. -/
noncomputable section
open Filter Asymptotics
open scoped Topology Classical BigOperators Matrix.L2OpNorm

namespace GeneralizedBulk.Graph.Configuration
open Entropy Entropy.ChannelRates GeneralizedBulk.Gaussian

universe u

theorem eventually_gaussianChannelError_polynomial (k d M : ℕ) (C : ℝ) :
    ∀ᶠ N : ℕ in atTop,∀ {J : Type u} [Fintype J] [DecidableEq J] (m : ℕ)
      (A : Matrix (Fin k × Fin N) J ℝ) (hNd : N*d = 2*m)
      (hA : ‖A*A.transpose‖ ≤ channelNoiseBound (channelTheta k d) N),
      gaussianChannelError (d := d) A (channelCovarianceFloor (channelTheta k d) N)
        (channelPalette k (channelTheta k d) N) m C ((N : ℝ)^(1/4 : ℝ)) M
        (channelNoiseBound (channelTheta k d) N) (channelNoiseVariance (channelTheta k d) N)
        (channelMesh (channelTheta k d) N) (channelDither N) (channelCovarianceFloor (channelTheta k d) N)
        (channelCutoff (channelTheta k d) N)/(N : ℝ) ≤ (N : ℝ)^(-channelTheta k d/2) := by
  filter_upwards [scalarChannelError_eventually_le_polynomial k d M C,eventually_ge_atTop 1] with N hbound hN
  intro J _ _ m A hNd hA
  exact (actual_gaussianChannelError_le_scalar A (channelTheta k d)
    (lt_of_lt_of_le Nat.zero_lt_one hN) hNd hA C M).trans hbound

theorem coordinateVariance_le_covariance_norm {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Matrix I J ℝ) (i : I) :
    (coordinateVariance A i : ℝ) ≤ ‖A*A.transpose‖ := by
  have h := Hermite.matrix_gradient_energy_le_covariance A (Pi.single i 1)
  simpa [coordinateVariance,Pi.single_apply] using h

theorem covariance_lower_le_coordinateVariance {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix I J ℝ) (lo : ℝ)
    (hbound : ∀ x : I → ℝ,lo*(∑ i,x i^2) ≤ dotProduct x ((A*A.transpose).mulVec x)) (i : I) :
    lo ≤ coordinateVariance A i := by
  have h := hbound (Pi.single i 1)
  rw [coordinateVariance_eq_covariance_diagonal]
  simpa [dotProduct,Matrix.mulVec,Pi.single_apply] using h

theorem wholeGaussianDensity_entropy_mean_independent {k N : ℕ} {J : Type*} [Fintype J]
    (A : Matrix (Fin k × Fin N) J ℝ) (lo : ℝ) (hlo : 0 < lo)
    (hbound : ∀ x : Fin k × Fin N → ℝ,lo*(∑ i,x i^2) ≤ dotProduct x ((A*A.transpose).mulVec x))
    (mean mean' : Fin k × Fin N → ℝ) :
    differentialEntropy (wholeGaussianDensity A lo hlo hbound mean) =
      differentialEntropy (wholeGaussianDensity A lo hlo hbound mean') :=
  differentialEntropy_affineGaussianPDF_mean_independent _ _ _ (wholeNoiseFactor_det_ne_zero A lo hlo hbound)

set_option maxHeartbeats 2000000 in
theorem eventually_correlated_gaussian_channel_polynomial (k d M : ℕ) (C : ℝ) :
    ∀ᶠ N : ℕ in atTop,∀ {J : Type u} [Fintype J] [DecidableEq J] (m : ℕ)
      (A : Matrix (Fin k × Fin N) J ℝ) (G : RegularGraph N d) (hd : 0 < d) (hNd : N*d = 2*m)
      (hA : ‖A*A.transpose‖ ≤ channelNoiseBound (channelTheta k d) N)
      (hlo : 0 < channelCovarianceFloor (channelTheta k d) N)
      (hlower : ∀ x : Fin k × Fin N → ℝ,channelCovarianceFloor (channelTheta k d) N*(∑ i,x i^2) ≤
        dotProduct x ((A*A.transpose).mulVec x))
      (hG : GraphProfileGood (q := channelPalette k (channelTheta k d) N) (m := m) C ((N : ℝ)^(1/4 : ℝ)) M G)
      (e : (Fin k → Fin (2*channelCutoff (channelTheta k d) N)) ≃ Fin (channelPalette k (channelTheta k d) N))
      (mean : Fin k × Fin N → ℝ) (hmean : ∀ i,|mean i| ≤ channelNoiseBound (channelTheta k d) N),
      ∀ r ∈ Set.Icc (0 : ℝ) 1,
        differentialEntropy (wholeGaussianDensity A (channelCovarianceFloor (channelTheta k d) N)
          hlo hlower 0)/(N : ℝ) ≤
          differentialEntropy (starGaussianDensity A (channelCovarianceFloor (channelTheta k d) N)
            hlo hlower G (fun i => r*mean i))-
          (d : ℝ)/2*differentialEntropy (edgeGaussianDensity A (channelCovarianceFloor (channelTheta k d) N)
            hlo hlower G (fun i => r*mean i))+
          (N : ℝ)^(-channelTheta k d/2) := by
  filter_upwards [eventually_gaussianChannelError_polynomial k d M C,eventually_ge_atTop 1] with N herr hN
  intro J _ _ m A G hd hNd hA hlo hlower hG e mean hmean r hr
  have hnp : 0 < (N : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hN
  have hH : 0 < channelNoiseBound (channelTheta k d) N := Real.rpow_pos_of_pos hnp _
  have hc : 0 < channelNoiseVariance (channelTheta k d) N := by exact_mod_cast hH
  have hvar (i : Fin k × Fin N) : coordinateVariance A i ≤ channelNoiseVariance (channelTheta k d) N := by
    exact_mod_cast (coordinateVariance_le_covariance_norm A i).trans hA
  have h := correlated_gaussian_channel_entropy_all_scales A (channelCovarianceFloor (channelTheta k d) N) hlo hlower
    G (lt_of_lt_of_le Nat.zero_lt_one hN) hd hNd C ((N : ℝ)^(1/4 : ℝ)) M hG
    (channelCutoff_pos (channelTheta k d) N (lt_of_lt_of_le Nat.zero_lt_one hN)) e mean
    (channelNoiseBound (channelTheta k d) N) hH.le hmean (channelNoiseVariance (channelTheta k d) N) hc hvar
    (channelMesh (channelTheta k d) N) (channelMesh_pos _ _ (lt_of_lt_of_le Nat.zero_lt_one hN))
    (channel_mean_within_clipping _ (channelTheta_pos k d).le N hN) (channelDither N)
    (Real.rpow_pos_of_pos hnp _) (channelCovarianceFloor (channelTheta k d) N) hlo
    (covariance_lower_le_coordinateVariance A _ hlower) r hr
  rw [wholeGaussianDensity_entropy_mean_independent A _ hlo hlower (fun i => r*mean i) 0] at h
  exact h.trans (add_le_add_left (herr m A hNd hA) _)

end GeneralizedBulk.Graph.Configuration
