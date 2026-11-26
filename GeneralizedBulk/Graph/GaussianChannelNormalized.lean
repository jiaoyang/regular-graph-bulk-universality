import GeneralizedBulk.Graph.GaussianChannelEntropy

/-! Per-vertex normalization of the proved correlated Gaussian channel
entropy inequality, uniformly for all scalar contractions of the signal. -/
noncomputable section
open scoped BigOperators Classical NNReal

namespace GeneralizedBulk.Graph.Configuration
open Entropy GeneralizedBulk.Gaussian

variable {k N d : ℕ} {J₀ : Type*} [Fintype J₀] [DecidableEq J₀]
variable (A : Matrix (Fin k × Fin N) J₀ ℝ) (lo : ℝ) (hlo : 0 < lo)
  (hbound : ∀ x : Fin k × Fin N → ℝ,lo*(∑ i,x i^2) ≤ dotProduct x ((A*A.transpose).mulVec x))

set_option maxHeartbeats 1500000 in
theorem correlated_gaussian_channel_entropy_per_vertex {q m K : ℕ}
    (G : RegularGraph N d) (hN : 0 < N) (hd : 0 < d) (hNd : N*d = 2*m)
    (C t : ℝ) (M : ℕ) (hG : GraphProfileGood (q := q) (m := m) C t M G)
    (hK : 0 < K) (e : (Fin k → Fin (2*K)) ≃ Fin q)
    (mean : Fin k × Fin N → ℝ) (H : ℝ) (hH : 0 ≤ H) (hmean : ∀ i,|mean i| ≤ H)
    (c : ℝ≥0) (hc : 0 < c) (hvar : ∀ i,coordinateVariance A i ≤ c)
    (a : ℝ) (ha : 0 < a) (hR : H ≤ (K : ℝ)*a) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (v₀ : ℝ) (hv₀ : 0 < v₀) (hvarlo : ∀ i,v₀ ≤ coordinateVariance A i) :
    differentialEntropy (wholeGaussianDensity A lo hlo hbound mean)/(N : ℝ) ≤
      differentialEntropy (starGaussianDensity A lo hlo hbound G mean)-
        (d : ℝ)/2*differentialEntropy (edgeGaussianDensity A lo hlo hbound G mean)+
        gaussianChannelError (d := d) A lo q m C t M H c a ℓ v₀ K/(N : ℝ) := by
  have h := correlated_gaussian_channel_entropy A lo hlo hbound G hN hd hNd C t M hG hK e
    mean H hH hmean c hc hvar a ha hR ℓ hℓ v₀ hv₀ hvarlo
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hcoef : (m : ℝ)/(N : ℝ) = (d : ℝ)/2 := by
    apply (div_eq_div_iff (ne_of_gt hNreal) (by norm_num : (2 : ℝ) ≠ 0)).mpr
    have hh : (N : ℝ)*(d : ℝ) = 2*(m : ℝ) := by exact_mod_cast hNd
    linarith
  apply (div_le_div_of_nonneg_right h hNreal.le).trans_eq
  calc
    _ = differentialEntropy (starGaussianDensity A lo hlo hbound G mean)-
        ((m : ℝ)/(N : ℝ))*differentialEntropy (edgeGaussianDensity A lo hlo hbound G mean)+
        gaussianChannelError (d := d) A lo q m C t M H c a ℓ v₀ K/(N : ℝ) := by
      field_simp
      <;> ring
    _ = _ := by rw [hcoef]

theorem scaled_signal_abs_le (mean : Fin k × Fin N → ℝ) (H : ℝ) (hH : 0 ≤ H)
    (hmean : ∀ i,|mean i| ≤ H) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (i : Fin k × Fin N) :
    |r*mean i| ≤ H := by
  rw [abs_mul,abs_of_nonneg hr0]
  exact (mul_le_mul_of_nonneg_left (hmean i) hr0).trans (by nlinarith)

theorem correlated_gaussian_channel_entropy_all_scales {q m K : ℕ}
    (G : RegularGraph N d) (hN : 0 < N) (hd : 0 < d) (hNd : N*d = 2*m)
    (C t : ℝ) (M : ℕ) (hG : GraphProfileGood (q := q) (m := m) C t M G)
    (hK : 0 < K) (e : (Fin k → Fin (2*K)) ≃ Fin q)
    (mean : Fin k × Fin N → ℝ) (H : ℝ) (hH : 0 ≤ H) (hmean : ∀ i,|mean i| ≤ H)
    (c : ℝ≥0) (hc : 0 < c) (hvar : ∀ i,coordinateVariance A i ≤ c)
    (a : ℝ) (ha : 0 < a) (hR : H ≤ (K : ℝ)*a) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (v₀ : ℝ) (hv₀ : 0 < v₀) (hvarlo : ∀ i,v₀ ≤ coordinateVariance A i) :
    ∀ r ∈ Set.Icc (0 : ℝ) 1,
      differentialEntropy (wholeGaussianDensity A lo hlo hbound (fun i => r*mean i))/(N : ℝ) ≤
        differentialEntropy (starGaussianDensity A lo hlo hbound G (fun i => r*mean i))-
          (d : ℝ)/2*differentialEntropy (edgeGaussianDensity A lo hlo hbound G (fun i => r*mean i))+
          gaussianChannelError (d := d) A lo q m C t M H c a ℓ v₀ K/(N : ℝ) := by
  intro r hr
  exact correlated_gaussian_channel_entropy_per_vertex A lo hlo hbound G hN hd hNd C t M hG hK e
    (fun i => r*mean i) H hH (scaled_signal_abs_le mean H hH hmean r hr.1 hr.2)
    c hc hvar a ha hR ℓ hℓ v₀ hv₀ hvarlo

end GeneralizedBulk.Graph.Configuration
