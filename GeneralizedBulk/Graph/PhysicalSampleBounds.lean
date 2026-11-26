import GeneralizedBulk.Graph.SpectralSampleCovariances
import GeneralizedBulk.Entropy.SelectedGaussianOtherBounds
import GeneralizedBulk.Entropy.UniformProductMass

/-! The actual physical spectral factors inherit resolvent-scale coercivity
and variance, independent of their construction floor, and actual uniformly
scaled eigenvector means satisfy the needed local absolute bounds. -/
noncomputable section
open scoped BigOperators Classical
namespace GeneralizedBulk.Entropy
open GeneralizedBulk.Entropy.Mehler

theorem coordinateL1_selected_scaled_le {I J : Type*} [Fintype J]
    (f : I → ℝ) (e : J → I) (B : ℝ) (hB : 0 ≤ B) (hf : ∀ i,|f i| ≤ B)
    (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    coordinateL1 ((fun i => r*f i) ∘ e) ≤ (Fintype.card J : ℝ)*B := by
  unfold coordinateL1
  calc
    _ ≤ ∑ j : J,B := Finset.sum_le_sum (fun j _ => by
      change |r*f (e j)| ≤ B
      rw [abs_mul,abs_of_nonneg hr.1]
      exact (mul_le_mul_of_nonneg_left (hf _) hr.1).trans (by nlinarith [hr.2]))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

theorem uniformProduct_bad_mass_lt_one {N : ℕ} (hN : 2 ≤ N)
    (C : Type*) [Fintype C] [Nonempty C] (bad : Finset (Fin N))
    (hbad : (bad.card : ℝ) ≤ (N : ℝ)^(1/2 : ℝ)) :
    subsetWeightMass (uniformSampleWeight (Fin N × C)) (fun s => s.1 ∈ bad) < 1 := by
  have hn : 0 < N := by omega
  have hh := uniformProduct_bad_mass_le_sqrt_reciprocal hn C bad hbad
  exact hh.trans_lt (Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (by omega : 1 < N)) (by norm_num))

end GeneralizedBulk.Entropy

namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Gaussian GeneralizedBulk.Covariance GeneralizedBulk.Entropy
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)
variable {k : ℕ} {J : Type*} [Fintype J]
variable (A : Matrix (Fin k × Fin (N n)) J ℝ) (lo : ℝ) (hlo : 0 < lo)
  (hbound : ∀ x : Fin k × Fin (N n) → ℝ,lo*(∑ i,x i^2) ≤ dotProduct x ((A*A.transpose).mulVec x))

def physicalResolventFloor (d : ℕ) (eta : ℝ) : ℝ := eta/(2*((2*(d : ℝ))^2+1))

theorem spectralSample_resolvent_global_bounds (energy sigma : Fin k → ℝ) (eta s : ℝ)
    (heta : 0 < eta) (heta1 : eta ≤ 1) (hs : 0 < s) (hsigma : ∀ a,s ≤ sigma a ∧ sigma a ≤ 2)
    (hE : ∀ a,|energy a| ≤ d)
    (hGram : A*A.transpose=D.coloredResolventCovariance n ω energy eta sigma)
    (x : Fin k × Fin (N n) → ℝ) :
    physicalResolventFloor d eta*(∑ i,x i^2) ≤ dotProduct x ((A*A.transpose).mulVec x) ∧
      dotProduct x ((A*A.transpose).mulVec x) ≤ (1/(s*eta))*(∑ i,x i^2) := by
  rw [hGram]
  exact D.coloredResolventCovariance_uniform_bounds n ω energy eta sigma heta heta1 s 2 hs (by norm_num) hsigma hE x

theorem spectralStarNoiseFactor_resolvent_bounds (energy sigma : Fin k → ℝ) (eta s : ℝ)
    (heta : 0 < eta) (heta1 : eta ≤ 1) (hs : 0 < s) (hsigma : ∀ a,s ≤ sigma a ∧ sigma a ≤ 2)
    (hE : ∀ a,|energy a| ≤ d)
    (hGram : A*A.transpose=D.coloredResolventCovariance n ω energy eta sigma)
    (sample : Fin (N n) × Equiv.Perm (Fin d)) (x : Fin k × Fin (d+1) → ℝ) :
    physicalResolventFloor d eta*(∑ i,x i^2) ≤ dotProduct x
      ((D.spectralStarNoiseFactor n ω A lo hlo hbound sample*(D.spectralStarNoiseFactor n ω A lo hlo hbound sample).transpose).mulVec x) ∧
    dotProduct x ((D.spectralStarNoiseFactor n ω A lo hlo hbound sample*
      (D.spectralStarNoiseFactor n ω A lo hlo hbound sample).transpose).mulVec x) ≤ (1/(s*eta))*(∑ i,x i^2) := by
  apply selectedGaussianFactor_other_bounds A _ _ lo hlo hbound _ _ _ x
  exact D.spectralSample_resolvent_global_bounds n ω A energy sigma eta s heta heta1 hs hsigma hE hGram

theorem spectralEdgeNoiseFactor_resolvent_bounds (energy sigma : Fin k → ℝ) (eta s : ℝ)
    (heta : 0 < eta) (heta1 : eta ≤ 1) (hs : 0 < s) (hsigma : ∀ a,s ≤ sigma a ∧ sigma a ≤ 2)
    (hE : ∀ a,|energy a| ≤ d)
    (hGram : A*A.transpose=D.coloredResolventCovariance n ω energy eta sigma)
    (sample : Fin (N n) × Fin d) (x : Fin k × Fin 2 → ℝ) :
    physicalResolventFloor d eta*(∑ i,x i^2) ≤ dotProduct x
      ((D.spectralEdgeNoiseFactor n ω A lo hlo hbound sample*(D.spectralEdgeNoiseFactor n ω A lo hlo hbound sample).transpose).mulVec x) ∧
    dotProduct x ((D.spectralEdgeNoiseFactor n ω A lo hlo hbound sample*
      (D.spectralEdgeNoiseFactor n ω A lo hlo hbound sample).transpose).mulVec x) ≤ (1/(s*eta))*(∑ i,x i^2) := by
  apply selectedGaussianFactor_other_bounds A _ _ lo hlo hbound _ _ _ x
  exact D.spectralSample_resolvent_global_bounds n ω A energy sigma eta s heta heta1 hs hsigma hE hGram

end GeneralizedBulk.External.RegularSpectralData
