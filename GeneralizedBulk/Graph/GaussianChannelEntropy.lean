import GeneralizedBulk.Graph.GaussianSampleLaws
import GeneralizedBulk.Entropy.CorrelatedColoringEntropy
import GeneralizedBulk.Entropy.AffineQuantizedEntropy

/-! The correlated Gaussian-channel entropy inequality obtained from actual
configuration counting, Gaussian concentration, and quantizer entropy.
The common good graph event works simultaneously for every bounded signal. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical NNReal Matrix.L2OpNorm

namespace GeneralizedBulk.Graph.Configuration
open ColorProfiles Entropy GeneralizedBulk.Gaussian

variable {k N d : ℕ} {J₀ : Type*} [Fintype J₀]
variable (A : Matrix (Fin k × Fin N) J₀ ℝ) (lo : ℝ) (hlo : 0 < lo)
  (hbound : ∀ x : Fin k × Fin N → ℝ,lo*(∑ i,x i^2) ≤ dotProduct x ((A*A.transpose).mulVec x))

def wholeGaussianDensity (mean : Fin k × Fin N → ℝ) : (Fin (k*N) → ℝ) → ℝ :=
  affineGaussianPDF (mean ∘ flatSelection (id : Fin N → Fin N)) (wholeNoiseFactor A lo hlo hbound)

def starGaussianDensity (G : RegularGraph N d) (mean : Fin k × Fin N → ℝ) : (Fin (k*(d+1)) → ℝ) → ℝ :=
  gaussianMixturePDF (uniformSampleWeight (Fin N × Equiv.Perm (Fin d)))
    (fun z => mean ∘ flatSelection (starVertexSelection G z)) (starNoiseFactor A lo hlo hbound G)

def edgeGaussianDensity (G : RegularGraph N d) (mean : Fin k × Fin N → ℝ) : (Fin (k*2) → ℝ) → ℝ :=
  gaussianMixturePDF (uniformSampleWeight (Fin N × Fin d))
    (fun z => mean ∘ flatSelection (edgeVertexSelection G z)) (edgeNoiseFactor A lo hlo hbound G)

def channelCountingError (N d q m : ℕ) (C t : ℝ) (M : ℕ) : ℝ :=
  ((q : ℝ)^2/2+2)*(C+Real.log (2*m+1))+3*paletteLog N d q+t+simplicityCost N d M

def gaussianChannelError (q m : ℕ) (C t : ℝ) (M : ℕ) (H : ℝ) (c : ℝ≥0)
    (a ℓ v₀ : ℝ) (K : ℕ) : ℝ :=
  gaussianClippingError (k*N) a H c K+(N : ℝ)*gaussianLocalGridError (k*(d+1)) a lo+
    (m : ℝ)*gaussianClippingError (k*2) a H c K+
    (m : ℝ)*(3+Real.log (q*q : ℕ))*
      Real.sqrt (edgeProfileConcentrationError (B := Fin (2*K)) A (clippedGridBoundaries a K) ℓ v₀/2)+
    channelCountingError N d q m C t M

set_option maxHeartbeats 2500000 in
theorem correlated_gaussian_channel_entropy {q m K : ℕ} [DecidableEq J₀]
    (G : RegularGraph N d) (hN : 0 < N) (hd : 0 < d) (hNd : N*d = 2*m)
    (C t : ℝ) (M : ℕ) (hG : GraphProfileGood (q := q) (m := m) C t M G)
    (hK : 0 < K) (e : (Fin k → Fin (2*K)) ≃ Fin q)
    (mean : Fin k × Fin N → ℝ) (H : ℝ) (hH : 0 ≤ H) (hmean : ∀ i,|mean i| ≤ H)
    (c : ℝ≥0) (hc : 0 < c) (hvar : ∀ i,coordinateVariance A i ≤ c)
    (a : ℝ) (ha : 0 < a) (hR : H ≤ (K : ℝ)*a) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (v₀ : ℝ) (hv₀ : 0 < v₀) (hvarlo : ∀ i,v₀ ≤ coordinateVariance A i) :
    differentialEntropy (wholeGaussianDensity A lo hlo hbound mean) ≤
      (N : ℝ)*differentialEntropy (starGaussianDensity A lo hlo hbound G mean)-
        (m : ℝ)*differentialEntropy (edgeGaussianDensity A lo hlo hbound G mean)+
        gaussianChannelError (d := d) A lo q m C t M H c a ℓ v₀ K := by
  letI : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  let μ := linearImageGaussian A
  let Q := codedClippedGridLabel a K hK
  have hQ : Measurable Q := measurable_codedClippedGridLabel a K hK
  let color := fun x => quantizedVertexColor e Q (mean+x)
  have hdiscrete := correlated_gaussian_coloring_entropy_bound G hN hd hNd C t M hG A e Q hQ
    (clippedGridBoundaries a K) (codedClippedGrid_has_boundaries a ha K hK) ℓ hℓ mean v₀ hv₀ hvarlo
  have hwholeEq := entropy_quantized_whole_eq μ mean e Q hQ
  rw [realWholeLaw_gaussian A lo hlo hbound mean] at hwholeEq
  have hwhole := affineGaussian_clipped_entropy_lower
    (mean ∘ flatSelection (id : Fin N → Fin N)) (wholeNoiseFactor A lo hlo hbound)
    (wholeNoiseFactor_det_ne_zero A lo hlo hbound) H hH (fun i => hmean _)
    c hc (fun i => by rw [wholeNoiseFactor_coordinateVariance]; exact hvar _) a ha K hK hR
  change Finite.entropy (lawMass μ color) = Finite.entropy (lawMass
    (affineGaussian (mean ∘ flatSelection (id : Fin N → Fin N)) (wholeNoiseFactor A lo hlo hbound))
      (codedClipIntegerVector K hK ∘ gridLabel a)) at hwholeEq
  rw [← hwholeEq] at hwhole
  have hstarEq := entropy_mean_star_eq_quantized_sample μ G mean e Q hQ
  rw [realStarSampleLaw_gaussian A lo hlo hbound G mean] at hstarEq
  have hstar := gaussianMixture_clipped_entropy_upper
    (uniformSampleWeight (Fin N × Equiv.Perm (Fin d)))
    (fun z => mean ∘ flatSelection (starVertexSelection G z)) (starNoiseFactor A lo hlo hbound G)
    (uniformSampleWeight_nonneg _) (uniformSampleWeight_sum _)
    (starNoiseFactor_det_ne_zero A lo hlo hbound G) lo hlo
    (starNoiseFactor_lower A lo hlo hbound G) a ha K hK
  change Finite.entropy (meanProfile μ (fun x => graphStarProfile G (color x))) =
    Finite.entropy (lawMass (gaussianMixtureLaw (uniformSampleWeight (Fin N × Equiv.Perm (Fin d)))
      (fun z => mean ∘ flatSelection (starVertexSelection G z)) (starNoiseFactor A lo hlo hbound G))
      (codedClipIntegerVector K hK ∘ gridLabel a)) at hstarEq
  rw [← hstarEq] at hstar
  have hedgeEq := entropy_mean_edge_eq_quantized_sample μ G hN hd hNd mean e Q hQ
  rw [realEdgeSampleLaw_gaussian A lo hlo hbound G mean] at hedgeEq
  have hedge := gaussianMixture_clipped_entropy_lower
    (uniformSampleWeight (Fin N × Fin d))
    (fun z => mean ∘ flatSelection (edgeVertexSelection G z)) (edgeNoiseFactor A lo hlo hbound G)
    (uniformSampleWeight_nonneg _) (uniformSampleWeight_sum _)
    (edgeNoiseFactor_det_ne_zero A lo hlo hbound G) H hH (fun z i => hmean _)
    c hc (fun z i => by rw [edgeNoiseFactor_coordinateVariance]; exact hvar _) a ha K hK hR
  change Finite.entropy (meanProfile μ (fun x => graphEdgeProfile G (color x))) =
    Finite.entropy (lawMass (gaussianMixtureLaw (uniformSampleWeight (Fin N × Fin d))
      (fun z => mean ∘ flatSelection (edgeVertexSelection G z)) (edgeNoiseFactor A lo hlo hbound G))
      (codedClipIntegerVector K hK ∘ gridLabel a)) at hedgeEq
  rw [← hedgeEq] at hedge
  have hstarN := mul_le_mul_of_nonneg_left hstar (show (0 : ℝ) ≤ N by positivity)
  have hedgeM := mul_le_mul_of_nonneg_left hedge (show (0 : ℝ) ≤ m by positivity)
  have hlogs : (k*N : ℕ)*Real.log a =
      (N : ℝ)*(k*(d+1) : ℕ)*Real.log a-(m : ℝ)*(k*2 : ℕ)*Real.log a := by
    have he : (N : ℝ)*(d : ℝ) = 2*(m : ℝ) := by exact_mod_cast hNd
    have hh := congrArg (fun r : ℝ => (k : ℝ)*r*Real.log a) he
    push_cast
    ring_nf at hh ⊢
    linarith
  change -gaussianClippingError (k*N) a H c K ≤ Finite.entropy (lawMass μ color)+
    (k*N : ℕ)*Real.log a-differentialEntropy (wholeGaussianDensity A lo hlo hbound mean) at hwhole
  change (N : ℝ)*(Finite.entropy (meanProfile μ (fun x => graphStarProfile G (color x)))+
    (k*(d+1) : ℕ)*Real.log a-differentialEntropy (starGaussianDensity A lo hlo hbound G mean)) ≤
    (N : ℝ)*gaussianLocalGridError (k*(d+1)) a lo at hstarN
  change (m : ℝ)*(-gaussianClippingError (k*2) a H c K) ≤ (m : ℝ)*
    (Finite.entropy (meanProfile μ (fun x => graphEdgeProfile G (color x)))+(k*2 : ℕ)*Real.log a-
      differentialEntropy (edgeGaussianDensity A lo hlo hbound G mean)) at hedgeM
  change Finite.entropy (lawMass μ color) ≤ (N : ℝ)*Finite.entropy (meanProfile μ (fun x => graphStarProfile G (color x)))-
    (m : ℝ)*Finite.entropy (meanProfile μ (fun x => graphEdgeProfile G (color x)))+
    (m : ℝ)*(3+Real.log (q*q : ℕ))*Real.sqrt (edgeProfileConcentrationError (B := Fin (2*K)) A (clippedGridBoundaries a K) ℓ v₀/2)+
    ((q : ℝ)^2/2+2)*(C+Real.log (2*m+1))+3*paletteLog N d q+t+simplicityCost N d M at hdiscrete
  unfold gaussianChannelError channelCountingError
  nlinarith only [hwhole,hstarN,hedgeM,hdiscrete,hlogs]

end GeneralizedBulk.Graph.Configuration
