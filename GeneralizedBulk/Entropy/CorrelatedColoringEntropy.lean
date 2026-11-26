import GeneralizedBulk.Graph.QuantizedProfiles

/-! The actual common-good-graph entropy inequality for componentwise
quantization of an arbitrary correlated Gaussian vector. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical Matrix.L2OpNorm

namespace GeneralizedBulk.Entropy
open GeneralizedBulk.Gaussian GeneralizedBulk.Graph GeneralizedBulk.Graph.Configuration
open GeneralizedBulk.Graph.ColorProfiles

variable {k N d q m : ℕ} {B J₀ : Type*} [Fintype B] [DecidableEq B]
  [MeasurableSpace B] [MeasurableSingletonClass B] [Fintype J₀] [DecidableEq J₀]

def edgeProfileConcentrationError (A : Matrix (Fin k × Fin N) J₀ ℝ)
    (F : Finset ℝ) (ℓ v₀ : ℝ) : ℝ :=
  32*k*(F.card : ℝ)*ℓ/Real.sqrt (2*Real.pi*v₀)+
    (Fintype.card B : ℝ)^(2*k)*Real.sqrt (‖A*A.transpose‖*((k : ℝ)/((N : ℝ)*ℓ^2)))

set_option maxHeartbeats 1500000 in
theorem quantized_graphEdgeProfile_mean_TV_le (G : RegularGraph N d)
    (hN : 0 < N) (hd : 0 < d) (hNd : N*d = 2*m)
    (A : Matrix (Fin k × Fin N) J₀ ℝ) (e : (Fin k → B) ≃ Fin q)
    (J : ℝ → B) (hJ : Measurable J) (F : Finset ℝ) (hF : HasQuantizerBoundaries J F)
    (ℓ : ℝ) (hℓ : 0 < ℓ) (a : Fin k × Fin N → ℝ) (v₀ : ℝ) (hv₀ : 0 < v₀)
    (hvar : ∀ i,v₀ ≤ coordinateVariance A i) :
    (∫ x,Finite.totalVariation (graphEdgeProfile G (quantizedVertexColor e J (a+x)))
      (meanProfile (linearImageGaussian A) (fun y => graphEdgeProfile G (quantizedVertexColor e J (a+y))))
      ∂linearImageGaussian A) ≤ edgeProfileConcentrationError (B := B) A F ℓ v₀/2 := by
  let μ := linearImageGaussian A
  let P := fun x word => quantizedHardEdgeAverage (graphNeighbor G) J a word x
  have he (x) : Finite.totalVariation (graphEdgeProfile G (quantizedVertexColor e J (a+x)))
      (meanProfile μ (fun y => graphEdgeProfile G (quantizedVertexColor e J (a+y)))) =
      (1/2 : ℝ)*profileL1 (P x) (meanProfile μ P) := by
    unfold Finite.totalVariation profileL1
    rw [← (edgeColorEquiv e).sum_comp]
    congr 1
    apply Finset.sum_congr rfl
    intro word hword
    rw [quantized_graphEdgeProfile_eq G hN hd hNd]
    congr 1
    congr 1
    unfold meanProfile
    simp_rw [quantized_graphEdgeProfile_eq G hN hd hNd]
    rfl
  dsimp only [μ] at he
  simp_rw [he]
  rw [integral_const_mul]
  have h := quantizedHardEdge_correlated_mean_l1_le A (graphNeighbor G) (graphNeighbor_sum G)
    hN hd J hJ F hF ℓ hℓ a v₀ hv₀ hvar
  have hh := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 1/2)
  dsimp only [edgeProfileConcentrationError]
  linarith only [hh]

set_option maxHeartbeats 1500000 in
theorem correlated_gaussian_coloring_entropy_bound (G : RegularGraph N d)
    (hN : 0 < N) (hd : 0 < d) (hNd : N*d = 2*m)
    (C t : ℝ) (M : ℕ) (hG : GraphProfileGood (q := q) (m := m) C t M G)
    (A : Matrix (Fin k × Fin N) J₀ ℝ) (e : (Fin k → B) ≃ Fin q)
    (J : ℝ → B) (hJ : Measurable J) (F : Finset ℝ) (hF : HasQuantizerBoundaries J F)
    (ℓ : ℝ) (hℓ : 0 < ℓ) (a : Fin k × Fin N → ℝ) (v₀ : ℝ) (hv₀ : 0 < v₀)
    (hvar : ∀ i,v₀ ≤ coordinateVariance A i) :
    Finite.entropy (lawMass (linearImageGaussian A) (fun x => quantizedVertexColor e J (a+x))) ≤
      (N : ℝ)*Finite.entropy (meanProfile (linearImageGaussian A)
        (fun x => graphStarProfile G (quantizedVertexColor e J (a+x))))-
        (m : ℝ)*Finite.entropy (meanProfile (linearImageGaussian A)
          (fun x => graphEdgeProfile G (quantizedVertexColor e J (a+x))))+
        (m : ℝ)*(3+Real.log (q*q : ℕ))*Real.sqrt (edgeProfileConcentrationError (B := B) A F ℓ v₀/2)+
        ((q : ℝ)^2/2+2)*(C+Real.log (2*m+1))+
        3*paletteLog N d q+t+simplicityCost N d M := by
  have h := random_coloring_entropy_mean_bound G hN hd C t M hG (linearImageGaussian A)
    (fun x => quantizedVertexColor e J (a+x)) (measurable_quantizedVertexColor e J hJ a)
  have hTV := quantized_graphEdgeProfile_mean_TV_le G hN hd hNd A e J hJ F hF ℓ hℓ a v₀ hv₀ hvar
  have hroot := Real.sqrt_le_sqrt hTV
  have hmul := mul_le_mul_of_nonneg_left hroot (show 0 ≤ (m : ℝ)*(3+Real.log (q*q : ℕ)) by
    apply mul_nonneg (by positivity)
    linarith [Real.log_natCast_nonneg (q*q)])
  linarith

end GeneralizedBulk.Entropy
