import GaussianWave.BS.Reused.Entropy.CountableLawTail
import GaussianWave.BS.Reused.Entropy.GridL2
import GaussianWave.BS.Reused.Entropy.FiniteHolder

/-! An actual finite-to-countable clipping entropy comparison. Its error
uses the probability of one global tail event and grows polynomially in
the dimension; there is no independence hypothesis. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical

namespace GaussianWave.BS.Reused.Entropy

variable {Ω : Type*} [MeasurableSpace Ω]

def gridClippingLossConstant (m : ℕ) (a B : ℝ) : ℝ :=
  3+linearIntegerEntropyConstant m+Real.sqrt ((m : ℝ)^2*(2*B/a^2+2))

theorem gridClippingLossConstant_nonneg (m : ℕ) (a B : ℝ) :
    0 ≤ gridClippingLossConstant m a B := by
  unfold gridClippingLossConstant
  exact add_nonneg (add_nonneg (by norm_num) (linearIntegerEntropyConstant_nonneg m)) (Real.sqrt_nonneg _)

set_option maxHeartbeats 1500000 in
theorem grid_clipping_entropy_loss_le {m : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin m → ℝ) (hX : Measurable X) (hcoord : ∀ i,MemLp (fun x => X x i) 2 μ)
    (B : ℝ) (hB : ∀ i,(∫ x,X x i^2 ∂μ) ≤ B) (a : ℝ) (ha : 0 < a)
    (K : ℕ) (hK : 0 < K) :
    countableEntropy (lawMass μ (gridLabel a ∘ X))-
      Finite.entropy (lawMass μ (codedClipIntegerVector K hK ∘ gridLabel a ∘ X)) ≤
      gridClippingLossConstant m a B*
        Real.sqrt (μ.real {x | integerClippingTail K (gridLabel a (X x))}) := by
  let Y := gridLabel a ∘ X
  let p := lawMass μ Y
  let δ := tailMass p (integerClippingTail K)
  have hY : Measurable Y := (measurable_gridLabel a).comp hX
  have hp := lawMass_nonneg μ Y
  have hs := lawMass_hasSum μ Y hY
  have hE : MemLp (fun x => integerEnergy (Y x)) 2 μ := memLp_gridEnergy μ X hX hcoord a ha
  have hmoment := (lawMass_weighted_hasSum μ Y hY integerEnergy (hE.integrable (by norm_num))).summable
  have hclip := coded_integer_clipping_entropy_bound p hp hs hmoment K hK
  have hpush : countablePush p (codedClipIntegerVector K hK) =
      lawMass μ (codedClipIntegerVector K hK ∘ Y) := by
    funext j
    exact countablePush_lawMass μ Y hY _ j
  have hfinite : countableEntropy (countablePush p (codedClipIntegerVector K hK)) =
      Finite.entropy (lawMass μ (codedClipIntegerVector K hK ∘ Y)) := by
    rw [hpush,countableEntropy,tsum_fintype]
    rfl
  rw [hfinite] at hclip
  have htail := restricted_lawMass_moment_le_sqrt μ Y hY (integerClippingTail K) integerEnergy hE
    integerEnergy_nonneg
  have hδreal : δ = μ.real {x | integerClippingTail K (gridLabel a (X x))} := tailMass_lawMass μ Y hY _
  have hδY : δ = μ.real {x | integerClippingTail K (Y x)} := tailMass_lawMass μ Y hY _
  have hδ : 0 ≤ δ := tailMass_nonneg p hp _
  have hδ1 : δ ≤ 1 := tailMass_le_one p hp hs _
  have hbin := Finite.binEntropy_le_three_sqrt δ hδ hδ1
  have hδsqrt : δ ≤ Real.sqrt δ := Real.le_sqrt_of_sq_le (by nlinarith)
  have hc := linearIntegerEntropyConstant_nonneg m
  have henergy : (∫ x,integerEnergy (Y x)^2 ∂μ) ≤ (m : ℝ)^2*(2*B/a^2+2) :=
    integral_gridEnergy_sq_le μ X hX hcoord B hB a ha
  have htail' : (∑' j,restrictedMass p (integerClippingTail K) j*integerEnergy j) ≤
      Real.sqrt ((m : ℝ)^2*(2*B/a^2+2))*Real.sqrt δ := by
    apply htail.trans
    rw [← hδY]
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt henergy) (Real.sqrt_nonneg _)
  have hδc := mul_le_mul_of_nonneg_right hδsqrt hc
  change countableEntropy p-Finite.entropy (lawMass μ (codedClipIntegerVector K hK ∘ Y)) ≤ _
  rw [← hδreal]
  change countableEntropy p-Finite.entropy (lawMass μ (codedClipIntegerVector K hK ∘ Y)) ≤
    (3+linearIntegerEntropyConstant m+Real.sqrt ((m : ℝ)^2*(2*B/a^2+2)))*Real.sqrt δ
  change countableEntropy p-Finite.entropy (lawMass μ (codedClipIntegerVector K hK ∘ Y)) ≤
    Real.binEntropy δ+δ*linearIntegerEntropyConstant m+
      (∑' j,restrictedMass p (integerClippingTail K) j*integerEnergy j) at hclip
  nlinarith

end GaussianWave.BS.Reused.Entropy
