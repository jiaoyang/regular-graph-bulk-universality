import GeneralizedBulk.Entropy.MehlerHermiteMoments
import GeneralizedBulk.Entropy.InfiniteChannelDefect

/-! The actual finite-signal Mehler density has its true infinite Hermite
expansion with exact powers of the smoothing parameter. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Mehler
open GeneralizedBulk.Entropy.Hermite
variable {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S]

/-- The actual degree-n Gaussian chaos with the finite signal's Hermite
moments, with the exact Gaussian factorial normalization. -/
def signalChaos (weight : S → ℝ) (signal : S → I → ℝ) (degree : ℕ) : fullChaosSpace I degree :=
  fullChaosEquiv I degree (fun α => signalHermiteMoment weight signal (degreeIndexNat I α) /
    multiFactorial I (degreeIndexNat I α))

@[simp] theorem signalChaos_coe (weight : S → ℝ) (signal : S → I → ℝ) (degree : ℕ) :
    (signalChaos weight signal degree : Lp ℝ 2 (standardGaussian I)) =
      fullChaosMap I degree (fun α => signalHermiteMoment weight signal (degreeIndexNat I α) /
        multiFactorial I (degreeIndexNat I α)) := rfl

theorem integral_multiHermite_positive_degree (α : I → ℕ) (hα : 0 < ∑ i, α i) :
    (∫ x, multiHermite I α x ∂standardGaussian I) = 0 := by
  rw [integral_multiHermite_mean]
  have hn : α ≠ fun _ => 0 := by
    intro h
    rw [h] at hα
    simp at hα
  simp only [hn, ↓reduceIte]

/-- Exact positive-degree Gaussian pairings of the literal centered density. -/
theorem inner_centered_density_multiLp (weight : S → ℝ) (signal : S → I → ℝ)
    (a : ℝ) (ha : 0 < 1 - a ^ 2) (f : Lp ℝ 2 (standardGaussian I))
    (hf : (f : (I → ℝ) → ℝ) =ᵐ[standardGaussian I] fun z => finiteMixtureKernel weight signal a z - 1)
    (α : I → ℕ) (hα : 0 < ∑ i, α i) :
    @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ f (multiLp I α) =
      a ^ (∑ i, α i) * signalHermiteMoment weight signal α := by
  rw [L2.inner_def]
  calc
    _ = ∫ z, finiteMixtureKernel weight signal a z * multiHermite I α z - multiHermite I α z ∂standardGaussian I := by
      apply integral_congr_ae
      filter_upwards [hf, multiLp_ae I α] with z hzf hzα
      rw [hzf, hzα]
      simp only [RCLike.inner_apply, conj_trivial]
      ring
    _ = _ := by
      rw [integral_sub (integrable_finiteMixture_mul_multiHermite weight signal a ha α)
        (integrable_multiHermite I α), integral_finiteMixture_mul_multiHermite weight signal a ha α,
        integral_multiHermite_positive_degree α hα, sub_zero]

/-- The actual Hilbert projection of the smoothed density is exactly the
signal chaos multiplied by the corresponding power of the smoothing scale. -/
theorem chaosComponent_centered_density (weight : S → ℝ) (signal : S → I → ℝ)
    (a : ℝ) (ha : 0 < 1 - a ^ 2) (f : Lp ℝ 2 (standardGaussian I))
    (hf : (f : (I → ℝ) → ℝ) =ᵐ[standardGaussian I] fun z => finiteMixtureKernel weight signal a z - 1)
    (degree : ℕ) (hdegree : 0 < degree) :
    (chaosComponent I f degree : Lp ℝ 2 (standardGaussian I)) =
      a ^ degree • (signalChaos weight signal degree : Lp ℝ 2 (standardGaussian I)) := by
  let coeff := fullChaosCoordinates I degree (chaosComponent I f degree)
  have hc : fullChaosMap I degree coeff = (chaosComponent I f degree : Lp ℝ 2 (standardGaussian I)) :=
    fullChaosCoordinates_spec I degree (chaosComponent I f degree)
  have hcoeff (α : DegreeIndex I degree) : coeff α = a ^ degree *
      (signalHermiteMoment weight signal (degreeIndexNat I α) / multiFactorial I (degreeIndexNat I α)) := by
    have hi := chaosComponent_inner I degree f
      ⟨multiLp I (degreeIndexNat I α), multiLp_mem_fullChaosSpace I degree _ (degreeIndexNat_sum I α)⟩
    change @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ (chaosComponent I f degree : Lp ℝ 2 (standardGaussian I))
      (multiLp I (degreeIndexNat I α)) = _ at hi
    rw [← hc, fullChaosMap_inner_basis, inner_centered_density_multiLp weight signal a ha f hf _
      (by rw [degreeIndexNat_sum]; exact hdegree), degreeIndexNat_sum] at hi
    rw [← mul_div_assoc]
    apply (eq_div_iff (ne_of_gt (multiFactorial_pos I _))).mpr
    exact hi
  rw [← hc, signalChaos_coe, ← map_smul]
  apply congrArg (fullChaosMap I degree)
  funext α
  exact hcoeff α

theorem centered_density_integral_zero (weight : S → ℝ) (signal : S → I → ℝ)
    (hnorm : ∑ s, weight s = 1) (a : ℝ) (ha : 0 < 1 - a ^ 2)
    (f : Lp ℝ 2 (standardGaussian I))
    (hf : (f : (I → ℝ) → ℝ) =ᵐ[standardGaussian I] fun z => finiteMixtureKernel weight signal a z - 1) :
    (∫ z, f z ∂standardGaussian I) = 0 := by
  rw [integral_congr_ae hf, integral_sub (integrable_finiteMixtureKernel weight signal a ha) (integrable_const 1),
    integral_finiteMixtureKernel weight signal hnorm a ha]
  simp

/-- The complete actual L² Mehler expansion, including convergence, with its
constant term removed by true normalization. -/
theorem hasSum_centered_density_signalChaos (weight : S → ℝ) (signal : S → I → ℝ)
    (hnorm : ∑ s, weight s = 1) (a : ℝ) (ha : 0 < 1 - a ^ 2)
    (f : Lp ℝ 2 (standardGaussian I))
    (hf : (f : (I → ℝ) → ℝ) =ᵐ[standardGaussian I] fun z => finiteMixtureKernel weight signal a z - 1) :
    HasSum (fun degree : ℕ => if degree = 0 then 0 else
      a ^ degree • (signalChaos weight signal degree : Lp ℝ 2 (standardGaussian I))) f := by
  have hs := hasSum_chaosComponents I f
  convert hs using 1
  funext n
  by_cases hn : n = 0
  · subst n
    simp only [↓reduceIte, chaosComponent_zero_of_integral_zero I f
      (centered_density_integral_zero weight signal hnorm a ha f hf)]
    rfl
  · simp only [hn, ↓reduceIte]
    exact (chaosComponent_centered_density weight signal a ha f hf n (Nat.pos_of_ne_zero hn)).symm

end GeneralizedBulk.Entropy.Mehler
