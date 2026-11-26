import GeneralizedBulk.Entropy.MehlerHilbert
import GeneralizedBulk.Entropy.EntropyDeficitAlgebra
import GeneralizedBulk.Entropy.ChaosSquares

/-! The entropy-to-quadratic approximation for actual Gaussian observation channels. -/
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace GeneralizedBulk.Entropy.Mehler
open GeneralizedBulk.Entropy.Hermite
namespace NormalizedFiniteSignal
variable {I S C : Type*} [Fintype I] [DecidableEq I] [Fintype S] [Fintype C]
variable (D : NormalizedFiniteSignal I S)

def observationEntropyDeficit (O : C → Matrix I I ℝ)
    (hO : ∀ c, O c * (O c).transpose = 1) (observed : C → Finset I) (a : ℝ) : ℝ :=
  relativeEntropy (standardGaussian I) (D.density a) - (1 / 2 : ℝ) *
    ∑ c, relativeEntropy (standardGaussian (observed c)) ((D.observedSignal (O c) (hO c) (observed c)).density a)

def observationRemainderConstant (observed : C → Finset I) : ℝ :=
  smoothingEntropyConstant I + (1 / 2 : ℝ) * ∑ c, smoothingEntropyConstant (observed c)

theorem observationRemainderConstant_pos (observed : C → Finset I) :
    0 < observationRemainderConstant observed := by
  have h1 := smoothingEntropyConstant_pos I
  have h2 : 0 ≤ ∑ c, smoothingEntropyConstant (observed c) :=
    Finset.sum_nonneg (fun c _ => (smoothingEntropyConstant_pos (observed c)).le)
  unfold observationRemainderConstant
  linarith

/-- All analytic inputs in this approximation are constructed from finite
signal values. In particular the actual conditional Gaussian operators,
not new abstract marginal operators, occur in its quadratic form. -/
theorem observationEntropyDeficit_quadratic_bound
    (O : C → Matrix I I ℝ) (hO : ∀ c, O c * (O c).transpose = 1)
    (observed : C → Finset I) (B a : ℝ) (hB : 0 ≤ B) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2)
    (hsmall : a * (((Fintype.card I : ℝ) + 1) * B) ≤ 1 / 2)
    (hsignal : ∀ s, coordinateL1 (D.signal s) ≤ B)
    (f : Lp ℝ 2 (standardGaussian I))
    (hf : (f : (I → ℝ) → ℝ) =ᵐ[standardGaussian I] (fun x => D.density a x - 1)) :
    |D.observationEntropyDeficit O hO observed a -
      (1 / 2 : ℝ) * gaussianChannelDefect O hO observed f| ≤
      observationRemainderConstant observed * (1 + (((Fintype.card I : ℝ) + 1) * B) ^ 2) ^ 9 * a ^ 9 := by
  let M := ((Fintype.card I : ℝ) + 1) * B
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hBM : B ≤ M := by
    dsimp [M]
    nlinarith [mul_nonneg (Nat.cast_nonneg (Fintype.card I)) hB]
  have hfull : ∀ s, coordinateL1 (D.signal s) ≤ M := fun s => (hsignal s).trans hBM
  have hobs (c : C) (s : S) : coordinateL1 ((D.observedSignal (O c) (hO c) (observed c)).signal s) ≤ M :=
    (D.observedSignal_bound (O c) (hO c) (observed c) B hsignal s).trans (by
      dsimp [M]
      nlinarith)
  have hff : f = D.centeredL2 M a hM ha ha1 hsmall hfull :=
    Lp.ext (hf.trans (D.centeredL2_ae M a hM ha ha1 hsmall hfull).symm)
  subst f
  let P := (1 + M ^ 2) ^ 9 * a ^ 9
  have he : |relativeEntropy (standardGaussian I) (D.density a) -
      (1 / 2 : ℝ) * ‖D.centeredL2 M a hM ha ha1 hsmall hfull‖ ^ 2| ≤ smoothingEntropyConstant I * P := by
    rw [D.centeredL2_norm_sq]
    convert D.entropy_quadratic_bound M a hM ha ha1 hsmall hfull using 1 <;> ring
  have hei (c : C) :
      |relativeEntropy (standardGaussian (observed c)) ((D.observedSignal (O c) (hO c) (observed c)).density a) -
        (1 / 2 : ℝ) * ‖subspaceConditionalL2 (O c) (hO c) (observed c)
          (D.centeredL2 M a hM ha ha1 hsmall hfull)‖ ^ 2| ≤ smoothingEntropyConstant (observed c) * P := by
    rw [D.channel_centeredL2_norm_sq]
    convert (D.observedSignal (O c) (hO c) (observed c)).entropy_quadratic_bound
      M a hM ha ha1 hsmall (hobs c) using 1 <;> ring
  have h := entropy_deficit_quadratic_error
    (relativeEntropy (standardGaussian I) (D.density a))
    (‖D.centeredL2 M a hM ha ha1 hsmall hfull‖ ^ 2) (smoothingEntropyConstant I * P)
    (fun c => relativeEntropy (standardGaussian (observed c)) ((D.observedSignal (O c) (hO c) (observed c)).density a))
    (fun c => ‖subspaceConditionalL2 (O c) (hO c) (observed c) (D.centeredL2 M a hM ha ha1 hsmall hfull)‖ ^ 2)
    (fun c => smoothingEntropyConstant (observed c) * P) he hei
  change |D.observationEntropyDeficit O hO observed a -
    (1 / 2 : ℝ) * gaussianChannelDefect O hO observed (D.centeredL2 M a hM ha ha1 hsmall hfull)| ≤ _ at h
  apply h.trans_eq
  rw [← Finset.sum_mul]
  dsimp [observationRemainderConstant, P, M]
  ring

end NormalizedFiniteSignal
end GeneralizedBulk.Entropy.Mehler
