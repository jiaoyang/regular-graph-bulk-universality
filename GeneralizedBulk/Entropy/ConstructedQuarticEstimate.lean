import GeneralizedBulk.Entropy.MehlerFourthLower
import GeneralizedBulk.Entropy.ConstructedEntropyDeficit
import GeneralizedBulk.EntropyOptimization

/-! The actual Gaussian analytic entropy-to-fourth-chaos estimate. The entropy
deficit upper bound is a numerical input here, to be supplied by finite graph
counting; all Gaussian analytic bounds are constructed and proved. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Channel
open GeneralizedBulk.Entropy GeneralizedBulk.Entropy.Hermite GeneralizedBulk.Entropy.Mehler

/-- The actual source Taylor coefficient with its proved polynomial signal
bound loss. Observation subspaces and this constant are parameter independent. -/
def starTaylorCoefficient (d k : ℕ) (hd : 2 ≤ d) (B : ℝ) : ℝ :=
  NormalizedFiniteSignal.observationRemainderConstant (coloredObserved d k hd) *
    (1 + (((Fintype.card (ScalarCoordinate d k) : ℝ) + 1) * B) ^ 2) ^ 9

theorem starTaylorCoefficient_pos (d k : ℕ) (hd : 2 ≤ d) (B : ℝ) :
    0 < starTaylorCoefficient d k hd B :=
  mul_pos (NormalizedFiniteSignal.observationRemainderConstant_pos (coloredObserved d k hd))
    (pow_pos (by positivity) _)

theorem starTaylorCoefficient_power (d k : ℕ) (hd : 2 ≤ d) (B : ℝ) :
    starTaylorCoefficient d k hd B ^ (4 / 9 : ℝ) =
      (NormalizedFiniteSignal.observationRemainderConstant (coloredObserved d k hd)) ^ (4 / 9 : ℝ) *
        (1 + (((Fintype.card (ScalarCoordinate d k) : ℝ) + 1) * B) ^ 2) ^ 4 := by
  unfold starTaylorCoefficient
  rw [Real.mul_rpow (NormalizedFiniteSignal.observationRemainderConstant_pos _).le
    (pow_nonneg (by positivity) _), ← Real.rpow_natCast_mul (by positivity)]
  congr 1
  convert Real.rpow_natCast (1 + (((Fintype.card (ScalarCoordinate d k) : ℝ) + 1) * B) ^ 2) 4 using 1 <;> norm_num

/-- The Gaussian analytic part of the source entropy-to-quartic theorem is
fully discharged for actual finite signals. The displayed scale restrictions
are the true smoothing domain; the only remaining numerical input is the
finite graph entropy deficit bound. -/
theorem uniform_constructed_optimized_quartic {S : Type*} [Fintype S]
    (d k : ℕ) (hd : 3 ≤ d) (K : Set (StarParameters k)) (hK : IsCompact K)
    (hbulk : ∀ c ∈ K, ∀ i, (c.val i) ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ c ∈ K,
      ∀ (D : NormalizedFiniteSignal (ScalarCoordinate d k) S) (B epsilon : ℝ),
      0 ≤ B → 0 < epsilon →
      (∀ s, coordinateL1 (D.signal s) ≤ B) →
      let a := (epsilon / starTaylorCoefficient d k (by omega) B) ^ ((9 : ℝ)⁻¹)
      a ≤ 1 / 2 → a * (((Fintype.card (ScalarCoordinate d k) : ℝ) + 1) * B) ≤ 1 / 2 →
      ∀ f : Lp ℝ 2 (standardGaussian (ScalarCoordinate d k)),
      ((f : (ScalarCoordinate d k → ℝ) → ℝ) =ᵐ[standardGaussian (ScalarCoordinate d k)]
        fun z => D.density a z - 1) →
      (coloredGaussianFrameSystem d k (by omega) c.val c.property).Admissible f →
      D.observationEntropyDeficit (coloredObservationMatrix d k (by omega))
        (coloredObservationMatrix_orthogonal d k (by omega)) (coloredObserved d k (by omega)) a ≤ epsilon →
      ‖signalChaos D.weight D.signal 4‖ ≤
        (2 / Real.sqrt kappa) *
          (NormalizedFiniteSignal.observationRemainderConstant (coloredObserved d k (by omega))) ^ (4 / 9 : ℝ) *
          (1 + (((Fintype.card (ScalarCoordinate d k) : ℝ) + 1) * B) ^ 2) ^ 4 *
          epsilon ^ (1 / 18 : ℝ) := by
  obtain ⟨κ, hκ, hgap⟩ := uniform_actual_Mehler_fourth_lower (S := S) d k hd K hK hbulk
  refine ⟨κ, hκ, ?_⟩
  intro c hc D B epsilon hB hepsilon hsignal a ha1 hsmall f hf hadm hdelta
  have hA := starTaylorCoefficient_pos d k (by omega) B
  have hap : 0 < a := (ninth_root_balance epsilon (starTaylorCoefficient d k (by omega) B) hepsilon hA).1
  have hden : 0 < 1 - a ^ 2 := by nlinarith [mul_nonneg hap.le (show 0 ≤ 1 / 2 - a by linarith)]
  have hQ := hgap c hc D.weight D.signal D.total a hden f hf hadm
  have hE := D.observationEntropyDeficit_quadratic_bound
    (coloredObservationMatrix d k (by omega)) (coloredObservationMatrix_orthogonal d k (by omega))
    (coloredObserved d k (by omega)) B a hB hap.le ha1 hsmall hsignal f hf
  have hlow : κ / 2 * a ^ 8 * ‖signalChaos D.weight D.signal 4‖ ^ 2 -
      starTaylorCoefficient d k (by omega) B * a ^ 9 ≤
      D.observationEntropyDeficit (coloredObservationMatrix d k (by omega))
        (coloredObservationMatrix_orthogonal d k (by omega)) (coloredObserved d k (by omega)) a := by
    have he := (abs_le.mp hE).1
    change κ * a ^ 8 * ‖signalChaos D.weight D.signal 4‖ ^ 2 ≤
      gaussianChannelDefect (coloredObservationMatrix d k (by omega))
        (coloredObservationMatrix_orthogonal d k (by omega)) (coloredObserved d k (by omega)) f at hQ
    change _ - starTaylorCoefficient d k (by omega) B * a ^ 9 ≤ _
    change -(starTaylorCoefficient d k (by omega) B * a ^ 9) ≤ _ at he
    linarith
  have h := optimized_quartic_norm epsilon
    (D.observationEntropyDeficit (coloredObservationMatrix d k (by omega))
      (coloredObservationMatrix_orthogonal d k (by omega)) (coloredObserved d k (by omega)) a)
    κ (starTaylorCoefficient d k (by omega) B) ‖signalChaos D.weight D.signal 4‖
    hκ hepsilon hA (norm_nonneg _) hdelta hlow
  rw [starTaylorCoefficient_power] at h
  convert h using 1; ring

end GeneralizedBulk.Entropy.Channel
