import GeneralizedBulk.Graph.EmpiricalSignalBounds
import GeneralizedBulk.Graph.EmpiricalEdgeReversal
import GeneralizedBulk.Entropy.MixedWickMoments

/-! Actual empirical regular-graph fourth-moment control. The only numerical
input left here is the finite-graph entropy deficit estimate. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Entropy.Channel GeneralizedBulk.Entropy.Mehler GeneralizedBulk.Entropy.Hermite
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

/-- The actual selected correlations in the open Gaussian channel domain. -/
def empiricalParameters {k : ℕ} (hd : 3 ≤ d) (selection : Fin k → Fin (N n))
    (hbulk : ∀ a, (D.eigenvalue n ω (selection a) / d) ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2) :
    StarParameters k :=
  ⟨fun a => D.eigenvalue n ω (selection a) / d,
    fun a => (bulk_rho_lower d hd _ (hbulk a)).1⟩

theorem empiricalEigenvalue_abs_lt_d {k : ℕ} (hd : 3 ≤ d) (selection : Fin k → Fin (N n))
    (hbulk : ∀ a, (D.eigenvalue n ω (selection a) / d) ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2) :
    ∀ a, |D.eigenvalue n ω (selection a)| < d := by
  intro a
  have hc := (D.empiricalParameters n ω hd selection hbulk).property a
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  change |D.eigenvalue n ω (selection a) / (d : ℝ)| < 1 at hc
  rw [abs_div, abs_of_pos hdpos, div_lt_one hdpos] at hc
  exact hc

def empiricalBulkSignal {k : ℕ} (hd : 3 ≤ d) (selection : Fin k → Fin (N n))
    (hinj : Function.Injective selection)
    (hbulk : ∀ a, (D.eigenvalue n ω (selection a) / d) ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2) :
    NormalizedFiniteSignal (ScalarCoordinate d k) (EmpiricalStarSample d (N n)) :=
  D.empiricalNormalizedSignal n ω (by omega) selection hinj (D.empiricalEigenvalue_abs_lt_d n ω hd selection hbulk)

def empiricalWhitenedBound (d k : ℕ) (B : ℝ) : ℝ :=
  (Fintype.card (ScalarCoordinate d k) : ℝ) * ((k : ℝ) * d * ((d : ℝ) + 1) * B)

theorem empiricalBulkSignal_bound {k : ℕ} (hd : 3 ≤ d) (selection : Fin k → Fin (N n))
    (hinj : Function.Injective selection)
    (hbulk : ∀ a, (D.eigenvalue n ω (selection a) / d) ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (B : ℝ) (hB : 0 ≤ B)
    (hU : ∀ a v, Real.sqrt (N n) * |D.eigenvector n ω (selection a) v| ≤ B) :
    ∀ s, coordinateL1 ((D.empiricalBulkSignal n ω hd selection hinj hbulk).signal s) ≤ empiricalWhitenedBound d k B :=
  D.empiricalNormalizedSignal_bound n ω hd selection hinj _ hbulk B hB hU

theorem empiricalBulkSignal_admissible {k : ℕ} (hd : 3 ≤ d) (selection : Fin k → Fin (N n))
    (hinj : Function.Injective selection)
    (hbulk : ∀ a, (D.eigenvalue n ω (selection a) / d) ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (a : ℝ) (ha : 0 < 1 - a ^ 2)
    (f : Lp ℝ 2 (standardGaussian (ScalarCoordinate d k)))
    (hf : (f : (ScalarCoordinate d k → ℝ) → ℝ) =ᵐ[standardGaussian (ScalarCoordinate d k)]
      fun x => (D.empiricalBulkSignal n ω hd selection hinj hbulk).density a x - 1) :
    (coloredGaussianFrameSystem d k (by omega) (D.empiricalParameters n ω hd selection hbulk).val
      (D.empiricalParameters n ω hd selection hbulk).property).Admissible f :=
  D.empiricalNormalizedSignal_admissible n ω (by omega) selection hinj _ a ha f hf

/-- The concrete finite-graph signal satisfies the actual optimized Gaussian
quartic estimate. No whitening, normalization, or reversal assumption remains. -/
theorem uniform_empirical_quartic {k : ℕ} (hd : 3 ≤ d)
    (K : Set (StarParameters k)) (hK : IsCompact K)
    (hKbulk : ∀ c ∈ K, ∀ a, (c.val a) ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ n ω (selection : Fin k → Fin (N n)) (hinj : Function.Injective selection)
      (hbulk : ∀ a, (D.eigenvalue n ω (selection a) / d) ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2),
      D.empiricalParameters n ω hd selection hbulk ∈ K → ∀ B epsilon : ℝ, 0 ≤ B → 0 < epsilon →
      (∀ a v, Real.sqrt (N n) * |D.eigenvector n ω (selection a) v| ≤ B) →
      let Bwhite := empiricalWhitenedBound d k B
      let a := (epsilon / starTaylorCoefficient d k (by omega) Bwhite) ^ ((9 : ℝ)⁻¹)
      a ≤ 1 / 2 → a * (((Fintype.card (ScalarCoordinate d k) : ℝ) + 1) * Bwhite) ≤ 1 / 2 →
      (D.empiricalBulkSignal n ω hd selection hinj hbulk).observationEntropyDeficit
        (coloredObservationMatrix d k (by omega)) (coloredObservationMatrix_orthogonal d k (by omega))
          (coloredObserved d k (by omega)) a ≤ epsilon →
      ‖signalChaos (D.empiricalBulkSignal n ω hd selection hinj hbulk).weight
        (D.empiricalBulkSignal n ω hd selection hinj hbulk).signal 4‖ ≤
        (2 / Real.sqrt κ) *
          (NormalizedFiniteSignal.observationRemainderConstant (coloredObserved d k (by omega))) ^ (4 / 9 : ℝ) *
          (1 + (((Fintype.card (ScalarCoordinate d k) : ℝ) + 1) * Bwhite) ^ 2) ^ 4 *
          epsilon ^ (1 / 18 : ℝ) := by
  obtain ⟨κ, hκ, hgap⟩ := uniform_actual_defect_fourth_lower d k hd K hK hKbulk
  refine ⟨κ, hκ, ?_⟩
  intro n ω selection hinj hbulk hc B epsilon hB hepsilon hU Bwhite a ha1 hsmall hdelta
  let Sg := D.empiricalBulkSignal n ω hd selection hinj hbulk
  let c := D.empiricalParameters n ω hd selection hbulk
  have hBw : 0 ≤ Bwhite := by dsimp [Bwhite, empiricalWhitenedBound]; positivity
  have hsig := D.empiricalBulkSignal_bound n ω hd selection hinj hbulk B hB hU
  let M := ((Fintype.card (ScalarCoordinate d k) : ℝ) + 1) * Bwhite
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hBM : Bwhite ≤ M := by
    dsimp [M]
    nlinarith [mul_nonneg (Nat.cast_nonneg (Fintype.card (ScalarCoordinate d k))) hBw]
  have hsigM : ∀ s, coordinateL1 (Sg.signal s) ≤ M := fun s => (hsig s).trans hBM
  have hap : 0 < a := (GeneralizedBulk.Entropy.ninth_root_balance epsilon
    (starTaylorCoefficient d k (by omega) Bwhite) hepsilon (starTaylorCoefficient_pos d k (by omega) Bwhite)).1
  have hden : 0 < 1 - a ^ 2 := by nlinarith [mul_nonneg hap.le (show 0 ≤ 1 / 2 - a by linarith)]
  let f := Sg.centeredL2 M a hM hap.le ha1 hsmall hsigM
  have hf := Sg.centeredL2_ae M a hM hap.le ha1 hsmall hsigM
  have hadm := D.empiricalBulkSignal_admissible n ω hd selection hinj hbulk a hden f hf
  have hcoerc := hgap c hc f hadm (centered_density_integral_zero Sg.weight Sg.signal Sg.total a hden f hf)
  have hproj := chaosComponent_centered_density Sg.weight Sg.signal a hden f hf 4 (by decide)
  have hnorm : ‖chaosComponent (ScalarCoordinate d k) f 4‖ ^ 2 = a ^ 8 * ‖signalChaos Sg.weight Sg.signal 4‖ ^ 2 := by
    change ‖(chaosComponent (ScalarCoordinate d k) f 4 : Lp ℝ 2 (standardGaussian (ScalarCoordinate d k)))‖ ^ 2 = _
    rw [hproj, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, ← pow_mul]
    rfl
  rw [hnorm] at hcoerc
  have hE := Sg.observationEntropyDeficit_quadratic_bound (coloredObservationMatrix d k (by omega))
    (coloredObservationMatrix_orthogonal d k (by omega)) (coloredObserved d k (by omega)) Bwhite a
      hBw hap.le ha1 hsmall hsig f hf
  have hlow : κ / 2 * a ^ 8 * ‖signalChaos Sg.weight Sg.signal 4‖ ^ 2 -
      starTaylorCoefficient d k (by omega) Bwhite * a ^ 9 ≤
      Sg.observationEntropyDeficit (coloredObservationMatrix d k (by omega))
        (coloredObservationMatrix_orthogonal d k (by omega)) (coloredObserved d k (by omega)) a := by
    have he := (abs_le.mp hE).1
    change -(starTaylorCoefficient d k (by omega) Bwhite * a ^ 9) ≤ _ at he
    change κ * (a ^ 8 * ‖signalChaos Sg.weight Sg.signal 4‖ ^ 2) ≤
      gaussianChannelDefect (coloredObservationMatrix d k (by omega))
        (coloredObservationMatrix_orthogonal d k (by omega)) (coloredObserved d k (by omega)) f at hcoerc
    linarith
  have hh := GeneralizedBulk.Entropy.optimized_quartic_norm epsilon
    (Sg.observationEntropyDeficit (coloredObservationMatrix d k (by omega))
      (coloredObservationMatrix_orthogonal d k (by omega)) (coloredObserved d k (by omega)) a)
      κ (starTaylorCoefficient d k (by omega) Bwhite) ‖signalChaos Sg.weight Sg.signal 4‖
      hκ hepsilon (starTaylorCoefficient_pos d k (by omega) Bwhite) (norm_nonneg _) hdelta hlow
  rw [starTaylorCoefficient_power] at hh
  convert hh using 1; ring

end GeneralizedBulk.External.RegularSpectralData
