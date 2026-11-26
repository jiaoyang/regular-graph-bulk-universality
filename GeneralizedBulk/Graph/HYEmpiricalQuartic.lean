import GeneralizedBulk.Graph.EmpiricalFourthMoments

/-! The actual HY delocalization event supplies the empirical entropy-to-quartic
estimate's polylogarithmic signal bound. HY remains an external input. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Entropy.Channel GeneralizedBulk.Entropy.Mehler
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

def empiricalQuarticRate (d k : ℕ) (hd : 2 ≤ d) (κ B epsilon : ℝ) : ℝ :=
  (2 / Real.sqrt κ) *
    (NormalizedFiniteSignal.observationRemainderConstant (coloredObserved d k hd)) ^ (4 / 9 : ℝ) *
    (1 + (((Fintype.card (ScalarCoordinate d k) : ℝ) + 1) * B) ^ 2) ^ 4 *
    epsilon ^ (1 / 18 : ℝ)

/-- On the actual externally supplied HY good event, the concrete empirical
quartic norm obeys the proved entropy rate with an explicit polylogarithmic
signal bound. Only the finite-graph numeric entropy deficit remains an input. -/
theorem HY_uniform_empirical_quartic {P : Measure Ω} [IsProbabilityMeasure P]
    {quantile : ∀ n, Fin (N n) → ℝ} (H : HYCoarseInput D P quantile)
    {k : ℕ} (hd : 3 ≤ d) (K : Set (StarParameters k)) (hK : IsCompact K)
    (hKbulk : ∀ c ∈ K, ∀ a, (c.val a) ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ n, H.events.threshold ≤ n → ∀ ω, ω ∈ H.events.good n →
      ∀ (selection : Fin k → Fin (N n)) (hinj : Function.Injective selection)
      (hbulk : ∀ a, (D.eigenvalue n ω (selection a) / d) ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2),
      D.empiricalParameters n ω hd selection hbulk ∈ K → ∀ epsilon : ℝ, 0 < epsilon →
      let Bwhite := empiricalWhitenedBound d k (H.events.constant * Real.log (N n) ^ H.logPower)
      let a := (epsilon / starTaylorCoefficient d k (by omega) Bwhite) ^ ((9 : ℝ)⁻¹)
      a ≤ 1 / 2 → a * (((Fintype.card (ScalarCoordinate d k) : ℝ) + 1) * Bwhite) ≤ 1 / 2 →
      (D.empiricalBulkSignal n ω hd selection hinj hbulk).observationEntropyDeficit
        (coloredObservationMatrix d k (by omega)) (coloredObservationMatrix_orthogonal d k (by omega))
          (coloredObserved d k (by omega)) a ≤ epsilon →
      ‖signalChaos (D.empiricalBulkSignal n ω hd selection hinj hbulk).weight
        (D.empiricalBulkSignal n ω hd selection hinj hbulk).signal 4‖ ≤
        empiricalQuarticRate d k (by omega) κ Bwhite epsilon := by
  obtain ⟨κ, hκ, hdet⟩ := D.uniform_empirical_quartic hd K hK hKbulk
  refine ⟨κ, hκ, ?_⟩
  intro n hn ω hgood selection hinj hbulk hc epsilon hepsilon Bwhite a ha1 hsmall hdelta
  have hN : (1 : ℝ) ≤ N n := by exact_mod_cast D.size_pos n
  have hB : 0 ≤ H.events.constant * Real.log (N n) ^ H.logPower :=
    mul_nonneg H.events.constant_pos.le (pow_nonneg (Real.log_nonneg hN) _)
  have hU (a : Fin k) (v : Fin (N n)) : Real.sqrt (N n) * |D.eigenvector n ω (selection a) v| ≤
      H.events.constant * Real.log (N n) ^ H.logPower := by
    apply H.delocalization n hn ω hgood _ (D.eigenvalue n ω (selection a)) ?_ ?_ v
    · simpa only [pow_two, ite_true] using D.orthonormal n ω (selection a) (selection a)
    · exact D.eigen_equation n ω (selection a)
  exact hdet n ω selection hinj hbulk hc _ epsilon hB hepsilon hU ha1 hsmall hdelta

end GeneralizedBulk.External.RegularSpectralData
