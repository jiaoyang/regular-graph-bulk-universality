import GeneralizedBulk.Graph.CompactEnergyParameters

/-! The uniform entropy-channel estimate applies at the internally chosen
optimized Taylor scale. No scale or coefficient assumptions remain in the
resulting physical-slot Wick estimate. -/
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Entropy.Channel GeneralizedBulk.Entropy.Mehler
open GeneralizedBulk.Entropy.ChannelRates
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

set_option maxHeartbeats 2000000 in
theorem HY_uniform_fourth_moment_rate_of_uniform_entropy {P : Measure Ω} [IsProbabilityMeasure P]
    {quantile : ∀ n,Fin (N n) → ℝ} (H : HYCoarseInput D P quantile)
    (k : ℕ) (hd : 3 ≤ d) (K : Set ℝ) (hK : IsCompact K)
    (hbulkK : ∀ E ∈ K,E^2 < 4*((d : ℝ)-1)) (γ : ℝ) (hγ : 0 < γ) :
    ∀ᶠ n : ℕ in atTop,∀ ω ∈ H.events.good n,
      ∀ (selection : Fin k → Fin (N n)) (hinj : Function.Injective selection)
        (henergy : ∀ a,D.eigenvalue n ω (selection a) ∈ K),
      let hbulk := fun a => energy_div_degree_bulk d hd _ (hbulkK _ (henergy a))
      (∀ a ∈ Icc (0 : ℝ) (1/2),
        (D.empiricalBulkSignal n ω hd selection hinj hbulk).observationEntropyDeficit
          (coloredObservationMatrix d k (by omega)) (coloredObservationMatrix_orthogonal d k (by omega))
          (coloredObserved d k (by omega)) a ≤ (N n : ℝ)^(-γ)) →
      ∀ j1 j2 j3 j4 : Fin k × Fin (d+1),
        |D.empiricalFourthWickDiscrepancy n ω selection j1 j2 j3 j4| ≤ (N n : ℝ)^(-γ/36) := by
  let B : ℕ → ℝ := fun L => empiricalWhitenedBound d k (H.events.constant*Real.log (L : ℝ)^H.logPower)
  let C : ℝ := ((Fintype.card (ScalarCoordinate d k) : ℝ)*((k : ℝ)*d*((d : ℝ)+1)))*H.events.constant
  have hB : B =O[atTop] fun L => C*Real.log (L : ℝ)^H.logPower :=
    empiricalWhitenedBound_polylog_bigO d k H.events.constant H.logPower
  have hdomains := D.size_tendsto.eventually
    (eventually_ninthRootScale_domains d k (by omega) B C γ H.logPower hγ hB)
  have hw := D.HY_uniform_fourth_moment_rate_on_energy_window H k hd K hK hbulkK γ hγ
  filter_upwards [hdomains,hw] with n hdomain hw ω hω selection hinj henergy hbulk hdelta
  apply hw ω hω selection hinj henergy
  let a := ((N n : ℝ)^(-γ)/starTaylorCoefficient d k (by omega) (B (N n)))^((9 : ℝ)⁻¹)
  have ha : 0 ≤ a := Real.rpow_nonneg (div_nonneg
    (Real.rpow_nonneg (Nat.cast_nonneg _) _) (starTaylorCoefficient_pos d k (by omega) _).le) _
  exact hdelta a ⟨ha,hdomain.1⟩

end GeneralizedBulk.External.RegularSpectralData
