import GeneralizedBulk.Graph.EmpiricalQuarticRates

/-! The actual HY empirical fourth moments with all Taylor domain and
polynomial prefactor restrictions discharged. The entropy premise is the
literal finite-signal deficit that finite graph counting supplies. -/
noncomputable section
open Filter MeasureTheory
open scoped Topology
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Entropy.Channel GeneralizedBulk.Entropy.Mehler
open GeneralizedBulk.Entropy.ChannelRates
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

set_option maxHeartbeats 2000000 in
theorem HY_uniform_fourth_moment_rate_of_entropy {P : Measure Ω} [IsProbabilityMeasure P]
    {quantile : ∀ n,Fin (N n) → ℝ} (H : HYCoarseInput D P quantile)
    {k : ℕ} (hd : 3 ≤ d) (K : Set (StarParameters k)) (hK : IsCompact K)
    (hKbulk : ∀ c ∈ K,∀ a,(c.val a)^2 < 4*((d : ℝ)-1)/(d : ℝ)^2)
    (γ : ℝ) (hγ : 0 < γ) :
    ∀ᶠ n : ℕ in atTop,∀ ω ∈ H.events.good n,
      ∀ (selection : Fin k → Fin (N n)) (hinj : Function.Injective selection)
        (hbulk : ∀ a,(D.eigenvalue n ω (selection a)/(d : ℝ))^2 < 4*((d : ℝ)-1)/(d : ℝ)^2),
      D.empiricalParameters n ω hd selection hbulk ∈ K →
      let epsilon := (N n : ℝ)^(-γ)
      let Bwhite := empiricalWhitenedBound d k (H.events.constant*Real.log (N n : ℝ)^H.logPower)
      let a := (epsilon/starTaylorCoefficient d k (by omega) Bwhite)^((9 : ℝ)⁻¹)
      (D.empiricalBulkSignal n ω hd selection hinj hbulk).observationEntropyDeficit
        (coloredObservationMatrix d k (by omega)) (coloredObservationMatrix_orthogonal d k (by omega))
        (coloredObserved d k (by omega)) a ≤ epsilon →
      ∀ j1 j2 j3 j4 : Fin k × Fin (d+1),
        |D.empiricalFourthWickDiscrepancy n ω selection j1 j2 j3 j4| ≤ (N n : ℝ)^(-γ/36) := by
  obtain ⟨κ,hκ,hw⟩ := D.HY_uniform_empirical_fourth_moments H hd K hK hKbulk
  let B : ℕ → ℝ := fun L => empiricalWhitenedBound d k (H.events.constant*Real.log (L : ℝ)^H.logPower)
  let C : ℝ := ((Fintype.card (ScalarCoordinate d k) : ℝ)*((k : ℝ)*d*((d : ℝ)+1)))*H.events.constant
  have hB : B =O[atTop] fun L => C*Real.log (L : ℝ)^H.logPower :=
    empiricalWhitenedBound_polylog_bigO d k H.events.constant H.logPower
  have hdomains := D.size_tendsto.eventually
    (eventually_ninthRootScale_domains d k (by omega) B C γ H.logPower hγ hB)
  have hrate := D.size_tendsto.eventually
    (eventually_empiricalQuarticRate_polynomial d k (by omega) κ C γ H.logPower B hγ hB)
  filter_upwards [hdomains,hrate,eventually_ge_atTop H.events.threshold] with n hdomains hrate hn
    ω hω selection hinj hbulk hparameter epsilon Bwhite a hdelta j1 j2 j3 j4
  have hε : 0 < epsilon := Real.rpow_pos_of_pos (Nat.cast_pos.mpr (D.size_pos n)) _
  exact (hw n hn ω hω selection hinj hbulk hparameter epsilon hε hdomains.1 hdomains.2
    hdelta j1 j2 j3 j4).trans hrate

end GeneralizedBulk.External.RegularSpectralData
