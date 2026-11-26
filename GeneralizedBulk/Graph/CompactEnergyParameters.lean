import GeneralizedBulk.Graph.HYFourthMomentRate

/-! Compact physical energy windows canonically give the compact normalized
Gaussian-channel parameter sets required by the actual quartic estimate. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Entropy.Channel GeneralizedBulk.Entropy.Mehler
open GeneralizedBulk.Entropy.ChannelRates

lemma energy_div_degree_bulk (d : ℕ) (hd : 3 ≤ d) (E : ℝ)
    (hE : E^2 < 4*((d : ℝ)-1)) :
    (E/(d : ℝ))^2 < 4*((d : ℝ)-1)/(d : ℝ)^2 := by
  rw [div_pow]
  exact div_lt_div_of_pos_right hE (sq_pos_of_pos (by exact_mod_cast (show 0 < d by omega)))

def energyTupleParameters (d k : ℕ) (hd : 3 ≤ d) (K : Set ℝ)
    (hbulk : ∀ E ∈ K,E^2 < 4*((d : ℝ)-1)) (energy : Fin k → K) : StarParameters k :=
  ⟨fun a => (energy a).val/(d : ℝ),fun a =>
    (bulk_rho_lower d hd _ (energy_div_degree_bulk d hd _ (hbulk _ (energy a).property))).1⟩

def compactEnergyParameters (d k : ℕ) (hd : 3 ≤ d) (K : Set ℝ)
    (hbulk : ∀ E ∈ K,E^2 < 4*((d : ℝ)-1)) : Set (StarParameters k) :=
  range (energyTupleParameters d k hd K hbulk)

theorem isCompact_compactEnergyParameters (d k : ℕ) (hd : 3 ≤ d)
    (K : Set ℝ) (hK : IsCompact K) (hbulk : ∀ E ∈ K,E^2 < 4*((d : ℝ)-1)) :
    IsCompact (compactEnergyParameters d k hd K hbulk) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc : Continuous (energyTupleParameters d k hd K hbulk) := by
    apply Continuous.subtype_mk
    exact continuous_pi (fun a => (continuous_subtype_val.comp (continuous_apply a)).div_const (d : ℝ))
  exact isCompact_range hc

theorem compactEnergyParameters_bulk (d k : ℕ) (hd : 3 ≤ d)
    (K : Set ℝ) (hbulk : ∀ E ∈ K,E^2 < 4*((d : ℝ)-1)) :
    ∀ c ∈ compactEnergyParameters d k hd K hbulk,∀ a,
      (c.val a)^2 < 4*((d : ℝ)-1)/(d : ℝ)^2 := by
  rintro c ⟨energy,rfl⟩ a
  exact energy_div_degree_bulk d hd _ (hbulk _ (energy a).property)

variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

theorem empiricalParameters_mem_compactEnergyParameters (k : ℕ) (hd : 3 ≤ d)
    (K : Set ℝ) (hbulkK : ∀ E ∈ K,E^2 < 4*((d : ℝ)-1))
    (n : ℕ) (ω : Ω) (selection : Fin k → Fin (N n))
    (henergy : ∀ a,D.eigenvalue n ω (selection a) ∈ K) :
    D.empiricalParameters n ω hd selection
      (fun a => energy_div_degree_bulk d hd _ (hbulkK _ (henergy a))) ∈
      compactEnergyParameters d k hd K hbulkK := by
  refine ⟨fun a => ⟨D.eigenvalue n ω (selection a),henergy a⟩,?_⟩
  rfl

set_option maxHeartbeats 2000000 in
theorem HY_uniform_fourth_moment_rate_on_energy_window {P : Measure Ω} [IsProbabilityMeasure P]
    {quantile : ∀ n,Fin (N n) → ℝ} (H : HYCoarseInput D P quantile)
    (k : ℕ) (hd : 3 ≤ d) (K : Set ℝ) (hK : IsCompact K)
    (hbulkK : ∀ E ∈ K,E^2 < 4*((d : ℝ)-1)) (γ : ℝ) (hγ : 0 < γ) :
    ∀ᶠ n : ℕ in atTop,∀ ω ∈ H.events.good n,
      ∀ (selection : Fin k → Fin (N n)) (hinj : Function.Injective selection)
        (henergy : ∀ a,D.eigenvalue n ω (selection a) ∈ K),
      let hbulk := fun a => energy_div_degree_bulk d hd _ (hbulkK _ (henergy a))
      let epsilon := (N n : ℝ)^(-γ)
      let Bwhite := empiricalWhitenedBound d k (H.events.constant*Real.log (N n : ℝ)^H.logPower)
      let a := (epsilon/starTaylorCoefficient d k (by omega) Bwhite)^((9 : ℝ)⁻¹)
      (D.empiricalBulkSignal n ω hd selection hinj hbulk).observationEntropyDeficit
        (coloredObservationMatrix d k (by omega)) (coloredObservationMatrix_orthogonal d k (by omega))
        (coloredObserved d k (by omega)) a ≤ epsilon →
      ∀ j1 j2 j3 j4 : Fin k × Fin (d+1),
        |D.empiricalFourthWickDiscrepancy n ω selection j1 j2 j3 j4| ≤ (N n : ℝ)^(-γ/36) := by
  have h := D.HY_uniform_fourth_moment_rate_of_entropy H hd
    (compactEnergyParameters d k hd K hbulkK) (isCompact_compactEnergyParameters d k hd K hK hbulkK)
    (compactEnergyParameters_bulk d k hd K hbulkK) γ hγ
  filter_upwards [h] with n hn ω hω selection hinj henergy hbulk epsilon Bwhite a hdelta
  exact hn ω hω selection hinj hbulk
    (D.empiricalParameters_mem_compactEnergyParameters k hd K hbulkK n ω selection henergy) hdelta

end GeneralizedBulk.External.RegularSpectralData
