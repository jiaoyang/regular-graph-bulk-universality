import GeneralizedBulk.Graph.BulkEntropyDeficit
import GeneralizedBulk.Graph.HYUniformDeficitWick

/-! The finite regular-graph fourth-Wick estimate is now proved on one actual
common graph event. Counting and Gaussian entropy analysis supply the entire
entropy deficit; BS and HY are the only external theorem inputs. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Gaussian GeneralizedBulk.Entropy.Channel GeneralizedBulk.Entropy.Mehler
open GeneralizedBulk.Entropy.ChannelRates GeneralizedBulk.KestenMcKay GeneralizedBulk.Graph
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

set_option maxHeartbeats 2000000 in
theorem HY_common_event_fourth_moments {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : 3 ≤ d) (Hc : HYCoarseInput D P (D.kestenMcKayQuantile (by exact_mod_cast hd)))
    (k : ℕ) (hk : 0 < k) (K : Set ℝ) (hK : IsCompact K)
    (hbulk : ∀ E ∈ K,E^2 < 4*((d : ℝ)-1)) (c0 : ℝ)
    (hcchannel : c0 < channelNoiseExponent (channelTheta k d))
    (hcrigidity : c0 < Hc.rigidity_exponent) (hcsmall : c0 ≤ 1/16)
    (H : HYLocalStarInput D P K c0 (treeGreenStar d (by exact_mod_cast hd))) :
    ∀ᶠ n in atTop,∀ ω ∈ D.commonEntropyGood P k Hc.events H.events n,
      ∀ (selection : Fin k → Fin (N n)) (hinj : Function.Injective selection)
        (henergy : ∀ a,D.eigenvalue n ω (selection a) ∈ K),
      ∀ j1 j2 j3 j4 : Fin k × Fin (d+1),
        |D.empiricalFourthWickDiscrepancy n ω selection j1 j2 j3 j4| ≤
          (N n : ℝ)^(-bulkEntropyExponent k d Hc.rigidity_exponent H.local_exponent c0/36) := by
  let γ := bulkEntropyExponent k d Hc.rigidity_exponent H.local_exponent c0
  have hγ : 0 < γ := bulkEntropyExponent_pos k d _ _ _ H.local_exponent_pos
    H.height_range.1 hcrigidity (by linarith [H.height_range.2])
  have hfourth := D.HY_uniform_fourth_moment_rate_of_uniform_entropy Hc k hd K hK hbulk γ hγ
  have hdelta := D.HY_empirical_entropy_deficit_eventually hd Hc k hk K hK hbulk c0
    hcchannel hcrigidity hcsmall H
  filter_upwards [hfourth,hdelta] with n hfourth hdelta ω hω selection hinj henergy
  apply hfourth ω hω.1.1 selection hinj henergy
  intro a ha
  exact hdelta ω hω selection hinj henergy a ha.1 ha.2

set_option maxHeartbeats 2000000 in
/-- The common fourth-moment event is measurable, its failure probability
vanishes under the actual uniform graph model, and every selected bulk
channel has the proved uniform Wick error. No fourth-moment or entropy
certificate appears among the assumptions. -/
theorem HY_common_fourth_moment_event {P : Measure Ω} [IsProbabilityMeasure P]
    (hUniform : ∀ n,Measure.map (D.spectralRegularGraph n) P=regularGraphLaw (N n) d)
    (hd : 3 ≤ d) (Hc : HYCoarseInput D P (D.kestenMcKayQuantile (by exact_mod_cast hd)))
    (k : ℕ) (hk : 0 < k) (K : Set ℝ) (hK : IsCompact K)
    (hbulk : ∀ E ∈ K,E^2 < 4*((d : ℝ)-1)) (c0 : ℝ)
    (hcchannel : c0 < channelNoiseExponent (channelTheta k d))
    (hcrigidity : c0 < Hc.rigidity_exponent) (hcsmall : c0 ≤ 1/16)
    (H : HYLocalStarInput D P K c0 (treeGreenStar d (by exact_mod_cast hd))) :
    (∀ n,MeasurableSet (D.commonEntropyGood P k Hc.events H.events n)) ∧
    Tendsto (fun n => P.real (D.commonEntropyGood P k Hc.events H.events n)ᶜ) atTop (nhds 0) ∧
    ∀ᶠ n in atTop,∀ ω ∈ D.commonEntropyGood P k Hc.events H.events n,
      ∀ (selection : Fin k → Fin (N n)) (hinj : Function.Injective selection)
        (henergy : ∀ a,D.eigenvalue n ω (selection a) ∈ K),
      ∀ j1 j2 j3 j4 : Fin k × Fin (d+1),
        |D.empiricalFourthWickDiscrepancy n ω selection j1 j2 j3 j4| ≤
          (N n : ℝ)^(-bulkEntropyExponent k d Hc.rigidity_exponent H.local_exponent c0/36) := by
  exact ⟨D.measurableSet_commonEntropyGood P k Hc.events H.events,
    D.commonEntropyGood_failure_tendsto_zero hUniform (by omega) k Hc.events H.events,
    D.HY_common_event_fourth_moments hd Hc k hk K hK hbulk c0 hcchannel hcrigidity hcsmall H⟩

theorem HY_common_event_fourth_le_one {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : 3 ≤ d) (Hc : HYCoarseInput D P (D.kestenMcKayQuantile (by exact_mod_cast hd)))
    (k : ℕ) (hk : 0 < k) (K : Set ℝ) (hK : IsCompact K)
    (hbulk : ∀ E ∈ K,E^2 < 4*((d : ℝ)-1)) (c0 : ℝ)
    (hcchannel : c0 < channelNoiseExponent (channelTheta k d))
    (hcrigidity : c0 < Hc.rigidity_exponent) (hcsmall : c0 ≤ 1/16)
    (H : HYLocalStarInput D P K c0 (treeGreenStar d (by exact_mod_cast hd))) :
    ∀ᶠ n in atTop,∀ ω ∈ D.commonEntropyGood P k Hc.events H.events n,
      ∀ (selection : Fin k → Fin (N n)) (hinj : Function.Injective selection)
        (henergy : ∀ a,D.eigenvalue n ω (selection a) ∈ K),
      ∀ j1 j2 j3 j4 : Fin k × Fin (d+1),
        |D.empiricalFourthWickDiscrepancy n ω selection j1 j2 j3 j4| ≤ 1 := by
  have hγ := bulkEntropyExponent_pos k d Hc.rigidity_exponent H.local_exponent c0
    H.local_exponent_pos H.height_range.1 hcrigidity (by linarith [H.height_range.2])
  filter_upwards [D.HY_common_event_fourth_moments hd Hc k hk K hK hbulk c0 hcchannel hcrigidity hcsmall H]
    with n hn ω hω selection hinj henergy j1 j2 j3 j4
  exact (hn ω hω selection hinj henergy j1 j2 j3 j4).trans
    (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (D.size_pos n)) (by linarith))

end GeneralizedBulk.External.RegularSpectralData
