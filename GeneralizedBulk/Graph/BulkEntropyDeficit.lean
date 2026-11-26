import GeneralizedBulk.Graph.PhysicalLocalEntropyRate
import GeneralizedBulk.Graph.EmpiricalDeficitComparison
import GeneralizedBulk.Entropy.BulkEntropyExponent

/-! The numerical empirical entropy deficit is proved on the actual common
graph event, uniformly over every selected bulk eigenchannel and every
Mehler scale in [0,1/2]. BS and HY remain external input theorems. -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Filter Set
open scoped BigOperators Topology Classical
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Gaussian GeneralizedBulk.Entropy GeneralizedBulk.Entropy.Channel
open GeneralizedBulk.Entropy.Mehler GeneralizedBulk.Entropy.ChannelRates GeneralizedBulk.KestenMcKay
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

theorem HY_empirical_entropy_deficit_eventually {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : 3 ≤ d) (Hc : HYCoarseInput D P (D.kestenMcKayQuantile (by exact_mod_cast hd)))
    (k : ℕ) (hk : 0 < k) (K : Set ℝ) (hK : IsCompact K)
    (hbulk : ∀ E ∈ K,E^2 < 4*((d : ℝ)-1)) (c0 : ℝ)
    (hcchannel : c0 < channelNoiseExponent (channelTheta k d))
    (hcrigidity : c0 < Hc.rigidity_exponent) (hcsmall : c0 ≤ 1/16)
    (H : HYLocalStarInput D P K c0 (treeGreenStar d (by exact_mod_cast hd))) :
    ∀ᶠ n in atTop,∀ ω ∈ D.commonEntropyGood P k Hc.events H.events n,
      ∀ (selection : Fin k → Fin (N n)) (hinj : Function.Injective selection)
        (henergy : ∀ j,D.eigenvalue n ω (selection j) ∈ K),
      let hEd := fun j => bulk_abs_lt_degree (by exact_mod_cast hd) _ (hbulk _ (henergy j))
      ∀ a : ℝ,0 ≤ a → a ≤ 1/2 →
      (D.empiricalNormalizedSignal n ω (by omega) selection hinj hEd).observationEntropyDeficit
        (coloredObservationMatrix d k (by omega)) (coloredObservationMatrix_orthogonal d k (by omega))
        (coloredObserved d k (by omega)) a ≤
        (N n : ℝ)^(-bulkEntropyExponent k d Hc.rigidity_exponent H.local_exponent c0) := by
  have hdR : (3:ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : 0 < d := by omega
  have hc0 := H.height_range.1
  have hc1 : c0 < 1 := by linarith
  obtain ⟨s,hs,hσ⟩ := diagonalBoundary_im_uniform d hdR K hK hbulk
  obtain ⟨eta0,he0,Cg,hCg,hglobal⟩ := D.HY_coloredResolventNoise_entropy_bulk_uniform hdR Hc k K hK hbulk
  have hchannel := D.HY_actual_physical_entropy_channel_eventually Hc k hdpos c0 hc0 hcchannel s 2 hs (by norm_num)
  have hstar := D.HY_physical_star_entropy_rate Hc hdR k hk K hK hbulk c0 hcsmall H
  have hedge := D.HY_physical_edge_entropy_rate Hc hdR k hk K hK hbulk c0 hcsmall H
  let Ad := |(d : ℝ)-radius d|+4*radius d
  have hglobalRate := D.size_tendsto.eventually (eventually_bulkNoiseError_polynomial
    (k : ℝ) Ad Cg Hc.rigidity_exponent c0 hc0 hcrigidity hc1)
  have htotalRate := D.size_tendsto.eventually (eventually_bulkEntropyError_polynomial k d Hc.rigidity_exponent H.local_exponent c0
    H.local_exponent_pos hc0 hcrigidity hc1)
  have hetaLimit : Tendsto (fun n => (N n : ℝ)^(-c0)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hc0).comp (tendsto_natCast_atTop_atTop.comp D.size_tendsto)
  have hetasmall : ∀ᶠ n in atTop,(N n : ℝ)^(-c0) ≤ eta0 :=
    (hetaLimit.eventually (eventually_lt_nhds he0)).mono (fun n hn => hn.le)
  filter_upwards [hchannel,hstar,hedge,hglobalRate,htotalRate,hetasmall,eventually_ge_atTop Hc.events.threshold]
    with n hnchannel hnstar hnedge hnglobal hntotal hneta hncoarse
  intro ω hω selection hinj henergy hEd a ha ha1
  rcases hω with ⟨⟨hωc,hωl⟩,hωcount⟩
  let energy := fun j => D.eigenvalue n ω (selection j)
  let eta := (N n : ℝ)^(-c0)
  let sigma := fun j => (diagonalBoundary d (energy j)).im
  let lo := channelCovarianceFloor (channelTheta k d) (N n)
  let A := D.coloredResolventCovarianceFactor n ω energy eta sigma
  have heta : 0 < eta := Real.rpow_pos_of_pos (Nat.cast_pos.mpr (D.size_pos n)) _
  have hsigma (j) : s ≤ sigma j ∧ sigma j ≤ 2 := hσ _ (henergy j)
  have hsigmaPos (j) : 0 < sigma j := hs.trans_le (hsigma j).1
  have hlo : 0 < lo := Real.rpow_pos_of_pos (Nat.cast_pos.mpr (D.size_pos n)) _
  obtain ⟨hlower,hchan⟩ := hnchannel ω hωc hωcount selection sigma hsigma
  have hGram : A*A.transpose=D.coloredResolventCovariance n ω energy eta sigma :=
    D.coloredResolventCovariance_factor n ω energy eta sigma heta hsigmaPos
  have hr := physicalSignalScale_range a ha ha1
  have hs0 := hnstar ω hωc hωl selection hinj henergy (Fin k × Fin (N n)) A lo hlo hlower hGram (physicalSignalScale a) hr
  let leaf : Fin d := ⟨0,hdpos⟩
  have he0' := hnedge ω hωc hωl selection hinj henergy (Fin k × Fin (N n)) A lo hlo hlower hGram
    (physicalSignalScale a) hr leaf
  have hg0 := hglobal n hncoarse ω hωc energy sigma henergy hsigmaPos eta heta hneta
  have hbase : (∑ j,((1/2 : ℝ)*(1+Real.log (2*Real.pi)+Real.log (eta/sigma j))-bulkPotential d (energy j)))=
      ∑ j,((1+Real.log (2*Real.pi)+Real.log (eta/sigma j))/2-bulkPotential d (energy j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hbase] at hg0
  have hg : |differentialEntropy (affineGaussianPDF 0 A)/(N n : ℝ)-
      ∑ j,((1+Real.log (2*Real.pi)+Real.log (eta/sigma j))/2-bulkPotential d (energy j))| ≤
      (N n : ℝ)^(-bulkNoiseExponent Hc.rigidity_exponent c0/2) := hg0.trans hnglobal
  have hbulkAbs (j) : |D.eigenvalue n ω (selection j)| < 2*Real.sqrt ((d : ℝ)-1) := by
    apply (sq_lt_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 2*Real.sqrt ((d : ℝ)-1))).mp
    have hsqrt := Real.sq_sqrt (show 0 ≤ (d : ℝ)-1 by linarith)
    nlinarith [hbulk _ (henergy j),sq_abs (D.eigenvalue n ω (selection j))]
  have hv : 0 < 1-a^2 := by nlinarith
  have hδ := D.empirical_deficit_le_of_physical_comparisons n ω hd (by omega) selection hinj hEd hbulkAbs
    a hv leaf eta heta sigma hsigmaPos lo hlo hlower
    ((N n : ℝ)^(-channelTheta k d/2))
    ((N n : ℝ)^(-localComparisonExponent H.local_exponent c0))
    ((N n : ℝ)^(-localComparisonExponent H.local_exponent c0))
    ((N n : ℝ)^(-bulkNoiseExponent Hc.rigidity_exponent c0/2)) (hchan (physicalSignalScale a) hr) hs0 he0' hg
  refine hδ.trans ?_
  convert hntotal using 1 <;> unfold bulkEntropyError <;> ring

end GeneralizedBulk.External.RegularSpectralData
