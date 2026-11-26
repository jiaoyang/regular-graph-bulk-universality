import GeneralizedBulk.Graph.PhysicalLocalEntropy
import GeneralizedBulk.Entropy.PhysicalLocalNumericRate

/-! Uniform polynomial local entropy comparison on the actual HY events.
The delocalization bound and all local smallness conditions are discharged. -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Filter Set
open scoped BigOperators Topology Classical
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Gaussian GeneralizedBulk.Covariance GeneralizedBulk.Entropy
open GeneralizedBulk.KestenMcKay GeneralizedBulk.Entropy.Channel GeneralizedBulk.Entropy.Mehler
open GeneralizedBulk.Entropy.ChannelRates
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

theorem HY_physical_star_entropy_rate {P : Measure Ω} [IsProbabilityMeasure P]
    {quantile : ∀ n,Fin (N n) → ℝ} (Hc : HYCoarseInput D P quantile)
    (hd : 3 ≤ (d : ℝ)) (k : ℕ) (hk : 0 < k) (K : Set ℝ) (hK : IsCompact K)
    (hbulk : ∀ E ∈ K,E^2 < 4*((d : ℝ)-1)) (c0 : ℝ) (hcsmall : c0 ≤ 1/16)
    (H : HYLocalStarInput D P K c0 (treeGreenStar d hd)) :
    ∀ᶠ n in atTop, ∀ ω ∈ Hc.events.good n,ω ∈ H.events.good n →
      ∀ (selection : Fin k → Fin (N n)) (hinj : Function.Injective selection)
        (henergy : ∀ a,D.eigenvalue n ω (selection a) ∈ K),
      ∀ (J : Type) [Fintype J] (A : Matrix (Fin k × Fin (N n)) J ℝ)
        (lo : ℝ) (hlo : 0 < lo)
        (hbound : ∀ x : Fin k × Fin (N n) → ℝ,lo*(∑ i,x i^2) ≤ dotProduct x ((A*A.transpose).mulVec x)),
      let energy := fun a => D.eigenvalue n ω (selection a)
      let eta := (N n : ℝ)^(-c0)
      let sigma := fun a => (diagonalBoundary d (energy a)).im
      let hEd := fun a => bulk_abs_lt_degree hd (energy a) (hbulk _ (henergy a))
      A*A.transpose=D.coloredResolventCovariance n ω energy eta sigma →
      ∀ r : ℝ,r ∈ Icc (0 : ℝ) 1 →
      |differentialEntropy (D.spectralStarGaussianDensity n ω A lo hlo hbound (fun i => r*D.rawEigenSignal n ω selection i))-
        (idealStarEntropy d k (by exact_mod_cast (show (2:ℝ) ≤ d by linarith)) energy (D.empiricalStarWeight n)
          (fun q => r • (D.empiricalNormalizedSignal n ω (by exact_mod_cast (show (2:ℝ) ≤ d by linarith)) selection hinj hEd).signal q)-
          ∑ a,Real.log (starNormalRescaleFactor d (energy a) eta (sigma a)))| ≤
        (N n : ℝ)^(-localComparisonExponent H.local_exponent c0) := by
  obtain ⟨s,hs,κ,hκ,κref,hκref,C,hC,hfull⟩ := D.HY_physical_star_entropy_uniform hd k hk K hK hbulk c0 H
  let m : ℝ := (k*(d+1) : ℕ)
  have hm : 0 < m := by dsimp [m]; positivity
  let R := uniformCovarianceEntropyRateConstant (Fin k × Fin (d+1)) κ ((k : ℝ)*((d : ℝ)+2))
  have hrate := eventually_uniform_physical_entropy_error (Fin k × Fin (d+1)) d m s κref
    (1+(k : ℝ)*((d : ℝ)+2)) (m*Hc.events.constant) c0 (R*C) H.local_exponent hm hs hκref (by positivity)
    H.height_range.1 hcsmall H.local_exponent_pos Hc.logPower
  have hsmall := eventually_localCovarianceScale_small C κ m H.local_exponent c0 H.local_exponent_pos H.height_range.1
  filter_upwards [D.size_tendsto.eventually hrate,D.size_tendsto.eventually hsmall,
    D.size_tendsto.eventually (eventually_ge_atTop 2),eventually_ge_atTop H.events.threshold,
    eventually_ge_atTop Hc.events.threshold] with n hnrate hnsmall hN2 hnH hnHc
  intro ω hωc hω selection hinj henergy J _ A lo hlo hbound energy eta sigma hEd hGram r hr
  letI : Nonempty (Fin (N n)) := ⟨⟨0,D.size_pos n⟩⟩
  let p := subsetWeightMass (uniformSampleWeight (Fin (N n) × Equiv.Perm (Fin d))) (fun q => q.1 ∈ H.badRoots n ω)
  have hp0 : 0 ≤ p := subsetWeightMass_nonneg _ (uniformSampleWeight_nonneg _) _
  have hp1 : p ≤ 1 := subsetWeightMass_le_one _ (uniformSampleWeight_nonneg _) (uniformSampleWeight_sum _) _
  have hpsmall : p ≤ (N n : ℝ)^(-(1/2 : ℝ)) := uniformProduct_bad_mass_le_sqrt_reciprocal
    (D.size_pos n) (Equiv.Perm (Fin d)) (H.badRoots n ω) (H.bad_count n hnH ω hω)
  have hB : 0 ≤ Hc.events.constant*Real.log (N n)^Hc.logPower :=
    mul_nonneg Hc.events.constant_pos.le (pow_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N n))) _)
  have hh := hfull n hnH hN2 ω hω selection hinj henergy J A lo hlo hbound hGram
    (Hc.events.constant*Real.log (N n)^Hc.logPower) hB
    (D.HY_rawEigenSignal_bound Hc n hnHc ω hωc selection) r hr hnsmall.1 hnsmall.2
  have hnumeric := hnrate p hp0 hp1 hpsmall
  apply hh.trans
  convert hnumeric using 1
  unfold physicalLocalEntropyError localCovarianceEntropyError
  dsimp only [R,m,p]
  ring

theorem HY_physical_edge_entropy_rate {P : Measure Ω} [IsProbabilityMeasure P]
    {quantile : ∀ n,Fin (N n) → ℝ} (Hc : HYCoarseInput D P quantile)
    (hd : 3 ≤ (d : ℝ)) (k : ℕ) (hk : 0 < k) (K : Set ℝ) (hK : IsCompact K)
    (hbulk : ∀ E ∈ K,E^2 < 4*((d : ℝ)-1)) (c0 : ℝ) (hcsmall : c0 ≤ 1/16)
    (H : HYLocalStarInput D P K c0 (treeGreenStar d hd)) :
    ∀ᶠ n in atTop, ∀ ω ∈ Hc.events.good n,ω ∈ H.events.good n →
      ∀ (selection : Fin k → Fin (N n)) (hinj : Function.Injective selection)
        (henergy : ∀ a,D.eigenvalue n ω (selection a) ∈ K),
      ∀ (J : Type) [Fintype J] (A : Matrix (Fin k × Fin (N n)) J ℝ)
        (lo : ℝ) (hlo : 0 < lo)
        (hbound : ∀ x : Fin k × Fin (N n) → ℝ,lo*(∑ i,x i^2) ≤ dotProduct x ((A*A.transpose).mulVec x)),
      let energy := fun a => D.eigenvalue n ω (selection a)
      let eta := (N n : ℝ)^(-c0)
      let sigma := fun a => (diagonalBoundary d (energy a)).im
      let hEd := fun a => bulk_abs_lt_degree hd (energy a) (hbulk _ (henergy a))
      A*A.transpose=D.coloredResolventCovariance n ω energy eta sigma →
      ∀ r : ℝ,r ∈ Icc (0 : ℝ) 1 → ∀ leaf : Fin d,
      |differentialEntropy (D.spectralEdgeGaussianDensity n ω A lo hlo hbound (fun i => r*D.rawEigenSignal n ω selection i))-
        idealEdgeEntropy d k (by exact_mod_cast (show (2:ℝ) ≤ d by linarith)) energy (D.empiricalStarWeight n)
          (fun q => r • (D.empiricalNormalizedSignal n ω (by exact_mod_cast (show (2:ℝ) ≤ d by linarith)) selection hinj hEd).signal q) leaf| ≤
        (N n : ℝ)^(-localComparisonExponent H.local_exponent c0) := by
  obtain ⟨s,hs,κ,hκ,κref,hκref,C,hC,hfull⟩ := D.HY_physical_edge_entropy_uniform hd k hk K hK hbulk c0 H
  have hdpos : 0 < d := by exact_mod_cast (show (0 : ℝ) < d by linarith)
  letI : Nonempty (Fin d) := ⟨⟨0,hdpos⟩⟩
  let m : ℝ := (k*2 : ℕ)
  have hm : 0 < m := by dsimp [m]; positivity
  let R := uniformCovarianceEntropyRateConstant (Fin k × Fin 2) κ (2*k)
  have hR : 0 ≤ R := by
    dsimp [R]
    unfold uniformCovarianceEntropyRateConstant stabilityRateConstant
    positivity
  have hrate := eventually_uniform_physical_entropy_error (Fin k × Fin 2) d m s κref
    (1+2*k) (m*Hc.events.constant) c0 (R*C) H.local_exponent hm hs hκref (by positivity)
    H.height_range.1 hcsmall H.local_exponent_pos Hc.logPower
  have hsmall := eventually_localCovarianceScale_small C κ m H.local_exponent c0 H.local_exponent_pos H.height_range.1
  filter_upwards [D.size_tendsto.eventually hrate,D.size_tendsto.eventually hsmall,
    D.size_tendsto.eventually (eventually_ge_atTop 2),eventually_ge_atTop H.events.threshold,
    eventually_ge_atTop Hc.events.threshold] with n hnrate hnsmall hN2 hnH hnHc
  intro ω hωc hω selection hinj henergy J _ A lo hlo hbound energy eta sigma hEd hGram r hr leaf
  letI : Nonempty (Fin (N n)) := ⟨⟨0,D.size_pos n⟩⟩
  let p := subsetWeightMass (uniformSampleWeight (Fin (N n) × Fin d)) (fun q => q.1 ∈ H.badRoots n ω)
  let b := Hc.events.constant*Real.log (N n)^Hc.logPower
  let restoration := 2*p*(uniformMixtureAbsoluteEntropyBound (Fin k × Fin 2) (physicalResolventFloor d eta)
    (m*(1/(s*eta))) (m*b)+uniformMixtureAbsoluteEntropyBound (Fin k × Fin 2) κref (1+2*k) (m*b))+2*Real.binEntropy p
  have hp0 : 0 ≤ p := subsetWeightMass_nonneg _ (uniformSampleWeight_nonneg _) _
  have hp1 : p ≤ 1 := subsetWeightMass_le_one _ (uniformSampleWeight_nonneg _) (uniformSampleWeight_sum _) _
  have hpsmall : p ≤ (N n : ℝ)^(-(1/2 : ℝ)) := uniformProduct_bad_mass_le_sqrt_reciprocal
    (D.size_pos n) (Fin d) (H.badRoots n ω) (H.bad_count n hnH ω hω)
  have hB : 0 ≤ b :=
    mul_nonneg Hc.events.constant_pos.le (pow_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N n))) _)
  have heta : 0 < eta := Real.rpow_pos_of_pos (Nat.cast_pos.mpr (D.size_pos n)) _
  have heta1 : eta ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (by omega : 1 ≤ N n)) (neg_nonpos.mpr H.height_range.1.le)
  have hsq : eta ≤ Real.sqrt eta := by nlinarith [Real.sq_sqrt heta.le,Real.sqrt_nonneg eta]
  have hscale : C*((N n : ℝ)^(-H.local_exponent)+eta) ≤
      C*((N n : ℝ)^(-H.local_exponent)+Real.sqrt eta) := by gcongr
  have he1 := hscale.trans hnsmall.1
  have he2 := (mul_le_mul_of_nonneg_left hscale (div_nonneg (sq_nonneg m) hκ.le)).trans hnsmall.2
  have hh := hfull n hnH hN2 ω hω selection hinj henergy J A lo hlo hbound hGram b hB
    (D.HY_rawEigenSignal_bound Hc n hnHc ω hωc selection) r hr leaf he1 he2
  change _ ≤ restoration+R*(1+(m*b)^2)*(C*((N n : ℝ)^(-H.local_exponent)+eta)) at hh
  have hnumeric : restoration+R*(1+(m*b)^2)*(C*((N n : ℝ)^(-H.local_exponent)+Real.sqrt eta)) ≤
      (N n : ℝ)^(-localComparisonExponent H.local_exponent c0) := by
    convert hnrate p hp0 hp1 hpsmall using 1
    unfold physicalLocalEntropyError localCovarianceEntropyError
    dsimp only [R,m,p,b,restoration,eta]
    ring
  exact hh.trans ((add_le_add_left (mul_le_mul_of_nonneg_left hscale (mul_nonneg hR (by positivity))) restoration).trans hnumeric)

end GeneralizedBulk.External.RegularSpectralData
