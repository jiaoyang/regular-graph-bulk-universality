import GeneralizedBulk.Graph.PhysicalSampleBounds
import GeneralizedBulk.Graph.HYFullStarEntropy
import GeneralizedBulk.Graph.HYFullEdgeEntropy
import GeneralizedBulk.Graph.ReferenceEdgeSampling

/-! HY full-mixture estimates applied to the literal physical spectral star
and edge densities. Covariance, coercivity, bad-root mass, signal means, and
the normal rescaling are all verified against the constructed factors. -/
noncomputable section
set_option maxHeartbeats 2000000
open scoped BigOperators Classical
open MeasureTheory Set
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Gaussian GeneralizedBulk.Covariance GeneralizedBulk.Entropy
open GeneralizedBulk.KestenMcKay GeneralizedBulk.Entropy.Channel GeneralizedBulk.Entropy.Mehler
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

theorem HY_physical_star_entropy_uniform {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : 3 ≤ (d : ℝ)) (k : ℕ) (hk : 0 < k) (K : Set ℝ) (hK : IsCompact K)
    (hbulk : ∀ E ∈ K,E^2 < 4*((d : ℝ)-1)) (c0 : ℝ)
    (H : HYLocalStarInput D P K c0 (treeGreenStar d hd)) :
    ∃ s : ℝ,0 < s ∧ ∃ κ : ℝ,0 < κ ∧ ∃ κref : ℝ,0 < κref ∧ ∃ C : ℝ,0 < C ∧
      ∀ n,H.events.threshold ≤ n → 2 ≤ N n → ∀ ω ∈ H.events.good n,
      ∀ (selection : Fin k → Fin (N n)) (hinj : Function.Injective selection)
        (henergy : ∀ a,D.eigenvalue n ω (selection a) ∈ K),
      ∀ (J : Type) [Fintype J] (A : Matrix (Fin k × Fin (N n)) J ℝ)
        (lo : ℝ) (hlo : 0 < lo)
        (hbound : ∀ x : Fin k × Fin (N n) → ℝ,lo*(∑ i,x i^2) ≤ dotProduct x ((A*A.transpose).mulVec x)),
      let energy := fun a => D.eigenvalue n ω (selection a)
      let eta := (N n : ℝ)^(-c0)
      let sigma := fun a => (diagonalBoundary d (energy a)).im
      A*A.transpose=D.coloredResolventCovariance n ω energy eta sigma →
      ∀ B : ℝ,0 ≤ B → (∀ i,|D.rawEigenSignal n ω selection i| ≤ B) → ∀ r : ℝ,r ∈ Icc (0 : ℝ) 1 →
      let m := ((k*(d+1) : ℕ) : ℝ)
      let p := subsetWeightMass (uniformSampleWeight (Fin (N n) × Equiv.Perm (Fin d)))
        (fun q => q.1 ∈ H.badRoots n ω)
      let e := C*((N n : ℝ)^(-H.local_exponent)+Real.sqrt eta)
      e ≤ 1 → (m^2/κ)*e ≤ 1/2 →
      |differentialEntropy (D.spectralStarGaussianDensity n ω A lo hlo hbound (fun i => r*D.rawEigenSignal n ω selection i))-
        (idealStarEntropy d k (by exact_mod_cast (show (2:ℝ) ≤ d by linarith)) energy (D.empiricalStarWeight n)
          (fun q => r • (D.empiricalNormalizedSignal n ω (by exact_mod_cast (show (2:ℝ) ≤ d by linarith)) selection hinj
            (fun a => bulk_abs_lt_degree hd _ (hbulk _ (henergy a)))).signal q)-
          ∑ a,Real.log (starNormalRescaleFactor d (energy a) eta (sigma a)))| ≤
        2*p*(uniformMixtureAbsoluteEntropyBound (Fin k × Fin (d+1)) (physicalResolventFloor d eta) (m*(1/(s*eta))) (m*B)+
          uniformMixtureAbsoluteEntropyBound (Fin k × Fin (d+1)) κref (1+(k : ℝ)*((d : ℝ)+2)) (m*B))+
        2*Real.binEntropy p+
        uniformCovarianceEntropyRateConstant (Fin k × Fin (d+1)) κ ((k : ℝ)*((d : ℝ)+2))*(1+(m*B)^2)*e := by
  have hd2 : 2 ≤ d := by exact_mod_cast (show (2:ℝ) ≤ d by linarith)
  obtain ⟨s,hs,hsigma⟩ := diagonalBoundary_im_uniform d hd K hK hbulk
  obtain ⟨κ,hκ,κref,hκref,C,hC,hfull⟩ := D.HY_full_star_mixture_entropy_uniform hd k K hK hbulk c0 H
  refine ⟨s,hs,κ,hκ,κref,hκref,C,hC,?_⟩
  intro n hn hN2 ω hω selection hinj henergy J _ A lo hlo hbound energy eta sigma hGram B hB hsignal r hr m p e he1 hsmall
  letI : Nonempty (Fin (N n)) := ⟨⟨0,D.size_pos n⟩⟩
  have heta : 0 < eta := Real.rpow_pos_of_pos (Nat.cast_pos.mpr (D.size_pos n)) _
  have heta1 : eta ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (by omega : 1 ≤ N n)) (neg_nonpos.mpr H.height_range.1.le)
  have hEd (a : Fin k) : |energy a| < d := bulk_abs_lt_degree hd _ (hbulk _ (henergy a))
  have hsigma' (a : Fin k) : s ≤ sigma a ∧ sigma a ≤ 2 := hsigma _ (henergy a)
  have hp : p < 1 := uniformProduct_bad_mass_lt_one hN2 (Equiv.Perm (Fin d)) (H.badRoots n ω) (H.bad_count n hn ω hω)
  have hraw (q : Fin (N n) × Equiv.Perm (Fin d)) (x : Fin k × Fin (d+1) → ℝ) :=
    D.spectralStarNoiseFactor_resolvent_bounds n ω A lo hlo hbound energy sigma eta s heta heta1 hs hsigma'
      (fun a => (hEd a).le) hGram q x
  have htrace (q : Fin (N n) × Equiv.Perm (Fin d)) :
      Matrix.trace (D.spectralStarNoiseFactor n ω A lo hlo hbound q*
        (D.spectralStarNoiseFactor n ω A lo hlo hbound q).transpose) ≤ m*(1/(s*eta)) := by
    simpa only [Fintype.card_prod,Fintype.card_fin] using
      covariance_trace_le_of_quadratic_upper _ (1/(s*eta)) (fun x => (hraw q x).2)
  have hmean (q : Fin (N n) × Equiv.Perm (Fin d)) :
      coordinateL1 (r • D.starSample n ω (fun a => D.eigenvector n ω (selection a)) q) ≤ m*B := by
    rw [← D.rawEigenSignal_star_mean n ω selection r q]
    simpa only [Fintype.card_prod,Fintype.card_fin] using coordinateL1_selected_scaled_le
      (D.rawEigenSignal n ω selection) (coloredCoordinateSelection (D.starVertex n ω q)) B hB hsignal r hr
  have hfix (q : Fin (N n) × Equiv.Perm (Fin d)) :
      (coloredStarRescale (d := d) energy sigma eta).mulVec
        (r • D.starSample n ω (fun a => D.eigenvector n ω (selection a)) q) =
        r • D.starSample n ω (fun a => D.eigenvector n ω (selection a)) q :=
    D.coloredStarRescale_starSample_fixed n ω _ q energy sigma eta r (fun a => D.eigen_equation n ω (selection a) q.1)
  have hh := hfull n hn ω hω energy henergy (Fin (N n) × Equiv.Perm (Fin d)) id
    (uniformSampleWeight _) (fun q => r • D.starSample n ω (fun a => D.eigenvector n ω (selection a)) q)
    (D.spectralStarNoiseFactor n ω A lo hlo hbound) (uniformSampleWeight_nonneg _) (uniformSampleWeight_sum _)
    (D.spectralStarNoiseFactor_det_ne_zero n ω A lo hlo hbound)
    (D.spectralStarNoiseFactor_resolvent_covariance n ω A lo hlo hbound energy sigma eta hGram) hfix hp
    (physicalResolventFloor d eta) (m*(1/(s*eta))) (m*B) (by unfold physicalResolventFloor; positivity)
    (by dsimp [m]; positivity) (mul_nonneg (by dsimp [m]; positivity) hB) hmean (fun q x => (hraw q x).1) htrace he1 hsmall
  have href := D.empirical_idealStarEntropy n ω hd2 selection hinj hEd r
  rw [href]
  exact hh

theorem HY_physical_edge_entropy_uniform {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : 3 ≤ (d : ℝ)) (k : ℕ) (hk : 0 < k) (K : Set ℝ) (hK : IsCompact K)
    (hbulk : ∀ E ∈ K,E^2 < 4*((d : ℝ)-1)) (c0 : ℝ)
    (H : HYLocalStarInput D P K c0 (treeGreenStar d hd)) :
    ∃ s : ℝ,0 < s ∧ ∃ κ : ℝ,0 < κ ∧ ∃ κref : ℝ,0 < κref ∧ ∃ C : ℝ,0 < C ∧
      ∀ n,H.events.threshold ≤ n → 2 ≤ N n → ∀ ω ∈ H.events.good n,
      ∀ (selection : Fin k → Fin (N n)) (hinj : Function.Injective selection)
        (henergy : ∀ a,D.eigenvalue n ω (selection a) ∈ K),
      ∀ (J : Type) [Fintype J] (A : Matrix (Fin k × Fin (N n)) J ℝ)
        (lo : ℝ) (hlo : 0 < lo)
        (hbound : ∀ x : Fin k × Fin (N n) → ℝ,lo*(∑ i,x i^2) ≤ dotProduct x ((A*A.transpose).mulVec x)),
      let energy := fun a => D.eigenvalue n ω (selection a)
      let eta := (N n : ℝ)^(-c0)
      let sigma := fun a => (diagonalBoundary d (energy a)).im
      A*A.transpose=D.coloredResolventCovariance n ω energy eta sigma →
      ∀ B : ℝ,0 ≤ B → (∀ i,|D.rawEigenSignal n ω selection i| ≤ B) → ∀ r : ℝ,r ∈ Icc (0 : ℝ) 1 → ∀ leaf : Fin d,
      let m := ((k*2 : ℕ) : ℝ)
      let p := subsetWeightMass (uniformSampleWeight (Fin (N n) × Fin d)) (fun q => q.1 ∈ H.badRoots n ω)
      let e := C*((N n : ℝ)^(-H.local_exponent)+eta)
      e ≤ 1 → (m^2/κ)*e ≤ 1/2 →
      |differentialEntropy (D.spectralEdgeGaussianDensity n ω A lo hlo hbound (fun i => r*D.rawEigenSignal n ω selection i))-
        idealEdgeEntropy d k (by exact_mod_cast (show (2:ℝ) ≤ d by linarith)) energy (D.empiricalStarWeight n)
          (fun q => r • (D.empiricalNormalizedSignal n ω (by exact_mod_cast (show (2:ℝ) ≤ d by linarith)) selection hinj
            (fun a => bulk_abs_lt_degree hd _ (hbulk _ (henergy a)))).signal q) leaf| ≤
        2*p*(uniformMixtureAbsoluteEntropyBound (Fin k × Fin 2) (physicalResolventFloor d eta) (m*(1/(s*eta))) (m*B)+
          uniformMixtureAbsoluteEntropyBound (Fin k × Fin 2) κref (1+2*k) (m*B))+2*Real.binEntropy p+
        uniformCovarianceEntropyRateConstant (Fin k × Fin 2) κ (2*k)*(1+(m*B)^2)*e := by
  have hd2 : 2 ≤ d := by exact_mod_cast (show (2:ℝ) ≤ d by linarith)
  have hdpos : 0 < d := by omega
  letI : Nonempty (Fin d) := ⟨⟨0,hdpos⟩⟩
  obtain ⟨s,hs,hsigma⟩ := diagonalBoundary_im_uniform d hd K hK hbulk
  obtain ⟨κ,hκ,κref,hκref,C,hC,hfull⟩ := D.HY_full_edge_mixture_entropy_uniform hd k K hK hbulk c0 H
  refine ⟨s,hs,κ,hκ,κref,hκref,C,hC,?_⟩
  intro n hn hN2 ω hω selection hinj henergy J _ A lo hlo hbound energy eta sigma hGram B hB hsignal r hr leaf m p e he1 hsmall
  letI : Nonempty (Fin (N n)) := ⟨⟨0,D.size_pos n⟩⟩
  have heta : 0 < eta := Real.rpow_pos_of_pos (Nat.cast_pos.mpr (D.size_pos n)) _
  have heta1 : eta ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (by omega : 1 ≤ N n)) (neg_nonpos.mpr H.height_range.1.le)
  have hEd (a : Fin k) : |energy a| < d := bulk_abs_lt_degree hd _ (hbulk _ (henergy a))
  have hsigma' (a : Fin k) : s ≤ sigma a ∧ sigma a ≤ 2 := hsigma _ (henergy a)
  have hp : p < 1 := uniformProduct_bad_mass_lt_one hN2 (Fin d) (H.badRoots n ω) (H.bad_count n hn ω hω)
  have hraw (q : Fin (N n) × Fin d) (x : Fin k × Fin 2 → ℝ) :=
    D.spectralEdgeNoiseFactor_resolvent_bounds n ω A lo hlo hbound energy sigma eta s heta heta1 hs hsigma'
      (fun a => (hEd a).le) hGram q x
  have htrace (q : Fin (N n) × Fin d) :
      Matrix.trace (D.spectralEdgeNoiseFactor n ω A lo hlo hbound q*
        (D.spectralEdgeNoiseFactor n ω A lo hlo hbound q).transpose) ≤ m*(1/(s*eta)) := by
    simpa only [Fintype.card_prod,Fintype.card_fin] using
      covariance_trace_le_of_quadratic_upper _ (1/(s*eta)) (fun x => (hraw q x).2)
  have hmean (q : Fin (N n) × Fin d) :
      coordinateL1 (r • D.orientedEdgeMark n ω (fun a => D.eigenvector n ω (selection a)) q) ≤ m*B := by
    rw [← D.rawEigenSignal_edge_mean n ω selection r q]
    simpa only [Fintype.card_prod,Fintype.card_fin] using coordinateL1_selected_scaled_le
      (D.rawEigenSignal n ω selection) (coloredCoordinateSelection (D.proposalEndpoint n ω q)) B hB hsignal r hr
  let M := edgePhysicalFactor d k hd2 energy leaf
  have hh := hfull n hn ω hω energy henergy (Fin (N n) × Fin d) id
    (uniformSampleWeight _) (fun q => r • D.orientedEdgeMark n ω (fun a => D.eigenvector n ω (selection a)) q)
    (D.spectralEdgeNoiseFactor n ω A lo hlo hbound) (uniformSampleWeight_nonneg _) (uniformSampleWeight_sum _)
    (D.spectralEdgeNoiseFactor_det_ne_zero n ω A lo hlo hbound)
    (D.spectralEdgeNoiseFactor_resolvent_covariance n ω A lo hlo hbound energy eta hGram)
    M (edgePhysicalFactor_det_ne_zero d k hd2 energy hEd leaf) (edgePhysicalFactor_covariance d k hd2 energy hEd leaf) hp
    (physicalResolventFloor d eta) (m*(1/(s*eta))) (m*B) (by unfold physicalResolventFloor; positivity)
    (by dsimp [m]; positivity) (mul_nonneg (by dsimp [m]; positivity) hB) hmean (fun q x => (hraw q x).1) htrace he1 hsmall
  have href : idealEdgeEntropy d k hd2 energy (D.empiricalStarWeight n)
      (fun q => r • (D.empiricalNormalizedSignal n ω hd2 selection hinj hEd).signal q) leaf =
      differentialEntropy (gaussianMixturePDF (uniformSampleWeight (Fin (N n) × Fin d))
        (fun q => r • D.orientedEdgeMark n ω (fun a => D.eigenvector n ω (selection a)) q) (fun _ => M)) := by
    rw [D.empirical_idealEdgeEntropy n ω hd2 selection hinj hEd r leaf,
      D.referenceEdgeGaussianMixturePDF_eq_oriented n ω _ leaf r M]
  rw [href]
  exact hh

end GeneralizedBulk.External.RegularSpectralData
