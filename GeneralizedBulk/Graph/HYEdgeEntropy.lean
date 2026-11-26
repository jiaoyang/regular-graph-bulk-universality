import GeneralizedBulk.Graph.HYEdgeCovariance
import GeneralizedBulk.Graph.HYRescaledStarCovariance
import GeneralizedBulk.Entropy.GaussianMixtureCovarianceEntropy

/-! Actual good-root colored edge mixtures have the Gaussian-wave reference
entropy up to the genuine HY covariance error. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.External.RegularSpectralData
open Set MeasureTheory GeneralizedBulk.KestenMcKay GeneralizedBulk.Gaussian GeneralizedBulk.Entropy GeneralizedBulk.Covariance GeneralizedBulk.Entropy.Mehler
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

def coloredLocalEdgeCovariance {k : ℕ} (n : ℕ) (ω : Ω) (s : Fin (N n) × Fin d)
    (energy : Fin k → ℝ) (eta : ℝ) : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℝ :=
  colorBlock (fun a => D.localEntropyEdgeCovariance n ω s (energy a) eta (diagonalBoundary d (energy a)).im)

theorem HY_good_edge_mixture_entropy_uniform {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : 3 ≤ (d : ℝ)) (k : ℕ) (K : Set ℝ) (hK : IsCompact K)
    (hbulk : ∀ E ∈ K,E^2 < 4*((d : ℝ)-1)) (c0 : ℝ)
    (H : HYLocalStarInput D P K c0 (treeGreenStar d hd)) :
    ∃ kappa : ℝ,0 < kappa ∧ ∃ C : ℝ,0 < C ∧
      ∀ n,H.events.threshold ≤ n → ∀ ω ∈ H.events.good n,
      ∀ energy : Fin k → ℝ,(∀ a,energy a ∈ K) →
      ∀ (S : Type) [Fintype S] (sample : S → Fin (N n) × Fin d),
      (∀ s,(sample s).1 ∉ H.badRoots n ω) →
      ∀ (weight : S → ℝ) (mean : S → Fin k × Fin 2 → ℝ)
        (A : S → Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℝ),
      (∀ s,0 ≤ weight s) → (∑ s,weight s=1) → (∀ s,(A s).det ≠ 0) →
      (∀ s,A s*(A s).transpose=D.coloredLocalEdgeCovariance n ω (sample s) energy ((N n : ℝ)^(-c0))) →
      ∀ M : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℝ,M.det ≠ 0 →
      M*M.transpose=colorBlock (fun a => edgeWaveCovariance d (energy a)) →
      ∀ B : ℝ,0 ≤ B → (∀ s,coordinateL1 (mean s) ≤ B) →
      let e := C*((N n : ℝ)^(-H.local_exponent)+(N n : ℝ)^(-c0))
      e ≤ 1 → (((k*2 : ℕ) : ℝ)^2/kappa)*e ≤ 1/2 →
      |differentialEntropy (gaussianMixturePDF weight mean A)-
        differentialEntropy (gaussianMixturePDF weight mean (fun _ => M))| ≤
        uniformCovarianceEntropyRateConstant (Fin k × Fin 2) kappa (2*k)*(1+B^2)*e := by
  have hdpos : 0 < d := by exact_mod_cast (show (0:ℝ) < d by linarith)
  have hb : ∀ E ∈ K,|E| < d := fun E hE => bulk_abs_lt_degree hd E (hbulk E hE)
  obtain ⟨κ,hκ,hfloor⟩ := coloredEdgeWaveCovariance_uniform_floor d k hdpos K hK hb
  obtain ⟨C,hC,hclose⟩ := D.HYLocalStar_edge_covariance_uniform hd K hK hbulk c0 H
  refine ⟨κ,hκ,C,hC,?_⟩
  intro n hn ω hω energy hE S _ sample hgood weight mean A hw hsum hA hGram M hM hMGram B hB hsignal e he1 hsmall
  let eta := (N n : ℝ)^(-c0)
  have heta : 0 < eta := Real.rpow_pos_of_pos (Nat.cast_pos.mpr (D.size_pos n)) _
  have hQ (s : S) : (A s*(A s).transpose).PosDef := by
    rw [hGram s]
    apply colorBlock_posDef
    intro a
    exact D.localEntropyEdgeCovariance_posDef n ω (sample s) (energy a) eta
      (diagonalBoundary d (energy a)).im heta (diagonalBoundary_im_pos d (energy a) hd (hbulk _ (hE a)))
  have hf (x : Fin k × Fin 2 → ℝ) : κ*(∑ i,x i^2) ≤ dotProduct x ((M*M.transpose).mulVec x) := by
    rw [hMGram]
    exact hfloor energy hE x
  have ht : Matrix.trace (M*M.transpose) ≤ (2:ℝ)*k := by
    rw [hMGram,colorBlock_trace]
    simp only [edgeWaveCovariance_trace,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    nlinarith
  apply gaussianMixture_entropy_stability_of_covariance weight mean A hw hsum hA hQ M hM κ (2*k) hκ
    (by positivity) hf ht B e hB (by dsimp [e]; positivity) he1 hsignal
  · intro s i j
    rw [hGram s,hMGram]
    apply colorBlock_entry_error _ _ e (by dsimp [e]; positivity)
    intro a u v
    exact hclose n hn ω hω (sample s) (hgood s) (energy a) (hE a) u v
  · simpa only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul] using hsmall

end GeneralizedBulk.External.RegularSpectralData
