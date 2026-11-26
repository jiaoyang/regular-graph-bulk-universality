import GeneralizedBulk.Graph.PermutedStarCovariance
import GeneralizedBulk.Gaussian.ColoredReferenceBounds
import GeneralizedBulk.Matrix.PositiveColorBlocks
import GeneralizedBulk.Entropy.GaussianMixtureCovarianceEntropy

/-! Actual good-root colored star mixtures have the full reference entropy,
up to a quantitative error derived only from HY. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.External.RegularSpectralData
open Set MeasureTheory GeneralizedBulk.KestenMcKay GeneralizedBulk.Gaussian GeneralizedBulk.Entropy GeneralizedBulk.Covariance GeneralizedBulk.Entropy.Mehler
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

def coloredRescaledStarCovariance {k : ℕ} (n : ℕ) (ω : Ω)
    (s : Fin (N n) × Equiv.Perm (Fin d)) (energy : Fin k → ℝ) (eta : ℝ) :
    Matrix (Fin k × Fin (d+1)) (Fin k × Fin (d+1)) ℝ :=
  colorBlock (fun a => D.rescaledPermutedStarCovariance n ω s (energy a) eta (diagonalBoundary d (energy a)).im)

theorem HY_good_star_mixture_entropy_uniform {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : 3 ≤ (d : ℝ)) (k : ℕ) (K : Set ℝ) (hK : IsCompact K)
    (hbulk : ∀ E ∈ K,E^2 < 4*((d : ℝ)-1)) (c0 : ℝ)
    (H : HYLocalStarInput D P K c0 (treeGreenStar d hd)) :
    ∃ kappa : ℝ,0 < kappa ∧ ∃ C : ℝ,0 < C ∧
      ∀ n,H.events.threshold ≤ n → ∀ ω ∈ H.events.good n,
      ∀ energy : Fin k → ℝ,(∀ a,energy a ∈ K) →
      ∀ (S : Type) [Fintype S] (sample : S → Fin (N n) × Equiv.Perm (Fin d)),
      (∀ s,(sample s).1 ∉ H.badRoots n ω) →
      ∀ (weight : S → ℝ) (mean : S → Fin k × Fin (d+1) → ℝ)
        (A : S → Matrix (Fin k × Fin (d+1)) (Fin k × Fin (d+1)) ℝ),
      (∀ s,0 ≤ weight s) → (∑ s,weight s=1) → (∀ s,(A s).det ≠ 0) →
      (∀ s,A s*(A s).transpose=D.coloredRescaledStarCovariance n ω (sample s) energy ((N n : ℝ)^(-c0))) →
      ∀ B : ℝ,0 ≤ B → (∀ s,coordinateL1 (mean s) ≤ B) →
      let e := C*((N n : ℝ)^(-H.local_exponent)+Real.sqrt ((N n : ℝ)^(-c0)))
      e ≤ 1 → (((k*(d+1) : ℕ) : ℝ)^2/kappa)*e ≤ 1/2 →
      |differentialEntropy (gaussianMixturePDF weight mean A)-
        differentialEntropy (gaussianMixturePDF weight mean (fun _ => coloredExtendedFactor d k (by exact_mod_cast (show (2:ℝ) ≤ d by linarith)) energy))| ≤
        uniformCovarianceEntropyRateConstant (Fin k × Fin (d+1)) kappa ((k : ℝ)*((d : ℝ)+2))*(1+B^2)*e := by
  have hd2 : 2 ≤ d := by exact_mod_cast (show (2:ℝ) ≤ d by linarith)
  have hb : ∀ E ∈ K,|E| < d := fun E hE => bulk_abs_lt_degree hd E (hbulk E hE)
  obtain ⟨κ,hκ,hcondition⟩ := coloredExtendedFactor_uniform_conditioning d k hd2 K hK hb
  obtain ⟨C,hC,hclose⟩ := D.HYLocalStar_rescaled_covariance_uniform hd K hK hbulk c0 H
  refine ⟨κ,hκ,C,hC,?_⟩
  intro n hn ω hω energy hE S _ sample hgood weight mean A hw hsum hA hGram B hB hsignal e he1 hsmall
  let eta := (N n : ℝ)^(-c0)
  have heta : 0 < eta := Real.rpow_pos_of_pos (Nat.cast_pos.mpr (D.size_pos n)) _
  have hener : ∀ a,|energy a| < d := fun a => hb (energy a) (hE a)
  have hcond := hcondition energy hE
  have hQ (s : S) : (A s*(A s).transpose).PosDef := by
    rw [hGram s]
    apply colorBlock_posDef
    intro a
    exact D.rescaledPermutedStarCovariance_posDef n ω (by omega) (sample s) (energy a) eta
      (diagonalBoundary d (energy a)).im heta (diagonalBoundary_im_pos d (energy a) hd (hbulk _ (hE a)))
  apply gaussianMixture_entropy_stability_of_covariance weight mean A hw hsum hA
    hQ (coloredExtendedFactor d k hd2 energy) hcond.1 κ ((k : ℝ)*((d : ℝ)+2)) hκ
    (by positivity) hcond.2.1 (le_of_eq hcond.2.2) B e hB (by dsimp [e]; positivity) he1 hsignal
  · intro s i j
    rw [hGram s,coloredExtendedFactor_covariance d k hd2 energy hener,coloredReferenceCovariance_eq_colorBlock]
    apply colorBlock_entry_error _ _ e (by dsimp [e]; positivity)
    intro a u v
    exact D.rescaledPermutedStarCovariance_entry_bound n ω (sample s) (energy a) eta
      (diagonalBoundary d (energy a)).im e (hclose n hn ω hω (sample s).1 (hgood s) (energy a) (hE a)) u v
  · simpa only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul] using hsmall

end GeneralizedBulk.External.RegularSpectralData
