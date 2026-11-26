import GeneralizedBulk.Graph.HYEdgeEntropy
import GeneralizedBulk.Entropy.RestoredCovarianceComparison

/-! The full colored edge entropy comparison includes all bad roots, with
their actual mixture mass and actual finite Gaussian entropy bounds. -/
noncomputable section
open scoped BigOperators Classical
namespace GeneralizedBulk.External.RegularSpectralData
open Set MeasureTheory GeneralizedBulk.KestenMcKay GeneralizedBulk.Gaussian GeneralizedBulk.Entropy GeneralizedBulk.Covariance GeneralizedBulk.Entropy.Mehler
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

theorem HY_full_edge_mixture_entropy_uniform {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : 3 ≤ (d : ℝ)) (k : ℕ) (K : Set ℝ) (hK : IsCompact K)
    (hbulk : ∀ E ∈ K,E^2 < 4*((d : ℝ)-1)) (c0 : ℝ)
    (H : HYLocalStarInput D P K c0 (treeGreenStar d hd)) :
    ∃ κ : ℝ,0 < κ ∧ ∃ κref : ℝ,0 < κref ∧ ∃ C : ℝ,0 < C ∧
      ∀ n,H.events.threshold ≤ n → ∀ ω ∈ H.events.good n,
      ∀ energy : Fin k → ℝ,(∀ a,energy a ∈ K) →
      ∀ (S : Type) [Fintype S] (sample : S → Fin (N n) × Fin d)
        (weight : S → ℝ) (mean : S → Fin k × Fin 2 → ℝ)
        (A : S → Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℝ),
      (∀ s,0 ≤ weight s) → (∑ s,weight s=1) → (∀ s,(A s).det ≠ 0) →
      (∀ s,A s*(A s).transpose=D.coloredLocalEdgeCovariance n ω (sample s) energy ((N n : ℝ)^(-c0))) →
      ∀ M : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℝ,M.det ≠ 0 →
      M*M.transpose=colorBlock (fun a => edgeWaveCovariance d (energy a)) →
      let bad := fun s => (sample s).1 ∈ H.badRoots n ω
      let p := subsetWeightMass weight bad
      p < 1 → ∀ κraw Uraw B : ℝ,0 < κraw → 0 < Uraw → 0 ≤ B →
      (∀ s,coordinateL1 (mean s) ≤ B) →
      (∀ s x,κraw*(∑ i,x i^2) ≤ dotProduct x ((A s*(A s).transpose).mulVec x)) →
      (∀ s,Matrix.trace (A s*(A s).transpose) ≤ Uraw) →
      let e := C*((N n : ℝ)^(-H.local_exponent)+(N n : ℝ)^(-c0))
      e ≤ 1 → (((k*2 : ℕ) : ℝ)^2/κ)*e ≤ 1/2 →
      |differentialEntropy (gaussianMixturePDF weight mean A)-
        differentialEntropy (gaussianMixturePDF weight mean (fun _ => M))| ≤
        2*p*(uniformMixtureAbsoluteEntropyBound (Fin k × Fin 2) κraw Uraw B+
          uniformMixtureAbsoluteEntropyBound (Fin k × Fin 2) κref (1+2*k) B)+2*Real.binEntropy p+
        uniformCovarianceEntropyRateConstant (Fin k × Fin 2) κ (2*k)*(1+B^2)*e := by
  obtain ⟨κ,hκ,C,hC,hgood⟩ := D.HY_good_edge_mixture_entropy_uniform hd k K hK hbulk c0 H
  obtain ⟨κref,hκref,hfloorRef⟩ := coloredEdgeWaveCovariance_uniform_floor d k
    (by exact_mod_cast (show (0:ℝ) < d by linarith)) K hK (fun E hE => bulk_abs_lt_degree hd E (hbulk E hE))
  refine ⟨κ,hκ,κref,hκref,C,hC,?_⟩
  intro n hn ω hω energy hE S _ sample weight mean A hw hsum hA hGram M hM hMGram bad p hp
    κraw Uraw B hκraw hUraw hB hsignal hfloor htrace e he1 hsmall
  have hg : subsetWeightMass weight (fun s => ¬ bad s) ≠ 0 := by
    rw [subsetWeightMass_compl weight hsum bad]
    exact (sub_pos.mpr hp).ne'
  letI : DecidablePred (fun s : S => ¬ bad s) := fun s => Classical.propDecidable _
  have hcompare : |differentialEntropy (conditionalGaussianMixturePDF weight mean A (fun s => ¬ bad s))-
      differentialEntropy (conditionalGaussianMixturePDF weight mean (fun _ => M) (fun s => ¬ bad s))| ≤
      uniformCovarianceEntropyRateConstant (Fin k × Fin 2) κ (2*k)*(1+B^2)*e := by
    rw [conditionalGaussianMixturePDF_eq_subtype weight mean A (fun s => ¬ bad s) hg,
      conditionalGaussianMixturePDF_eq_subtype weight mean (fun _ => M) (fun s => ¬ bad s) hg]
    exact hgood n hn ω hω energy hE {s : S // ¬ bad s} (fun s => sample s.val) (fun s => s.property)
      (conditionalSubtypeWeight weight (fun s => ¬ bad s)) (fun s => mean s.val) (fun s => A s.val)
      (conditionalSubtypeWeight_nonneg weight hw _) (conditionalSubtypeWeight_sum weight _ hg)
      (fun s => hA s.val) (fun s => hGram s.val) M hM hMGram B hB (fun s => hsignal s.val) he1 hsmall
  have hreffloor (x : Fin k × Fin 2 → ℝ) : κref*(∑ i,x i^2) ≤ dotProduct x ((M*M.transpose).mulVec x) := by
    rw [hMGram]
    exact hfloorRef energy hE x
  have hreftrace : Matrix.trace (M*M.transpose) ≤ (1:ℝ)+2*k := by
    rw [hMGram,colorBlock_trace]
    simp only [edgeWaveCovariance_trace,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    nlinarith
  have hh := gaussianMixture_entropy_compare_after_good_rescaling weight mean A M 1 hw hsum hA hM
    (by simp) (fun s => by simp) bad κraw Uraw κref (1+2*k) B
    (uniformCovarianceEntropyRateConstant (Fin k × Fin 2) κ (2*k)*(1+B^2)*e)
    hκraw hUraw hκref (by positivity) hB hsignal hfloor htrace hreffloor hreftrace
    (by simpa only [Matrix.one_mul] using hcompare)
  simpa only [Matrix.det_one,abs_one,Real.log_one,sub_zero] using hh

end GeneralizedBulk.External.RegularSpectralData
