import GeneralizedBulk.Gaussian.ColoredExtendedWhitening
import GeneralizedBulk.Gaussian.StarReferenceTrace
import GeneralizedBulk.Matrix.ColorBlocks

/-! Uniform conditioning of the actual independent-color full-star reference. -/
noncomputable section
open scoped BigOperators
namespace GeneralizedBulk.Gaussian
open GeneralizedBulk.Covariance GeneralizedBulk.Entropy

theorem coloredReferenceCovariance_eq_colorBlock (d k : ℕ) (energy : Fin k → ℝ) :
    coloredReferenceCovariance d k energy=colorBlock (fun a => starReferenceCovariance d (energy a)) := rfl

theorem coloredReferenceCovariance_trace (d k : ℕ) (hd : 0 < d) (energy : Fin k → ℝ) :
    Matrix.trace (coloredReferenceCovariance d k energy)=(k : ℝ)*((d : ℝ)+2) := by
  rw [coloredReferenceCovariance_eq_colorBlock,colorBlock_trace]
  simp only [starReferenceCovariance_trace d hd,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

theorem coloredReferenceCovariance_uniform_floor (d k : ℕ) (hd : 2 ≤ d)
    (K : Set ℝ) (hK : IsCompact K) (hbulk : ∀ E ∈ K,|E| < d) :
    ∃ kappa : ℝ,0 < kappa ∧ ∀ energy : Fin k → ℝ,(∀ a,energy a ∈ K) →
      ∀ x : Fin k × Fin (d+1) → ℝ,kappa*(∑ i,x i^2) ≤
        dotProduct x ((coloredReferenceCovariance d k energy).mulVec x) := by
  obtain ⟨κ,hκ,hfloor⟩ := starReference_uniform_positive_floor d hd K hK hbulk
  refine ⟨κ,hκ,fun energy hE x => ?_⟩
  rw [coloredReferenceCovariance_eq_colorBlock]
  exact colorBlock_quadratic_floor _ κ (fun a y => hfloor (energy a) (hE a) y) x

theorem coloredExtendedFactor_uniform_conditioning (d k : ℕ) (hd : 2 ≤ d)
    (K : Set ℝ) (hK : IsCompact K) (hbulk : ∀ E ∈ K,|E| < d) :
    ∃ kappa : ℝ,0 < kappa ∧ ∀ energy : Fin k → ℝ,(∀ a,energy a ∈ K) →
      let M := coloredExtendedFactor d k hd energy
      M.det ≠ 0 ∧
      (∀ x : Fin k × Fin (d+1) → ℝ,kappa*(∑ i,x i^2) ≤ dotProduct x ((M*M.transpose).mulVec x)) ∧
      Matrix.trace (M*M.transpose)=(k : ℝ)*((d : ℝ)+2) := by
  obtain ⟨κ,hκ,hfloor⟩ := coloredReferenceCovariance_uniform_floor d k hd K hK hbulk
  refine ⟨κ,hκ,fun energy hE => ?_⟩
  have he : ∀ a,|energy a| < d := fun a => hbulk (energy a) (hE a)
  refine ⟨coloredExtendedFactor_det_ne_zero d k hd energy he,?_,?_⟩
  · rw [coloredExtendedFactor_covariance d k hd energy he]
    exact hfloor energy hE
  · rw [coloredExtendedFactor_covariance d k hd energy he,coloredReferenceCovariance_trace d k (by omega)]

end GeneralizedBulk.Gaussian
