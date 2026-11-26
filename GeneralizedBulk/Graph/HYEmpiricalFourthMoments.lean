import GeneralizedBulk.Graph.HYEmpiricalQuartic

/-! Concrete actual graph fourth moments under the external HY good event.
Finite-graph entropy counting must supply the displayed numerical deficit. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.External.RegularSpectralData
open GeneralizedBulk.Entropy.Channel GeneralizedBulk.Entropy.Mehler
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

def empiricalFourthWickDiscrepancy {k : ℕ} (selection : Fin k → Fin (N n))
    (j1 j2 j3 j4 : Fin k × Fin (d + 1)) : ℝ :=
  (∑ s : EmpiricalStarSample d (N n), D.empiricalStarWeight n s *
    D.starSample n ω (fun a => D.eigenvector n ω (selection a)) s j1 *
    D.starSample n ω (fun a => D.eigenvector n ω (selection a)) s j2 *
    D.starSample n ω (fun a => D.eigenvector n ω (selection a)) s j3 *
    D.starSample n ω (fun a => D.eigenvector n ω (selection a)) s j4) -
    (D.empiricalGaussianCovariance n ω selection j1 j2 * D.empiricalGaussianCovariance n ω selection j3 j4 +
     D.empiricalGaussianCovariance n ω selection j1 j3 * D.empiricalGaussianCovariance n ω selection j2 j4 +
     D.empiricalGaussianCovariance n ω selection j1 j4 * D.empiricalGaussianCovariance n ω selection j2 j3)

/-- The actual graph fourth-moment estimate is uniform over every color and
physical root/leaf slot. BS/HY are not used to assume a fourth-moment limit. -/
theorem HY_uniform_empirical_fourth_moments {P : Measure Ω} [IsProbabilityMeasure P]
    {quantile : ∀ n, Fin (N n) → ℝ} (H : HYCoarseInput D P quantile)
    {k : ℕ} (hd : 3 ≤ d) (K : Set (StarParameters k)) (hK : IsCompact K)
    (hKbulk : ∀ c ∈ K, ∀ a, (c.val a) ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ n, H.events.threshold ≤ n → ∀ ω, ω ∈ H.events.good n →
      ∀ (selection : Fin k → Fin (N n)) (hinj : Function.Injective selection)
      (hbulk : ∀ a, (D.eigenvalue n ω (selection a) / d) ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2),
      D.empiricalParameters n ω hd selection hbulk ∈ K → ∀ epsilon : ℝ, 0 < epsilon →
      let Bwhite := empiricalWhitenedBound d k (H.events.constant * Real.log (N n) ^ H.logPower)
      let a := (epsilon / starTaylorCoefficient d k (by omega) Bwhite) ^ ((9 : ℝ)⁻¹)
      a ≤ 1 / 2 → a * (((Fintype.card (ScalarCoordinate d k) : ℝ) + 1) * Bwhite) ≤ 1 / 2 →
      (D.empiricalBulkSignal n ω hd selection hinj hbulk).observationEntropyDeficit
        (coloredObservationMatrix d k (by omega)) (coloredObservationMatrix_orthogonal d k (by omega))
          (coloredObserved d k (by omega)) a ≤ epsilon →
      ∀ j1 j2 j3 j4 : Fin k × Fin (d + 1),
      |D.empiricalFourthWickDiscrepancy n ω selection j1 j2 j3 j4| ≤
        64 * empiricalQuarticRate d k (by omega) κ Bwhite epsilon := by
  obtain ⟨κ, hκ, hnorm⟩ := D.HY_uniform_empirical_quartic H hd K hK hKbulk
  refine ⟨κ, hκ, ?_⟩
  intro n hn ω hgood selection hinj hbulk hc epsilon hepsilon Bwhite a ha1 hsmall hdelta j1 j2 j3 j4
  have hq := hnorm n hn ω hgood selection hinj hbulk hc epsilon hepsilon ha1 hsmall hdelta
  exact (D.empirical_mixed_fourth_wick_bound n ω hd selection hinj hbulk j1 j2 j3 j4).trans
    (mul_le_mul_of_nonneg_left hq (by norm_num : (0 : ℝ) ≤ 64))

end GeneralizedBulk.External.RegularSpectralData
