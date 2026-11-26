import GeneralizedBulk.Graph.StarProposalCovariance
import GeneralizedBulk.Graph.CovarianceVarianceRates

/-! One- and two-color star fourth rates feed the actual finite variance and tail machinery. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology Classical
namespace GeneralizedBulk.External.RegularSpectralData
open Graph
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

/-- Only one color for diagonal terms and two distinct colors for off-diagonal
terms are needed to control every actual proposal covariance in a window. -/
theorem proposal_covariance_window_of_one_two_color_Wick
    (hd : 0 < d) (s : Finset (Fin (N n)))
    (hs : ∀ k ∈ s, k ≠ ⟨0,D.size_pos n⟩) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hfourth : ∀ m : ℕ, m ≤ 2 → ∀ selection : Fin m → Fin (N n),
      Function.Injective selection → (∀ a, selection a ∈ s) → ∀ j1 j2 j3 j4,
      |D.empiricalFourthWickDiscrepancy n ω selection j1 j2 j3 j4| ≤ epsilon)
    (k : Fin (N n)) (hk : k ∈ s) (l : Fin (N n)) (hl : l ∈ s) (i j : Fin 4) :
    |∫ t, D.centeredProposalQuadratic n ω k i j t *
      D.centeredProposalQuadratic n ω l i j t ∂uniformOrientedProposals (N n) d| ≤
      2 * (if k = l then 1 else 0) + epsilon := by
  let leaf : Fin d := ⟨0,hd⟩
  by_cases hkl : k = l
  · subst l
    let selection : Fin 1 → Fin (N n) := fun _ => k
    have hinj : Function.Injective selection := fun a b hab => Subsingleton.elim a b
    have hfour := hfourth 1 (by omega) selection hinj (fun a => hk)
    simpa only [selection] using D.proposal_covariance_le_of_empiricalWick n ω hd selection hinj
      0 0 (hs k hk) (hs k hk) leaf epsilon hepsilon hfour i j
  · let selection : Fin 2 → Fin (N n) := ![k,l]
    have hinj : Function.Injective selection := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [selection]
    have hrange : ∀ a, selection a ∈ s := by
      intro a
      fin_cases a
      · exact hk
      · exact hl
    have hfour := hfourth 2 (by omega) selection hinj hrange
    simpa only [selection,Matrix.cons_val_zero,Matrix.cons_val_one] using
      D.proposal_covariance_le_of_empiricalWick n ω hd selection hinj
        0 1 (hs k hk) (hs l hl) leaf epsilon hepsilon hfour i j

end GeneralizedBulk.External.RegularSpectralData
