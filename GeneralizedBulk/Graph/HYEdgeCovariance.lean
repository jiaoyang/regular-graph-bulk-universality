import GeneralizedBulk.Graph.HYLocalStarCovariance
import GeneralizedBulk.Graph.StarCompression
import GeneralizedBulk.Graph.EndpointUniform
import GeneralizedBulk.Gaussian.EdgeReferenceBounds

/-! The actual root-port edge Gaussian covariance and its HY comparison. -/
noncomputable section
namespace GeneralizedBulk.External.RegularSpectralData
open Set MeasureTheory GeneralizedBulk.KestenMcKay GeneralizedBulk.Gaussian GeneralizedBulk.Covariance
variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω) (n : ℕ) (ω : Ω)

def edgeInStar (port : Fin d) : Fin 2 → Fin (d+1) := Fin.cases 0 (fun _ => port.succ)

@[simp] theorem edgeInStar_zero (port : Fin d) : edgeInStar port 0=0 := rfl
@[simp] theorem edgeInStar_one (port : Fin d) : edgeInStar port 1=port.succ := rfl

theorem edgeWaveCovariance_port_restriction (port : Fin d) (E : ℝ) :
    (starWaveCovariance d E).submatrix (edgeInStar port) (edgeInStar port)=edgeWaveCovariance d E := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [starWaveCovariance,edgeWaveCovariance,Matrix.submatrix_apply]

def localEntropyEdgeCovariance (s : Fin (N n) × Fin d) (E eta sigma : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (D.resolventCovariance n ω E eta sigma).submatrix (D.proposalEndpoint n ω s) (D.proposalEndpoint n ω s)

theorem localEntropyEdgeCovariance_star_restriction (s : Fin (N n) × Fin d) (E eta sigma : ℝ) :
    D.localEntropyEdgeCovariance n ω s E eta sigma=
      (D.localEntropyStarCovariance n ω s.1 E eta sigma).submatrix (edgeInStar s.2) (edgeInStar s.2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem localEntropyEdgeCovariance_posDef (s : Fin (N n) × Fin d) (E eta sigma : ℝ)
    (heta : 0 < eta) (hsigma : 0 < sigma) : (D.localEntropyEdgeCovariance n ω s E eta sigma).PosDef := by
  rw [localEntropyEdgeCovariance_star_restriction]
  apply posDef_submatrix_of_injective _ (D.localEntropyStarCovariance_posDef n ω s.1 E eta sigma heta hsigma)
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all
  exact Fin.succ_ne_zero _ h.symm

theorem HYLocalStar_edge_covariance_uniform {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : 3 ≤ (d : ℝ)) (K : Set ℝ) (hK : IsCompact K)
    (hbulk : ∀ E ∈ K,E^2 < 4*((d : ℝ)-1)) (c0 : ℝ)
    (H : HYLocalStarInput D P K c0 (treeGreenStar d hd)) :
    ∃ C : ℝ,0 < C ∧ ∀ n,H.events.threshold ≤ n → ∀ ω ∈ H.events.good n,
      ∀ s : Fin (N n) × Fin d,s.1 ∉ H.badRoots n ω → ∀ E ∈ K,∀ i j : Fin 2,
      |(D.localEntropyEdgeCovariance n ω s E ((N n : ℝ)^(-c0)) (diagonalBoundary d E).im-edgeWaveCovariance d E) i j| ≤
        C*((N n : ℝ)^(-H.local_exponent)+(N n : ℝ)^(-c0)) := by
  obtain ⟨C,hC,hclose⟩ := D.HYLocalStar_covariance_rate_uniform hd K hK hbulk c0 H
  refine ⟨C,hC,?_⟩
  intro n hn ω hω s hs E hE i j
  have hh := hclose n hn ω hω s.1 hs E hE (edgeInStar s.2 i) (edgeInStar s.2 j)
  rw [localEntropyEdgeCovariance_star_restriction,← edgeWaveCovariance_port_restriction s.2 E]
  exact hh

end GeneralizedBulk.External.RegularSpectralData
