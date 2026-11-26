import GeneralizedBulk.Graph.ProposalFiberVariance
import LocalLaw.GraphModel
import SpectralConsequences.PaperAllEigenvectors

/-! Exact deterministic normalization bridge to the imported local law.
The source uses A / sqrt(d-1); the bulk article uses A. These identities
refer to the same finite labelled graph and actual matrix inverse. -/
noncomputable section
open MeasureTheory Matrix
open scoped Classical BigOperators

namespace GeneralizedBulk.External.RegularSpectralData

variable {d : ℕ} {N : ℕ → ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable (D : RegularSpectralData d N Ω)

/-- The source and bulk graph spaces have the same labelled graph values. -/
def localLawGraph (n : ℕ) (ω : Ω) : LocalLaw.RegularGraph (N n) d :=
  D.spectralRegularGraph n ω

theorem localLawGraph_adjacency (n : ℕ) (ω : Ω) :
    (D.localLawGraph n ω).graph.adjMatrix ℂ =
      (D.adjacency n ω).map Complex.ofReal :=
  D.simpleGraph_adjacency_complex n ω

theorem localLawGraph_H (n : ℕ) (ω : Ω) :
    (D.localLawGraph n ω).H =
      ((Real.sqrt ((d : ℝ) - 1) : ℂ)⁻¹) •
        (D.adjacency n ω).map Complex.ofReal := by
  rw [LocalLaw.RegularGraph.H, LocalLaw.normalizedAdjacency,
    D.localLawGraph_adjacency]
  simp only [Complex.ofReal_inv]

/-- Resolvents scale inversely to the physical adjacency normalization. -/
theorem resolvent_eq_localLaw_green (hd : 3 ≤ d) (n : ℕ) (ω : Ω)
    (z : ℂ) (hz : 0 < z.im) :
    D.resolvent n ω z =
      ((Real.sqrt ((d : ℝ) - 1) : ℂ)⁻¹) •
        (D.localLawGraph n ω).G (z / (Real.sqrt ((d : ℝ) - 1) : ℂ)) := by
  let s : ℝ := Real.sqrt ((d : ℝ) - 1)
  have hdreal : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hs : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hsc : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hzim : 0 < (z / (s : ℂ)).im := by
    simpa only [Complex.div_ofReal_im] using div_pos hz hs
  have hmatrix : (D.adjacency n ω).map Complex.ofReal - z • 1 =
      (s : ℂ) • LocalLaw.spectralMatrix (D.localLawGraph n ω).H (z / (s : ℂ)) := by
    rw [LocalLaw.spectralMatrix, D.localLawGraph_H, smul_sub, smul_smul,
      smul_smul]
    change _ = ((s : ℂ) * (s : ℂ)⁻¹) • _ - ((s : ℂ) * (z / (s : ℂ))) • _
    rw [mul_inv_cancel₀ hsc, one_smul]
    congr 2
    field_simp
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp
    (LocalLaw.spectralMatrix_isUnit _ (D.localLawGraph n ω).H_hermitian
      (z / (s : ℂ)) hzim)
  letI : Invertible (s : ℂ) := invertibleOfNonzero hsc
  change ((_ : Matrix (Fin (N n)) (Fin (N n)) ℂ))⁻¹ = _
  rw [hmatrix, Matrix.inv_smul _ _ hdet]
  simp only [invOf_eq_inv]
  rfl

theorem scalarResolvent_eq_localLaw_transform (hd : 3 ≤ d) (n : ℕ) (ω : Ω)
    (z : ℂ) (hz : 0 < z.im) :
    D.scalarResolvent n ω z =
      ((Real.sqrt ((d : ℝ) - 1) : ℂ)⁻¹) *
        LocalLaw.empiricalTransform (D.localLawGraph n ω).H
          (z / (Real.sqrt ((d : ℝ) - 1) : ℂ)) := by
  rw [scalarResolvent, D.resolvent_eq_localLaw_green hd n ω z hz,
    Matrix.trace_smul]
  simp only [LocalLaw.empiricalTransform, LocalLaw.RegularGraph.G,
    Fintype.card_fin, smul_eq_mul]
  ring

/-- The source all-eigenspace statement yields exactly the deterministic
real, unit-vector bound used in the coarse HY contract. -/
theorem delocalization_of_localLaw (n : ℕ) (ω : Ω)
    (hdeloc : SpectralConsequences.PaperAllEigenvectors (D.localLawGraph n ω))
    (q : Fin (N n) → ℝ) (energy : ℝ) (hq : ∑ v, q v ^ 2 = 1)
    (heigen : ∀ v, ∑ w, D.adjacency n ω v w * q w = energy * q v)
    (v : Fin (N n)) :
    Real.sqrt (N n) * |q v| ≤ Real.log (N n) ^ 151 := by
  have he : (D.localLawGraph n ω).H *ᵥ (fun w => (q w : ℂ)) =
      ((energy : ℂ) / (Real.sqrt ((d : ℝ) - 1) : ℂ)) • (fun w => (q w : ℂ)) := by
    have he' : (D.adjacency n ω).map Complex.ofReal *ᵥ (fun w => (q w : ℂ)) =
        (energy : ℂ) • (fun w => (q w : ℂ)) := by
      ext i
      simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply,
        smul_eq_mul, Complex.ofReal_sum, Complex.ofReal_mul] using
        congrArg Complex.ofReal (heigen i)
    rw [D.localLawGraph_H, Matrix.smul_mulVec_assoc, he', smul_smul]
    congr 1
    simp only [div_eq_mul_inv, mul_comm]
  have hnorm : (∑ w : Fin (N n), ‖(q w : ℂ)‖ ^ 2) = 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using hq
  have hb := hdeloc _ (fun w => (q w : ℂ)) he
  rw [hnorm, Real.sqrt_one, mul_one] at hb
  have hv : |q v| ≤ Real.log (N n) ^ 151 / Real.sqrt (N n) := by
    calc
      |q v| = ‖(q v : ℂ)‖ := by simp
      _ ≤ ‖fun w : Fin (N n) => (q w : ℂ)‖ :=
        norm_le_pi_norm (fun w : Fin (N n) => (q w : ℂ)) v
      _ ≤ _ := hb
  have hs : 0 < Real.sqrt (N n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (D.size_pos n))
  have hv' := (le_div_iff₀ hs).mp hv
  simpa only [mul_comm] using hv'

end GeneralizedBulk.External.RegularSpectralData
