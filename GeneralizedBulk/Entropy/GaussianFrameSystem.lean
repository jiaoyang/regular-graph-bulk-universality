import GeneralizedBulk.Entropy.ChaosSquares

/-! A finite geometric realization of the Gaussian star observation channels.
The operators and admissibility below use actual Gaussian conditional laws. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Hermite
variable (I C P : Type*) [Fintype I] [DecidableEq I] [Fintype C] [Fintype P]

/-- This contains only finite Euclidean geometry. The Gaussian operators are
constructed from it by `subspaceConditionalL2`; no analytic channel estimates
are fields of this structure. -/
structure GaussianFrameSystem where
  coordinates : C → Matrix I I ℝ
  orthogonal : ∀ c, coordinates c * (coordinates c).transpose = 1
  observed : C → Finset I
  directionA : C → P → I → ℝ
  directionB : C → P → I → ℝ
  weightA : C → P → ℝ
  weightB : C → P → ℝ
  retainedA : ∀ c p, directionA c p ∈ observationSubspace (coordinates c) (observed c)
  retainedB : ∀ c p, directionB c p ∈ observationSubspace (coordinates c) (observed c)
  weight_sum : ∀ c p, weightA c p + weightB c p = 1
  global_frame : ∀ u : I → ℝ, (∑ c, ∑ p,
    (weightA c p * (∑ i, directionA c p i * u i) ^ 2 +
      weightB c p * (∑ i, directionB c p i * u i) ^ 2)) = ∑ i, u i ^ 2
  observation_frame : ∀ c u, u ∈ observationSubspace (coordinates c) (observed c) →
    (∑ p, ((∑ i, directionA c p i * u i) ^ 2 + (∑ i, directionB c p i * u i) ^ 2)) = ∑ i, u i ^ 2
  reversal : C → Matrix I I ℝ
  reversal_orthogonal : ∀ c, reversal c * (reversal c).transpose = 1
  reversal_swap : ∀ c p, (reversal c).mulVec (directionA c p) = directionB c p

namespace GaussianFrameSystem
variable {I C P} (G : GaussianFrameSystem I C P)

def channel (c : C) : Lp ℝ 2 (standardGaussian I) →L[ℝ] Lp ℝ 2 (standardGaussian I) :=
  subspaceConditionalL2 (G.coordinates c) (G.orthogonal c) (G.observed c)

def defect (f : Lp ℝ 2 (standardGaussian I)) : ℝ :=
  gaussianChannelDefect G.coordinates G.orthogonal G.observed f

/-- Source marginal reversal symmetry, imposed on the actual conditional
Gaussian L² functions. -/
def Admissible (f : Lp ℝ 2 (standardGaussian I)) : Prop :=
  ∀ c, gaussianPullback (G.reversal c) (G.reversal_orthogonal c) (G.channel c f) = G.channel c f

/-- Canonical full-chaos coefficients of the actual channel output. -/
def projectedCoeff (degree : ℕ) (coeff : DegreeIndex I degree → ℝ) (c : C) : DegreeIndex I degree → ℝ :=
  Classical.choose (show ∃ b, fullChaosMap I degree b = G.channel c (fullChaosMap I degree coeff) from
    subspaceConditionalL2_mem_fullChaos (G.coordinates c) (G.orthogonal c) (G.observed c) degree
      (show fullChaosMap I degree coeff ∈ fullChaosSpace I degree from ⟨coeff, rfl⟩))

theorem projectedCoeff_spec (degree : ℕ) (coeff : DegreeIndex I degree → ℝ) (c : C) :
    chaosLp (degreeIndexNat I) (G.projectedCoeff degree coeff c) = G.channel c (chaosLp (degreeIndexNat I) coeff) :=
  Classical.choose_spec (show ∃ b, fullChaosMap I degree b = G.channel c (fullChaosMap I degree coeff) from
    subspaceConditionalL2_mem_fullChaos (G.coordinates c) (G.orthogonal c) (G.observed c) degree
      (show fullChaosMap I degree coeff ∈ fullChaosSpace I degree from ⟨coeff, rfl⟩))

theorem projectedCoeff_reversal (degree : ℕ) (coeff : DegreeIndex I degree → ℝ)
    (hadm : G.Admissible (chaosLp (degreeIndexNat I) coeff)) (c : C) (x : I → ℝ) :
    chaosFunction (degreeIndexNat I) (G.projectedCoeff degree coeff c) ((G.reversal c).mulVec x) =
      chaosFunction (degreeIndexNat I) (G.projectedCoeff degree coeff c) x := by
  have heq : chaosLp (degreeIndexNat I) (G.projectedCoeff degree coeff c) =
      gaussianPullback (G.reversal c) (G.reversal_orthogonal c)
        (chaosLp (degreeIndexNat I) (G.projectedCoeff degree coeff c)) := by
    rw [G.projectedCoeff_spec, hadm c]
  have hf := chaosFunction_eq_pullback_of_lp_eq (degreeIndexNat I) (G.projectedCoeff degree coeff c)
    (degreeIndexNat I) (G.projectedCoeff degree coeff c) (G.reversal c) (G.reversal_orthogonal c)
    degree (fun a => (degreeIndexNat_sum I a).le) (fun a => (degreeIndexNat_sum I a).le) heq
  exact (congrFun hf x).symm

/-- The exact source defect identity for an actual admissible homogeneous
Gaussian polynomial. -/
theorem squares (degree : ℕ) (coeff : DegreeIndex I degree → ℝ)
    (hadm : G.Admissible (chaosLp (degreeIndexNat I) coeff)) :
    (degree : ℝ) * G.defect (chaosLp (degreeIndexNat I) coeff) =
      gaussianResidualEnergy G.coordinates G.orthogonal G.observed (degreeIndexNat I) coeff
        G.directionA G.directionB G.weightA G.weightB :=
  gaussianChannelDefect_squares G.coordinates G.orthogonal G.observed (degreeIndexNat I)
    (degreeIndexNat_injective I degree) coeff (fun _ => degreeIndexNat I)
    (fun _ => degreeIndexNat_injective I degree) (G.projectedCoeff degree coeff) degree
    (degreeIndexNat_sum I) (fun _ => degreeIndexNat_sum I) (G.projectedCoeff_spec degree coeff)
    G.directionA G.directionB G.weightA G.weightB G.retainedA G.retainedB G.weight_sum
    G.global_frame G.observation_frame G.reversal G.reversal_orthogonal G.reversal_swap
    (G.projectedCoeff_reversal degree coeff hadm)

/-- Positivity holds in every positive homogeneous degree. Constants are
excluded explicitly because their channel defect can be negative. -/
theorem defect_nonneg (degree : ℕ) (hdegree : 0 < degree) (coeff : DegreeIndex I degree → ℝ)
    (hadm : G.Admissible (chaosLp (degreeIndexNat I) coeff))
    (hA : ∀ c p, 0 ≤ G.weightA c p) (hB : ∀ c p, 0 ≤ G.weightB c p) :
    0 ≤ G.defect (chaosLp (degreeIndexNat I) coeff) := by
  have hh := gaussianResidualEnergy_nonneg G.coordinates G.orthogonal G.observed
    (degreeIndexNat I) coeff G.directionA G.directionB G.weightA G.weightB hA hB
  rw [← G.squares degree coeff hadm] at hh
  exact (mul_nonneg_iff_of_pos_left (Nat.cast_pos.mpr hdegree)).mp hh

/-- Zero source defect cancels the genuine directional residuals. -/
theorem zero_defect_residuals (degree : ℕ) (coeff : DegreeIndex I degree → ℝ)
    (hadm : G.Admissible (chaosLp (degreeIndexNat I) coeff))
    (hA : ∀ c p, 0 < G.weightA c p) (hB : ∀ c p, 0 < G.weightB c p)
    (hzero : G.defect (chaosLp (degreeIndexNat I) coeff) = 0) (c : C) (p : P) :
    (directionalLp (degreeIndexNat I) coeff (G.directionA c p) =
      G.channel c (directionalLp (degreeIndexNat I) coeff (G.directionA c p))) ∧
    (directionalLp (degreeIndexNat I) coeff (G.directionB c p) =
      G.channel c (directionalLp (degreeIndexNat I) coeff (G.directionB c p))) := by
  apply gaussianResidualEnergy_eq_zero_residuals G.coordinates G.orthogonal G.observed
    (degreeIndexNat I) coeff G.directionA G.directionB G.weightA G.weightB hA hB
  rw [← G.squares degree coeff hadm, hzero, mul_zero]

/-- The canceled residuals give pointwise derivative identities of the actual
polynomials, simultaneously at every Gaussian coordinate. -/
theorem zero_defect_pointwise (degree : ℕ) (coeff : DegreeIndex I degree → ℝ)
    (hadm : G.Admissible (chaosLp (degreeIndexNat I) coeff))
    (hA : ∀ c p, 0 < G.weightA c p) (hB : ∀ c p, 0 < G.weightB c p)
    (hzero : G.defect (chaosLp (degreeIndexNat I) coeff) = 0) (c : C) (p : P) (x : I → ℝ) :
    (fderiv ℝ (chaosFunction (degreeIndexNat I) coeff) x (G.directionA c p) =
      fderiv ℝ (chaosFunction (degreeIndexNat I) (G.projectedCoeff degree coeff c)) x (G.directionA c p)) ∧
    (fderiv ℝ (chaosFunction (degreeIndexNat I) coeff) x (G.directionB c p) =
      fderiv ℝ (chaosFunction (degreeIndexNat I) (G.projectedCoeff degree coeff c)) x (G.directionB c p)) := by
  have hr := G.zero_defect_residuals degree coeff hadm hA hB hzero c p
  have hcomm (v : I → ℝ) (hv : v ∈ observationSubspace (G.coordinates c) (G.observed c)) :=
    subspaceConditionalL2_directional (G.coordinates c) (G.orthogonal c) (G.observed c)
      (degreeIndexNat I) coeff (degreeIndexNat I) (G.projectedCoeff degree coeff c) degree
      (fun a => (degreeIndexNat_sum I a).le) (fun a => (degreeIndexNat_sum I a).le)
      (G.projectedCoeff_spec degree coeff c) v hv
  constructor
  · have hd := hr.1.trans (hcomm (G.directionA c p) (G.retainedA c p))
    exact congrFun (fderiv_eq_of_directionalLp_eq (degreeIndexNat I) coeff (G.directionA c p)
      (degreeIndexNat I) (G.projectedCoeff degree coeff c) (G.directionA c p) degree
      (fun a => (degreeIndexNat_sum I a).le) (fun a => (degreeIndexNat_sum I a).le) hd) x
  · have hd := hr.2.trans (hcomm (G.directionB c p) (G.retainedB c p))
    exact congrFun (fderiv_eq_of_directionalLp_eq (degreeIndexNat I) coeff (G.directionB c p)
      (degreeIndexNat I) (G.projectedCoeff degree coeff c) (G.directionB c p) degree
      (fun a => (degreeIndexNat_sum I a).le) (fun a => (degreeIndexNat_sum I a).le) hd) x

end GaussianFrameSystem
end GeneralizedBulk.Entropy.Hermite
