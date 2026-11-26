import Mathlib

/-!
# BS upper bound: weighted frame and actual conditional Fisher squares

This is stage U3 of the separately written upper-bound blueprint. The finite
frame is constructed explicitly, and conditional observation uses mathlib's
actual L2 conditional expectation. No entropy upper bound, de Bruijn identity,
or Gaussian classification is assumed or claimed here. The analytic score
projection and heat-flow identities are separate stages U1--U2.

The elementary coefficients are adapted from the earlier project's proved
Entropy/ChannelFrames module, without importing that project.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace GaussianWave.BS

def rho (c : ℝ) : ℝ := Real.sqrt (1 - c ^ 2)
def alpha (c : ℝ) : ℝ := (Real.sqrt (1 + c) + Real.sqrt (1 - c)) / 2
def beta (c : ℝ) : ℝ := (Real.sqrt (1 + c) - Real.sqrt (1 - c)) / 2

theorem rho_pos (c : ℝ) (hc : |c| < 1) : 0 < rho c := by
  apply Real.sqrt_pos.mpr
  exact sub_pos.mpr ((sq_lt_one_iff_abs_lt_one c).mpr hc)

theorem rho_sq (c : ℝ) (hc : |c| < 1) : rho c ^ 2 = 1 - c ^ 2 :=
  Real.sq_sqrt (sub_nonneg.mpr ((sq_lt_one_iff_abs_lt_one c).mpr hc).le)

theorem alpha_sq_add_beta_sq (c : ℝ) (hc : |c| < 1) : alpha c ^ 2 + beta c ^ 2 = 1 := by
  have hp := Real.sq_sqrt (by linarith [(abs_lt.mp hc).1] : 0 ≤ 1 + c)
  have hm := Real.sq_sqrt (by linarith [(abs_lt.mp hc).2] : 0 ≤ 1 - c)
  dsimp [alpha, beta]
  nlinarith

theorem two_alpha_mul_beta (c : ℝ) (hc : |c| < 1) : 2 * alpha c * beta c = c := by
  have hp := Real.sq_sqrt (by linarith [(abs_lt.mp hc).1] : 0 ≤ 1 + c)
  have hm := Real.sq_sqrt (by linarith [(abs_lt.mp hc).2] : 0 ≤ 1 - c)
  dsimp [alpha, beta]
  nlinarith

theorem alpha_sq_sub_beta_sq (c : ℝ) (hc : |c| < 1) : alpha c ^ 2 - beta c ^ 2 = rho c := by
  have hp : 0 ≤ 1 + c := by linarith [(abs_lt.mp hc).1]
  have hmul : Real.sqrt (1 + c) * Real.sqrt (1 - c) = rho c := by
    rw [← Real.sqrt_mul hp]
    unfold rho
    congr 1
    ring
  dsimp [alpha, beta]
  nlinarith

theorem alpha_sq (c : ℝ) (hc : |c| < 1) : alpha c ^ 2 = (1 + rho c) / 2 := by
  nlinarith [alpha_sq_add_beta_sq c hc, alpha_sq_sub_beta_sq c hc]

theorem beta_sq (c : ℝ) (hc : |c| < 1) : beta c ^ 2 = (1 - rho c) / 2 := by
  nlinarith [alpha_sq_add_beta_sq c hc, alpha_sq_sub_beta_sq c hc]

def weightA (d : ℕ) (c : ℝ) : ℝ := (rho c - 1 + 2 / (d : ℝ)) / (2 * rho c)
def weightB (d : ℕ) (c : ℝ) : ℝ := (rho c + 1 - 2 / (d : ℝ)) / (2 * rho c)

theorem weight_sum (d : ℕ) (c : ℝ) (hc : |c| < 1) : weightA d c + weightB d c = 1 := by
  unfold weightA weightB
  field_simp [ne_of_gt (rho_pos c hc)]
  ring

/-- The regular-graph bulk interval is exactly the strict positivity condition
for the weighted frame. No channel-coercivity hypothesis enters this proof. -/
theorem bulk_rho_lower (d : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2) :
    |c| < 1 ∧ 1 - 2 / (d : ℝ) < rho c := by
  have hdp : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hb : 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2 ≤ 1 := by
    apply (div_le_iff₀ (sq_pos_of_pos hdp)).2
    nlinarith [sq_nonneg ((d : ℝ) - 2)]
  have hc : |c| < 1 := (sq_lt_one_iff_abs_lt_one c).mp (hbulk.trans_le hb)
  refine ⟨hc, ?_⟩
  have ht : 0 ≤ 1 - 2 / (d : ℝ) := by
    have hh : 2 / (d : ℝ) ≤ 1 := (div_le_iff₀ hdp).2 (by linarith)
    linarith
  apply (sq_lt_sq₀ ht (rho_pos c hc).le).mp
  rw [rho_sq c hc]
  have hid : 1 - (1 - 2 / (d : ℝ)) ^ 2 = 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2 := by
    field_simp
    ring
  linarith

theorem bulk_weights_pos (d : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2) :
    0 < weightA d c ∧ 0 < weightB d c := by
  obtain ⟨hc, hr⟩ := bulk_rho_lower d hd c hbulk
  have hp := rho_pos c hc
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hdp : (0 : ℝ) < d := by linarith
  have ht : 0 < 1 - 2 / (d : ℝ) := by
    have hh : 2 / (d : ℝ) < 1 := (div_lt_iff₀ hdp).2 (by linarith)
    linarith
  constructor <;> simp only [weightA, weightB] <;> apply div_pos _ (by positivity) <;> linarith

theorem frame_scalar_weight (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1) :
    weightA d c * alpha c ^ 2 + weightB d c * beta c ^ 2 = 1 / (d : ℝ) := by
  rw [alpha_sq c hc, beta_sq c hc]
  unfold weightA weightB
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  field_simp [ne_of_gt (rho_pos c hc), hd0]
  ring

theorem frame_transverse_weight (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1) :
    weightA d c * beta c ^ 2 + weightB d c * alpha c ^ 2 = ((d : ℝ) - 1) / (d : ℝ) := by
  rw [alpha_sq c hc, beta_sq c hc]
  unfold weightA weightB
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  field_simp [ne_of_gt (rho_pos c hc), hd0]
  ring


/-- Inner product with a unit regular-simplex direction in centered leaf
coordinates is this scale times the corresponding centered coordinate. -/
def transverseScale (d : ℕ) : ℝ := Real.sqrt ((d : ℝ) / ((d : ℝ) - 1))

theorem transverseScale_sq (d : ℕ) (hd : 2 ≤ d) :
    transverseScale d ^ 2 = (d : ℝ) / ((d : ℝ) - 1) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  exact Real.sq_sqrt (div_nonneg (by linarith) (by linarith))

section HilbertFrame
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Score in the first endpoint-adapted unit direction. -/
def scoreA (c : ℝ) (root transverse : H) : H := alpha c • root - beta c • transverse

/-- Score in the second endpoint-adapted unit direction. -/
def scoreB (c : ℝ) (root transverse : H) : H := beta c • root + alpha c • transverse

lemma norm_scoreA_sq (c : ℝ) (r q : H) :
    ‖scoreA c r q‖ ^ 2 = alpha c ^ 2 * ‖r‖ ^ 2 -
      2 * alpha c * beta c * @inner ℝ H _ r q + beta c ^ 2 * ‖q‖ ^ 2 := by
  rw [scoreA, norm_sub_sq_real, real_inner_smul_left, real_inner_smul_right]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

lemma norm_scoreB_sq (c : ℝ) (r q : H) :
    ‖scoreB c r q‖ ^ 2 = beta c ^ 2 * ‖r‖ ^ 2 +
      2 * alpha c * beta c * @inner ℝ H _ r q + alpha c ^ 2 * ‖q‖ ^ 2 := by
  rw [scoreB, norm_add_sq_real, real_inner_smul_left, real_inner_smul_right]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

lemma weighted_pair_energy (d : ℕ) (c : ℝ) (r q : H) :
    weightA d c * ‖scoreA c r q‖ ^ 2 + weightB d c * ‖scoreB c r q‖ ^ 2 =
      (weightA d c * alpha c ^ 2 + weightB d c * beta c ^ 2) * ‖r‖ ^ 2 +
      (weightA d c * beta c ^ 2 + weightB d c * alpha c ^ 2) * ‖q‖ ^ 2 +
      (2 * alpha c * beta c * (weightB d c - weightA d c)) * @inner ℝ H _ r q := by
  rw [norm_scoreA_sq, norm_scoreB_sq]
  ring

/-- Literal weighted frame identity, valid in any real Hilbert space. In the
score application H=L2(P), so this is already the integrated Fisher energy. -/
theorem scalar_frame_energy (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1)
    (r : H) (z : Fin d → H) (hz : ∑ i, z i = 0) :
    (∑ i, (weightA d c * ‖scoreA c r (transverseScale d • z i)‖ ^ 2 +
      weightB d c * ‖scoreB c r (transverseScale d • z i)‖ ^ 2)) =
      ‖r‖ ^ 2 + ∑ i, ‖z i‖ ^ 2 := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hd1 : (d : ℝ) - 1 ≠ 0 := by linarith
  have hsum : (∑ i, transverseScale d • z i) = 0 := by rw [← Finset.smul_sum, hz, smul_zero]
  have hcross : (∑ i, @inner ℝ H _ r (transverseScale d • z i)) = 0 := by
    rw [← inner_sum, hsum, inner_zero_right]
  have hnorm : (∑ i, ‖transverseScale d • z i‖ ^ 2) =
      (d : ℝ) / ((d : ℝ) - 1) * ∑ i, ‖z i‖ ^ 2 := by
    simp_rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, transverseScale_sq d hd]
    exact (Finset.mul_sum ..).symm
  have he (i : Fin d) :
      weightA d c * ‖scoreA c r (transverseScale d • z i)‖ ^ 2 +
      weightB d c * ‖scoreB c r (transverseScale d • z i)‖ ^ 2 =
        (1 / (d : ℝ)) * ‖r‖ ^ 2 + ((d : ℝ) - 1) / (d : ℝ) *
          ‖transverseScale d • z i‖ ^ 2 +
        (2 * alpha c * beta c * (weightB d c - weightA d c)) *
          @inner ℝ H _ r (transverseScale d • z i) := by
    rw [weighted_pair_energy, frame_scalar_weight d hd c hc, frame_transverse_weight d hd c hc]
  simp_rw [he, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, hcross, mul_zero, add_zero, hnorm]
  field_simp
  ring

/-- Common-energy multichannel frame. Each channel has its own root score and
centered transverse coordinates; the frame weights are shared. -/
theorem colored_frame_energy (d k : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1)
    (r : Fin k → H) (z : Fin k → Fin d → H) (hz : ∀ a, ∑ i, z a i = 0) :
    (∑ a, ∑ i, (weightA d c * ‖scoreA c (r a) (transverseScale d • z a i)‖ ^ 2 +
      weightB d c * ‖scoreB c (r a) (transverseScale d • z a i)‖ ^ 2)) =
      ∑ a, (‖r a‖ ^ 2 + ∑ i, ‖z a i‖ ^ 2) := by
  apply Finset.sum_congr rfl
  intro a _
  exact scalar_frame_energy d hd c hc (r a) (z a) (hz a)

end HilbertFrame

/-- The two endpoint-adapted root coefficients are exchanged by the actual
root/leaf reflection matrix [[c,rho],[rho,−c]]. -/
theorem reversal_coefficients (c : ℝ) (hc : |c| < 1) :
    alpha c * c - beta c * rho c = beta c ∧
      alpha c * rho c + beta c * c = alpha c := by
  constructor
  · have h1 := congrArg (fun x : ℝ => alpha c * x) (two_alpha_mul_beta c hc)
    have h2 := congrArg (fun x : ℝ => beta c * x) (alpha_sq_sub_beta_sq c hc)
    have h3 := congrArg (fun x : ℝ => beta c * x) (alpha_sq_add_beta_sq c hc)
    simp only [mul_one] at h1 h2 h3
    linear_combination -h1 + h2 + h3
  · have h1 := congrArg (fun x : ℝ => beta c * x) (two_alpha_mul_beta c hc)
    have h2 := congrArg (fun x : ℝ => alpha c * x) (alpha_sq_sub_beta_sq c hc)
    have h3 := congrArg (fun x : ℝ => alpha c * x) (alpha_sq_add_beta_sq c hc)
    simp only [mul_one] at h1 h2 h3
    linear_combination -h1 - h2 + h3

end GaussianWave.BS

namespace GaussianWave.BS

section ConditionalScores
variable {Ω : Type*} [m0 : MeasurableSpace Ω] (P : Measure Ω)

/-- The score Hilbert space for an arbitrary law P, not a Gaussian reference. -/
abbrev ScoreSpace := Lp ℝ 2 P

/-- Actual conditional expectation onto the edge observation sigma-algebra. -/
def conditionalScore (m : MeasurableSpace Ω) (hm : m ≤ m0)
    (u : ScoreSpace (m0 := m0) P) : ScoreSpace (m0 := m0) P := (condExpL2 ℝ ℝ (m0 := m0) hm u : ScoreSpace (m0 := m0) P)

lemma orthogonal_projection_residual_norm_sq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (K : Submodule ℝ H) [K.HasOrthogonalProjection] (u : H) :
    ‖u - (K.orthogonalProjection u : H)‖ ^ 2 =
      ‖u‖ ^ 2 - ‖(K.orthogonalProjection u : H)‖ ^ 2 := by
  have hi : @inner ℝ H _ u (K.orthogonalProjection u : H) =
      ‖(K.orthogonalProjection u : H)‖ ^ 2 := by
    have h := Submodule.inner_orthogonalProjection_eq_of_mem_right K (K.orthogonalProjection u) u
    simpa only [Submodule.coe_inner, real_inner_self_eq_norm_sq] using h.symm
  rw [norm_sub_sq_real, hi]
  ring

/-- Conditional-score contraction is derived from its exact orthogonal square
identity; it is not supplied as an assumed Fisher-information inequality. -/
theorem conditionalScore_residual_norm_sq (m : MeasurableSpace Ω)
    (hm : m ≤ m0) (u : ScoreSpace (m0 := m0) P) :
    ‖u - conditionalScore (m0 := m0) P m hm u‖ ^ 2 =
      ‖u‖ ^ 2 - ‖conditionalScore (m0 := m0) P m hm u‖ ^ 2 := by
  letI : MeasurableSpace Ω := m0
  letI : Fact (m ≤ m0) := ⟨hm⟩
  exact orthogonal_projection_residual_norm_sq (lpMeas ℝ ℝ m 2 P) u

def frameScoreA {d k : ℕ} (c : ℝ) (r : Fin k → ScoreSpace (m0 := m0) P)
    (z : Fin k → Fin d → ScoreSpace (m0 := m0) P) (a : Fin k) (i : Fin d) : ScoreSpace (m0 := m0) P :=
  scoreA c (r a) (transverseScale d • z a i)

def frameScoreB {d k : ℕ} (c : ℝ) (r : Fin k → ScoreSpace (m0 := m0) P)
    (z : Fin k → Fin d → ScoreSpace (m0 := m0) P) (a : Fin k) (i : Fin d) : ScoreSpace (m0 := m0) P :=
  scoreB c (r a) (transverseScale d • z a i)

/-- Full Fisher energy of the root and centered transverse score components. -/
def fullScoreEnergy {d k : ℕ} (r : Fin k → ScoreSpace (m0 := m0) P)
    (z : Fin k → Fin d → ScoreSpace (m0 := m0) P) : ℝ :=
  ∑ a, (‖r a‖ ^ 2 + ∑ i, ‖z a i‖ ^ 2)

/-- Sum of the edge score energies in their two orthonormal direction families. -/
def observedScoreEnergy {d k : ℕ} (c : ℝ) (r : Fin k → ScoreSpace (m0 := m0) P)
    (z : Fin k → Fin d → ScoreSpace (m0 := m0) P) (m : Fin d → MeasurableSpace Ω)
    (hm : ∀ i, m i ≤ m0) : ℝ :=
  ∑ a, ∑ i, (‖conditionalScore (m0 := m0) P (m i) (hm i) (frameScoreA P c r z a i)‖ ^ 2 +
    ‖conditionalScore (m0 := m0) P (m i) (hm i) (frameScoreB P c r z a i)‖ ^ 2)

def fisherDefect {d k : ℕ} (c : ℝ) (r : Fin k → ScoreSpace (m0 := m0) P)
    (z : Fin k → Fin d → ScoreSpace (m0 := m0) P) (m : Fin d → MeasurableSpace Ω)
    (hm : ∀ i, m i ≤ m0) : ℝ :=
  fullScoreEnergy P r z - (1 / 2 : ℝ) * observedScoreEnergy P c r z m hm

def conditionalResidualEnergy {d k : ℕ} (c : ℝ) (r : Fin k → ScoreSpace (m0 := m0) P)
    (z : Fin k → Fin d → ScoreSpace (m0 := m0) P) (m : Fin d → MeasurableSpace Ω)
    (hm : ∀ i, m i ≤ m0) : ℝ :=
  ∑ a, ∑ i, (weightA d c * ‖frameScoreA P c r z a i -
      conditionalScore (m0 := m0) P (m i) (hm i) (frameScoreA P c r z a i)‖ ^ 2 +
    weightB d c * ‖frameScoreB P c r z a i -
      conditionalScore (m0 := m0) P (m i) (hm i) (frameScoreB P c r z a i)‖ ^ 2)

/-- Source Lemma11.4 + frame identity, with actual conditional observations.
The reversal hypothesis is only equality of the two observed directional
energies, to be derived from the root/leaf marginal symmetry of a score law. -/
theorem fisherDefect_eq_conditionalResidualEnergy
    (d k : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : |c| < 1)
    (r : Fin k → ScoreSpace (m0 := m0) P) (z : Fin k → Fin d → ScoreSpace (m0 := m0) P)
    (hz : ∀ a, ∑ i, z a i = 0)
    (m : Fin d → MeasurableSpace Ω) (hm : ∀ i, m i ≤ m0)
    (hreversal : ∀ a i,
      ‖conditionalScore (m0 := m0) P (m i) (hm i) (frameScoreA P c r z a i)‖ ^ 2 =
      ‖conditionalScore (m0 := m0) P (m i) (hm i) (frameScoreB P c r z a i)‖ ^ 2) :
    fisherDefect P c r z m hm = conditionalResidualEnergy P c r z m hm := by
  have hlocal (a : Fin k) (i : Fin d) :
      weightA d c * ‖frameScoreA P c r z a i‖ ^ 2 +
      weightB d c * ‖frameScoreB P c r z a i‖ ^ 2 -
        (1 / 2 : ℝ) * (‖conditionalScore (m0 := m0) P (m i) (hm i) (frameScoreA P c r z a i)‖ ^ 2 +
          ‖conditionalScore (m0 := m0) P (m i) (hm i) (frameScoreB P c r z a i)‖ ^ 2) =
      weightA d c * ‖frameScoreA P c r z a i -
        conditionalScore (m0 := m0) P (m i) (hm i) (frameScoreA P c r z a i)‖ ^ 2 +
      weightB d c * ‖frameScoreB P c r z a i -
        conditionalScore (m0 := m0) P (m i) (hm i) (frameScoreB P c r z a i)‖ ^ 2 := by
    rw [conditionalScore_residual_norm_sq, conditionalScore_residual_norm_sq, hreversal a i]
    have hw := congrArg (fun w : ℝ => w *
      ‖conditionalScore (m0 := m0) P (m i) (hm i) (frameScoreB P c r z a i)‖ ^ 2) (weight_sum d c hc)
    simp only [mul_one] at hw
    linear_combination hw
  unfold fisherDefect fullScoreEnergy observedScoreEnergy conditionalResidualEnergy
  rw [← colored_frame_energy d k hd c hc r z hz]
  change (∑ a, ∑ i, (weightA d c * ‖frameScoreA P c r z a i‖ ^ 2 +
      weightB d c * ‖frameScoreB P c r z a i‖ ^ 2)) - _ = _
  simp_rw [← hlocal, Finset.sum_sub_distrib, Finset.mul_sum]

/-- Strict-bulk Fisher nonnegativity follows from actual conditional-square
residuals. No entropy derivative or entropy upper bound occurs as a premise. -/
theorem fisherDefect_nonneg
    (d k : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (r : Fin k → ScoreSpace (m0 := m0) P) (z : Fin k → Fin d → ScoreSpace (m0 := m0) P)
    (hz : ∀ a, ∑ i, z a i = 0)
    (m : Fin d → MeasurableSpace Ω) (hm : ∀ i, m i ≤ m0)
    (hreversal : ∀ a i,
      ‖conditionalScore (m0 := m0) P (m i) (hm i) (frameScoreA P c r z a i)‖ ^ 2 =
      ‖conditionalScore (m0 := m0) P (m i) (hm i) (frameScoreB P c r z a i)‖ ^ 2) :
    0 ≤ fisherDefect P c r z m hm := by
  rw [fisherDefect_eq_conditionalResidualEnergy P d k (by omega) c
    (bulk_rho_lower d hd c hbulk).1 r z hz m hm hreversal]
  exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun i _ =>
    add_nonneg (mul_nonneg (bulk_weights_pos d hd c hbulk).1.le (sq_nonneg _))
      (mul_nonneg (bulk_weights_pos d hd c hbulk).2.le (sq_nonneg _))

end ConditionalScores
end GaussianWave.BS

namespace GaussianWave.BS
section ConditionalEquality
variable {Ω : Type*} [m0 : MeasurableSpace Ω] (P : Measure Ω)

/-- In the strict bulk, equality of the Fisher defect forces every actual
conditional observation to fix both families of directional scores. This is
the L2 equality input for the later smooth log-density rigidity proof. -/
theorem fisherDefect_eq_zero_scores_fixed
    (d k : ℕ) (hd : 3 ≤ d) (c : ℝ)
    (hbulk : c ^ 2 < 4 * ((d : ℝ) - 1) / (d : ℝ) ^ 2)
    (r : Fin k → ScoreSpace P) (z : Fin k → Fin d → ScoreSpace P)
    (hz : ∀ a, ∑ i, z a i = 0)
    (m : Fin d → MeasurableSpace Ω) (hm : ∀ i, m i ≤ m0)
    (hreversal : ∀ a i,
      ‖conditionalScore P (m i) (hm i) (frameScoreA P c r z a i)‖ ^ 2 =
      ‖conditionalScore P (m i) (hm i) (frameScoreB P c r z a i)‖ ^ 2)
    (hzero : fisherDefect P c r z m hm = 0) :
    ∀ a i,
      conditionalScore P (m i) (hm i) (frameScoreA P c r z a i) = frameScoreA P c r z a i ∧
      conditionalScore P (m i) (hm i) (frameScoreB P c r z a i) = frameScoreB P c r z a i := by
  classical
  have hweights := bulk_weights_pos d hd c hbulk
  let A := frameScoreA P c r z
  let B := frameScoreB P c r z
  let CA := fun a i => conditionalScore P (m i) (hm i) (A a i)
  let CB := fun a i => conditionalScore P (m i) (hm i) (B a i)
  let term := fun a i => weightA d c * ‖A a i - CA a i‖ ^ 2 +
    weightB d c * ‖B a i - CB a i‖ ^ 2
  have hnonneg (a : Fin k) (i : Fin d) : 0 ≤ term a i :=
    add_nonneg (mul_nonneg hweights.1.le (sq_nonneg _))
      (mul_nonneg hweights.2.le (sq_nonneg _))
  have hsum : (∑ a, ∑ i, term a i) = 0 := by
    change conditionalResidualEnergy P c r z m hm = 0
    rw [← fisherDefect_eq_conditionalResidualEnergy P d k (by omega) c
      (bulk_rho_lower d hd c hbulk).1 r z hz m hm hreversal]
    exact hzero
  intro a i
  have hrow : (∑ i, term a i) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun a _ =>
      Finset.sum_nonneg (fun i _ => hnonneg a i))).mp hsum a (Finset.mem_univ a)
  have hterm : term a i = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnonneg a i)).mp hrow i (Finset.mem_univ i)
  have hAz : weightA d c * ‖A a i - CA a i‖ ^ 2 = 0 := by
    have hb : 0 ≤ weightB d c * ‖B a i - CB a i‖ ^ 2 := mul_nonneg hweights.2.le (sq_nonneg _)
    dsimp [term] at hterm
    have ha : 0 ≤ weightA d c * ‖A a i - CA a i‖ ^ 2 := mul_nonneg hweights.1.le (sq_nonneg _)
    linarith
  have hBz : weightB d c * ‖B a i - CB a i‖ ^ 2 = 0 := by
    dsimp [term] at hterm
    linarith
  have hAsq : ‖A a i - CA a i‖ ^ 2 = 0 :=
    (mul_eq_zero.mp hAz).resolve_left (ne_of_gt hweights.1)
  have hBsq : ‖B a i - CB a i‖ ^ 2 = 0 :=
    (mul_eq_zero.mp hBz).resolve_left (ne_of_gt hweights.2)
  have hAn : ‖A a i - CA a i‖ = 0 := by nlinarith [norm_nonneg (A a i - CA a i)]
  have hBn : ‖B a i - CB a i‖ = 0 := by nlinarith [norm_nonneg (B a i - CB a i)]
  exact ⟨(sub_eq_zero.mp (norm_eq_zero.mp hAn)).symm,
    (sub_eq_zero.mp (norm_eq_zero.mp hBn)).symm⟩

end ConditionalEquality
end GaussianWave.BS

namespace GaussianWave.BS

/-- The Hilbert norms in the conditional-score theorem are literal Fisher
square integrals against the arbitrary score law P. -/
theorem score_norm_sq_eq_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (u : ScoreSpace P) : ‖u‖ ^ 2 = ∫ ω, u ω ^ 2 ∂P := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [] with ω
  simp [RCLike.inner_apply, pow_two]

end GaussianWave.BS
