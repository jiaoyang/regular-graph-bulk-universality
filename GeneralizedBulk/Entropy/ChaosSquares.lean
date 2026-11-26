import GeneralizedBulk.Entropy.ChaosFrameEnergy

/-! The genuine Gaussian channel defect is a sum of squared derivative
residuals. Only finite-dimensional frame and reversal identities enter. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Hermite
variable {I K J C P : Type*} [Fintype I] [DecidableEq I]
  [Fintype K] [Fintype J] [Fintype C] [Fintype P]

def gaussianChannelDefect (O : C → Matrix I I ℝ) (hO : ∀ c, O c * (O c).transpose = 1)
    (observed : C → Finset I) (f : Lp ℝ 2 (standardGaussian I)) : ℝ :=
  ‖f‖ ^ 2 - (1 / 2 : ℝ) * ∑ c, ‖subspaceConditionalL2 (O c) (hO c) (observed c) f‖ ^ 2

def gaussianResidualEnergy (O : C → Matrix I I ℝ) (hO : ∀ c, O c * (O c).transpose = 1)
    (observed : C → Finset I) (a : K → I → ℕ) (coeff : K → ℝ)
    (A B : C → P → I → ℝ) (tA tB : C → P → ℝ) : ℝ :=
  ∑ c, ∑ p, (tA c p * ‖directionalLp a coeff (A c p) -
      subspaceConditionalL2 (O c) (hO c) (observed c) (directionalLp a coeff (A c p))‖ ^ 2 +
    tB c p * ‖directionalLp a coeff (B c p) -
      subspaceConditionalL2 (O c) (hO c) (observed c) (directionalLp a coeff (B c p))‖ ^ 2)

/-- The actual fourth-chaos/source entropy quadratic form has the exact
squared-residual identity in every homogeneous degree. Its hypotheses are
finite geometric identities and actual polynomial reversal admissibility;
no positivity or derivative-commutation conclusion is assumed. -/
theorem gaussianChannelDefect_squares
    (O : C → Matrix I I ℝ) (hO : ∀ c, O c * (O c).transpose = 1) (observed : C → Finset I)
    (a : K → I → ℕ) (ha : Function.Injective a) (coeff : K → ℝ)
    (b : C → J → I → ℕ) (hb : ∀ c, Function.Injective (b c)) (other : C → J → ℝ)
    (degree : ℕ) (hdegree : ∀ k, ∑ i, a k i = degree)
    (hbdegree : ∀ c j, ∑ i, b c j i = degree)
    (hproj : ∀ c, chaosLp (b c) (other c) = subspaceConditionalL2 (O c) (hO c) (observed c) (chaosLp a coeff))
    (A B : C → P → I → ℝ) (tA tB : C → P → ℝ)
    (hretainA : ∀ c p, A c p ∈ observationSubspace (O c) (observed c))
    (hretainB : ∀ c p, B c p ∈ observationSubspace (O c) (observed c))
    (hweights : ∀ c p, tA c p + tB c p = 1)
    (hframe : ∀ u : I → ℝ, (∑ c, ∑ p, (tA c p * (∑ i, A c p i * u i) ^ 2 +
      tB c p * (∑ i, B c p i * u i) ^ 2)) = ∑ i, u i ^ 2)
    (hobsframe : ∀ c u, u ∈ observationSubspace (O c) (observed c) →
      (∑ p, ((∑ i, A c p i * u i) ^ 2 + (∑ i, B c p i * u i) ^ 2)) = ∑ i, u i ^ 2)
    (R : C → Matrix I I ℝ) (hR : ∀ c, R c * (R c).transpose = 1)
    (hswap : ∀ c p, (R c).mulVec (A c p) = B c p)
    (hsym : ∀ c x, chaosFunction (b c) (other c) ((R c).mulVec x) = chaosFunction (b c) (other c) x) :
    (degree : ℝ) * gaussianChannelDefect O hO observed (chaosLp a coeff) =
      gaussianResidualEnergy O hO observed a coeff A B tA tB := by
  have hfull := paired_directionalLp_degree_energy a ha coeff degree hdegree
    (fun cp : C × P => A cp.1 cp.2) (fun cp : C × P => B cp.1 cp.2)
    (fun cp : C × P => tA cp.1 cp.2) (fun cp : C × P => tB cp.1 cp.2)
    (fun u => by simpa only [Fintype.sum_prod_type] using hframe u)
  simp only [Fintype.sum_prod_type] at hfull
  have hhalf (c : C) : (∑ p, (tA c p * ‖directionalLp (b c) (other c) (A c p)‖ ^ 2 +
      tB c p * ‖directionalLp (b c) (other c) (B c p)‖ ^ 2)) =
      (1 / 2 : ℝ) * (degree : ℝ) * ‖subspaceConditionalL2 (O c) (hO c) (observed c) (chaosLp a coeff)‖ ^ 2 := by
    have he := paired_projected_directionalLp_degree_energy (O c) (hO c) (observed c)
      a coeff (b c) (other c) (hb c) degree (fun k => (hdegree k).le)
      (hbdegree c) (hproj c) (A c) (B c) (hobsframe c)
    have hp (p : P) : tA c p * ‖directionalLp (b c) (other c) (A c p)‖ ^ 2 +
        tB c p * ‖directionalLp (b c) (other c) (B c p)‖ ^ 2 =
        (1 / 2 : ℝ) * (‖directionalLp (b c) (other c) (A c p)‖ ^ 2 +
          ‖directionalLp (b c) (other c) (B c p)‖ ^ 2) := by
      have hn := directionalLp_norm_eq_of_symmetry (b c) (other c) (R c) (hR c)
        (A c p) (B c p) (hswap c p) (hsym c)
      rw [hn]
      nlinarith [hweights c p]
    simp_rw [hp]
    rw [← Finset.mul_sum, he, hproj c]
    ring
  have hcommA (c : C) (p : P) := subspaceConditionalL2_directional (O c) (hO c) (observed c)
    a coeff (b c) (other c) degree (fun k => (hdegree k).le)
    (fun j => (hbdegree c j).le) (hproj c) (A c p) (hretainA c p)
  have hcommB (c : C) (p : P) := subspaceConditionalL2_directional (O c) (hO c) (observed c)
    a coeff (b c) (other c) degree (fun k => (hdegree k).le)
    (fun j => (hbdegree c j).le) (hproj c) (B c p) (hretainB c p)
  have hres : gaussianResidualEnergy O hO observed a coeff A B tA tB =
      (∑ c, ∑ p, (tA c p * ‖directionalLp a coeff (A c p)‖ ^ 2 +
        tB c p * ‖directionalLp a coeff (B c p)‖ ^ 2)) -
      ∑ c, ∑ p, (tA c p * ‖directionalLp (b c) (other c) (A c p)‖ ^ 2 +
        tB c p * ‖directionalLp (b c) (other c) (B c p)‖ ^ 2) := by
    unfold gaussianResidualEnergy
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro c hc
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    rw [subspaceConditionalL2_pythagoras, subspaceConditionalL2_pythagoras,
      hcommA c p, hcommB c p]
    ring
  rw [hres, hfull]
  simp_rw [hhalf]
  unfold gaussianChannelDefect
  rw [← Finset.mul_sum]
  ring


/-- Nonnegative frame weights make the proved residual energy nonnegative. -/
theorem gaussianResidualEnergy_nonneg
    (O : C → Matrix I I ℝ) (hO : ∀ c, O c * (O c).transpose = 1) (observed : C → Finset I)
    (a : K → I → ℕ) (coeff : K → ℝ) (A B : C → P → I → ℝ) (tA tB : C → P → ℝ)
    (hA : ∀ c p, 0 ≤ tA c p) (hB : ∀ c p, 0 ≤ tB c p) :
    0 ≤ gaussianResidualEnergy O hO observed a coeff A B tA tB := by
  apply Finset.sum_nonneg
  intro c hc
  apply Finset.sum_nonneg
  intro p hp
  exact add_nonneg (mul_nonneg (hA c p) (sq_nonneg _)) (mul_nonneg (hB c p) (sq_nonneg _))

/-- Strictly positive weights force every actual derivative residual to vanish
when the residual energy is zero. -/
theorem gaussianResidualEnergy_eq_zero_residuals
    (O : C → Matrix I I ℝ) (hO : ∀ c, O c * (O c).transpose = 1) (observed : C → Finset I)
    (a : K → I → ℕ) (coeff : K → ℝ) (A B : C → P → I → ℝ) (tA tB : C → P → ℝ)
    (hA : ∀ c p, 0 < tA c p) (hB : ∀ c p, 0 < tB c p)
    (hz : gaussianResidualEnergy O hO observed a coeff A B tA tB = 0) (c : C) (p : P) :
    (directionalLp a coeff (A c p) = subspaceConditionalL2 (O c) (hO c) (observed c)
      (directionalLp a coeff (A c p))) ∧
    (directionalLp a coeff (B c p) = subspaceConditionalL2 (O c) (hO c) (observed c)
      (directionalLp a coeff (B c p))) := by
  let u := fun c p => tA c p * ‖directionalLp a coeff (A c p) -
      subspaceConditionalL2 (O c) (hO c) (observed c) (directionalLp a coeff (A c p))‖ ^ 2
  let v := fun c p => tB c p * ‖directionalLp a coeff (B c p) -
      subspaceConditionalL2 (O c) (hO c) (observed c) (directionalLp a coeff (B c p))‖ ^ 2
  have hu : ∀ c p, 0 ≤ u c p := fun c p => mul_nonneg (hA c p).le (sq_nonneg _)
  have hv : ∀ c p, 0 ≤ v c p := fun c p => mul_nonneg (hB c p).le (sq_nonneg _)
  have ht : u c p + v c p ≤ 0 := by
    have h1 := Finset.single_le_sum (s := Finset.univ) (f := fun q => u c q + v c q)
      (fun q _ => add_nonneg (hu c q) (hv c q)) (Finset.mem_univ p)
    have h2 := Finset.single_le_sum (s := Finset.univ) (f := fun r => ∑ q, (u r q + v r q))
      (fun r _ => Finset.sum_nonneg (fun q _ => add_nonneg (hu r q) (hv r q))) (Finset.mem_univ c)
    change (∑ r, ∑ q, (u r q + v r q)) = 0 at hz
    exact h1.trans (h2.trans_eq hz)
  have hzu : u c p = 0 := by linarith [hu c p, hv c p]
  have hzv : v c p = 0 := by linarith [hu c p, hv c p]
  constructor
  · apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    have hsq := (mul_eq_zero.mp hzu).resolve_left (ne_of_gt (hA c p))
    exact pow_eq_zero hsq
  · apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    have hsq := (mul_eq_zero.mp hzv).resolve_left (ne_of_gt (hB c p))
    exact pow_eq_zero hsq

end GeneralizedBulk.Entropy.Hermite
