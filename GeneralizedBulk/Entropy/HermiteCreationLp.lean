import GeneralizedBulk.Entropy.ChaosDecomposition
import GeneralizedBulk.Entropy.HermiteJetEnergy

/-! Exact Hilbert adjoint algebra for Gaussian Hermite lowering and creation. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GeneralizedBulk.Entropy.Hermite
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K]

@[simp] theorem lower_upper (a : I → ℕ) (i : I) : lower (upper a i) i = a := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [lower, upper]
  · simp [lower, upper, hji]

theorem upper_lower_of_pos (a : I → ℕ) (i : I) (hi : 0 < a i) : upper (lower a i) i = a := by
  funext j
  by_cases hji : j = i
  · subst j
    simp only [upper, lower, Function.update_self]
    omega
  · simp [upper, lower, hji]

theorem multiFactorial_upper (a : I → ℕ) (i : I) :
    multiFactorial I (upper a i) = (a i + 1 : ℝ) * multiFactorial I a := by
  have hp : 0 < upper a i i := by simp [upper]
  have hh := multiFactorial_lower (upper a i) i hp
  rw [lower_upper] at hh
  simpa only [upper, Function.update_self, Nat.cast_add, Nat.cast_one] using hh

/-- Actual Gaussian lowering is adjoint to actual raising on the polynomial
Hilbert vectors, with factorial normalization proved rather than assumed. -/
theorem derivativeLp_inner_multiLp (a b : I → ℕ) (i : I) :
    @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ (derivativeLp a i) (multiLp I b) =
      @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ (multiLp I a) (multiLp I (upper b i)) := by
  simp only [derivativeLp, inner_smul_left, starRingEnd_apply, star_trivial, multiLp_inner]
  by_cases hab : a = upper b i
  · subst a
    rw [lower_upper, multiFactorial_upper]
    simp only [↓reduceIte, upper, Function.update_self, Nat.cast_add, Nat.cast_one]
  · simp only [hab, ↓reduceIte]
    by_cases ha : a i = 0
    · simp [ha]
    · have hl : lower a i ≠ b := by
        intro h
        have hh := congrArg (fun c => upper c i) h
        change upper (lower a i) i = upper b i at hh
        rw [upper_lower_of_pos a i (Nat.pos_of_ne_zero ha)] at hh
        exact hab hh
      simp only [hl, ↓reduceIte, mul_zero]

theorem chaosDerivativeLp_inner_multiLp (a : K → I → ℕ) (coeff : K → ℝ) (b : I → ℕ) (i : I) :
    @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ (chaosDerivativeLp a coeff i) (multiLp I b) =
      @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ (chaosLp a coeff) (multiLp I (upper b i)) := by
  simp only [chaosDerivativeLp, chaosLp, sum_inner, inner_smul_left, starRingEnd_apply, star_trivial,
    derivativeLp_inner_multiLp]

/-- Equality against the full finite Hermite basis is actual L² equality in
the true homogeneous subspace. -/
theorem fullChaos_eq_of_basis_inner_eq (n : ℕ) (f g : fullChaosSpace I n)
    (h : ∀ a : DegreeIndex I n,
      @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ f (multiLp I (degreeIndexNat I a)) =
        @inner ℝ (Lp ℝ 2 (standardGaussian I)) _ g (multiLp I (degreeIndexNat I a))) : f = g := by
  have hf := fullChaosCoordinates_spec I n f
  have hg := fullChaosCoordinates_spec I n g
  have hc : fullChaosCoordinates I n f = fullChaosCoordinates I n g := by
    funext a
    have hh := h a
    rw [← hf, ← hg, fullChaosMap_inner_basis, fullChaosMap_inner_basis] at hh
    exact mul_right_cancel₀ (ne_of_gt (multiFactorial_pos I _)) hh
  apply Subtype.ext
  rw [← hf, ← hg, hc]

/-- The actual derivative of a homogeneous polynomial is in the immediately
lower homogeneous chaos. Zero lowering coefficients are genuinely removed. -/
theorem chaosDerivativeLp_mem_fullChaos_succ (a : K → I → ℕ) (coeff : K → ℝ)
    (n : ℕ) (ha : ∀ k, ∑ j, a k j = n + 1) (i : I) :
    chaosDerivativeLp a coeff i ∈ fullChaosSpace I n := by
  rw [chaosDerivativeLp_eq_positiveLower]
  apply chaosLp_mem_fullChaosSpace I n
  intro k
  simpa only [Nat.add_sub_cancel] using positiveLowerFamily_degree a (n + 1) ha i k

end GeneralizedBulk.Entropy.Hermite
