import Mathlib

/-!
# Finite probability estimates for quadratic edge marks

This module proves the algebraic quantitative interface used in Section 4
of the accompanying research note. The probability space is finite, with
explicit nonnegative weights of total mass one. No random-graph moment
estimate is assumed as an axiom: each theorem lists its covariance estimate
as a hypothesis.
-/

noncomputable section
open scoped BigOperators

namespace GaussianWave.EdgeQuadratics

/-- A finite probability distribution, with real probability weights. -/
structure FiniteProbability (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  total : ∑ ω, weight ω = 1

namespace FiniteProbability

variable {Ω : Type*} [Fintype Ω] (P : FiniteProbability Ω)

/-- Uniform sampling, in particular a uniform oriented-edge sample. -/
def uniform [Nonempty Ω] : FiniteProbability Ω where
  weight _ := (Fintype.card Ω : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by simp [Fintype.card_ne_zero]

/-- Expectation on the finite probability space. -/
def expect (f : Ω → ℝ) : ℝ := ∑ ω, P.weight ω * f ω

/-- The actual empirical probability law of a finite sampled mark. -/
def law {E : Type*} [MeasurableSpace E] (mark : Ω → E) : MeasureTheory.Measure E :=
  ∑ ω, ENNReal.ofReal (P.weight ω) • MeasureTheory.Measure.dirac (mark ω)

instance law_isProbability {E : Type*} [MeasurableSpace E] (mark : Ω → E) :
    MeasureTheory.IsProbabilityMeasure (P.law mark) := by
  constructor
  simp only [law, MeasureTheory.Measure.coe_finset_sum, Finset.sum_apply,
    MeasureTheory.Measure.smul_apply,
    MeasureTheory.Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun ω _ => P.nonneg ω), P.total]
  simp

theorem integrable_law {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    (mark : Ω → E) (f : E → ℝ) : MeasureTheory.Integrable f (P.law mark) := by
  apply MeasureTheory.integrable_finset_sum_measure.mpr
  intro ω _
  exact MeasureTheory.integrable_dirac.smul_measure ENNReal.ofReal_ne_top

/-- Bochner integration against the genuine finite law is exactly the finite
expectation. This links the estimates below to empirical sampling measures. -/
theorem integral_law {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    (mark : Ω → E) (f : E → ℝ) :
    (∫ x, f x ∂P.law mark) = P.expect (fun ω => f (mark ω)) := by
  rw [law, MeasureTheory.integral_finset_sum_measure]
  · unfold expect
    apply Finset.sum_congr rfl
    intro ω _
    rw [MeasureTheory.integral_smul_measure, MeasureTheory.integral_dirac]
    simp [ENNReal.toReal_ofReal, P.nonneg ω]
  · intro ω _
    exact MeasureTheory.integrable_dirac.smul_measure ENNReal.ofReal_ne_top

@[simp] theorem expect_const (c : ℝ) : P.expect (fun _ => c) = c := by
  simp [expect, ← Finset.sum_mul, P.total]

theorem expect_add (f g : Ω → ℝ) :
    P.expect (fun ω => f ω + g ω) = P.expect f + P.expect g := by
  simp [expect, mul_add, Finset.sum_add_distrib]

theorem expect_sub (f g : Ω → ℝ) :
    P.expect (fun ω => f ω - g ω) = P.expect f - P.expect g := by
  simp [expect, mul_sub, Finset.sum_sub_distrib]

theorem expect_mul_const (c : ℝ) (f : Ω → ℝ) :
    P.expect (fun ω => c * f ω) = c * P.expect f := by
  simp [expect, Finset.mul_sum, mul_left_comm]

theorem expect_sum {ι : Type*} [Fintype ι] (f : ι → Ω → ℝ) :
    P.expect (fun ω => ∑ i, f i ω) = ∑ i, P.expect (f i) := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm

theorem expect_nonneg {f : Ω → ℝ} (h : ∀ ω, 0 ≤ f ω) : 0 ≤ P.expect f := by
  exact Finset.sum_nonneg fun ω _ => mul_nonneg (P.nonneg ω) (h ω)

theorem expect_mono {f g : Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) :
    P.expect f ≤ P.expect g := by
  exact Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (P.nonneg ω)

/-- The centered diagonal quadratic estimate implies a scalar fourth bound. -/
theorem fourth_moment_le_of_centered_square
    (X : Ω → ℝ) (C a : ℝ)
    (hsecond : P.expect (fun ω => X ω ^ 2) = 1)
    (hquadratic : |P.expect (fun ω => (X ω ^ 2 - 1) ^ 2)| ≤ C + a) :
    P.expect (fun ω => X ω ^ 4) ≤ 1 + C + a := by
  have hid : P.expect (fun ω => (X ω ^ 2 - 1) ^ 2) =
      P.expect (fun ω => X ω ^ 4) - 1 := by
    calc
      P.expect (fun ω => (X ω ^ 2 - 1) ^ 2) =
          P.expect (fun ω => X ω ^ 4 - 2 * X ω ^ 2 + 1) := by
            congr 1
            funext ω
            ring
      _ = P.expect (fun ω => X ω ^ 4) - 1 := by
        rw [P.expect_add, P.expect_sub, P.expect_mul_const]
        simp [hsecond]
        ring
  have hb := le_trans (le_abs_self (P.expect (fun ω => (X ω ^ 2 - 1) ^ 2))) hquadratic
  rw [hid] at hb
  linarith

/-- The same fourth-moment conclusion stated for an actual empirical law. -/
theorem integral_fourth_law_le_of_centered_square
    (X : Ω → ℝ) (C a : ℝ)
    (hsecond : P.expect (fun ω => X ω ^ 2) = 1)
    (hquadratic : |P.expect (fun ω => (X ω ^ 2 - 1) ^ 2)| ≤ C + a) :
    (∫ x, x ^ 4 ∂P.law X) ≤ 1 + C + a := by
  rw [P.integral_law]
  exact P.fourth_moment_le_of_centered_square X C a hsecond hquadratic

/-- Expanding a finite weighted sum's square gives its covariance sum. -/
theorem expect_sum_sq {ι : Type*} [Fintype ι]
    (h : ι → ℝ) (X : ι → Ω → ℝ) :
    P.expect (fun ω => (∑ i, h i * X i ω) ^ 2) =
      ∑ i, ∑ j, h i * h j * P.expect (fun ω => X i ω * X j ω) := by
  calc
    P.expect (fun ω => (∑ i, h i * X i ω) ^ 2) =
        P.expect (fun ω => ∑ i, ∑ j, (h i * h j) * (X i ω * X j ω)) := by
          congr 1
          funext ω
          simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = ∑ i, ∑ j, h i * h j * P.expect (fun ω => X i ω * X j ω) := by
      rw [P.expect_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [P.expect_sum]
      apply Finset.sum_congr rfl
      intro j _
      exact P.expect_mul_const _ _

/-- A diagonal-plus-uniform-error covariance bound controls weighted sums.

Centering of the variables is not needed for this algebraic implication;
in the edge-mark application `X i` is already a centered quadratic mark.
-/
theorem weighted_square_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → ℝ) (X : ι → Ω → ℝ) (C a : ℝ)
    (hcov : ∀ i j, |P.expect (fun ω => X i ω * X j ω)| ≤
      (if i = j then C else 0) + a) :
    P.expect (fun ω => (∑ i, h i * X i ω) ^ 2) ≤
      C * (∑ i, (h i) ^ 2) + a * (∑ i, |h i|) ^ 2 := by
  rw [P.expect_sum_sq]
  calc
    ∑ i, ∑ j, h i * h j * P.expect (fun ω => X i ω * X j ω) ≤
        ∑ i, ∑ j, |h i| * |h j| * ((if i = j then C else 0) + a) := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          calc
            h i * h j * P.expect (fun ω => X i ω * X j ω) ≤
                |h i * h j * P.expect (fun ω => X i ω * X j ω)| := le_abs_self _
            _ = |h i| * |h j| * |P.expect (fun ω => X i ω * X j ω)| := by
              rw [abs_mul, abs_mul]
            _ ≤ |h i| * |h j| * ((if i = j then C else 0) + a) :=
              mul_le_mul_of_nonneg_left (hcov i j) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = C * (∑ i, (h i) ^ 2) + a * (∑ i, |h i|) ^ 2 := by
      simp only [mul_add, Finset.sum_add_distrib]
      have hdiag : (∑ i, ∑ j, |h i| * |h j| * (if i = j then C else 0)) =
          C * (∑ i, (h i) ^ 2) := by
        simp only [mul_ite, mul_zero]
        simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [← sq_abs]
        ring
      rw [hdiag]
      congr 1
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- Complex weights are allowed. The factor two in the uniform-error term
comes from separately bounding real and imaginary coefficient sums. -/
theorem weighted_complex_square_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → ℂ) (X : ι → Ω → ℝ) (C a : ℝ) (ha : 0 ≤ a)
    (hcov : ∀ i j, |P.expect (fun ω => X i ω * X j ω)| ≤
      (if i = j then C else 0) + a) :
    P.expect (fun ω => ‖∑ i, h i * (X i ω : ℂ)‖ ^ 2) ≤
      C * (∑ i, ‖h i‖ ^ 2) + 2 * a * (∑ i, ‖h i‖) ^ 2 := by
  have hr := P.weighted_square_le (fun i => (h i).re) X C a hcov
  have hi := P.weighted_square_le (fun i => (h i).im) X C a hcov
  have hexpand : P.expect (fun ω => ‖∑ i, h i * (X i ω : ℂ)‖ ^ 2) =
      P.expect (fun ω => (∑ i, (h i).re * X i ω) ^ 2) +
      P.expect (fun ω => (∑ i, (h i).im * X i ω) ^ 2) := by
    rw [← P.expect_add]
    congr 1
    funext ω
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.mul_re, Complex.mul_im, pow_two]
  have hcoeff : (∑ i, (h i).re ^ 2) + (∑ i, (h i).im ^ 2) =
      ∑ i, ‖h i‖ ^ 2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hre : (∑ i, |(h i).re|) ≤ ∑ i, ‖h i‖ :=
    Finset.sum_le_sum fun i _ => Complex.abs_re_le_norm (h i)
  have him : (∑ i, |(h i).im|) ≤ ∑ i, ‖h i‖ :=
    Finset.sum_le_sum fun i _ => Complex.abs_im_le_norm (h i)
  have hre0 : 0 ≤ ∑ i, |(h i).re| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have him0 : 0 ≤ ∑ i, |(h i).im| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hn0 : 0 ≤ ∑ i, ‖h i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hre2 : (∑ i, |(h i).re|) ^ 2 ≤ (∑ i, ‖h i‖) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hre) (add_nonneg hn0 hre0)]
  have him2 : (∑ i, |(h i).im|) ^ 2 ≤ (∑ i, ‖h i‖) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr him) (add_nonneg hn0 him0)]
  rw [hexpand]
  have hmre := mul_le_mul_of_nonneg_left hre2 ha
  have hmim := mul_le_mul_of_nonneg_left him2 ha
  have hc : C * (∑ i, (h i).re ^ 2) + C * (∑ i, (h i).im ^ 2) =
      C * (∑ i, ‖h i‖ ^ 2) := by rw [← mul_add, hcoeff]
  linarith

/-- Summing coordinate estimates gives a finite-dimensional squared
Frobenius bound. Taking `κ = Fin 4 × Fin 4` gives sixteen coordinates. -/
theorem weighted_frobenius_square_le {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (h : ι → ℂ) (X : ι → κ → Ω → ℝ) (C a : ℝ) (ha : 0 ≤ a)
    (hcov : ∀ r i j, |P.expect (fun ω => X i r ω * X j r ω)| ≤
      (if i = j then C else 0) + a) :
    P.expect (fun ω => ∑ r, ‖∑ i, h i * (X i r ω : ℂ)‖ ^ 2) ≤
      (Fintype.card κ : ℝ) *
        (C * (∑ i, ‖h i‖ ^ 2) + 2 * a * (∑ i, ‖h i‖) ^ 2) := by
  rw [P.expect_sum]
  calc
    ∑ r, P.expect (fun ω => ‖∑ i, h i * (X i r ω : ℂ)‖ ^ 2) ≤
        ∑ _r : κ, (C * (∑ i, ‖h i‖ ^ 2) + 2 * a * (∑ i, ‖h i‖) ^ 2) := by
          apply Finset.sum_le_sum
          intro r _
          exact P.weighted_complex_square_le h (fun i => X i r) C a ha (hcov r)
    _ = _ := by simp; ring

/-- Two independently sampled edges are represented by the product law. -/
def prod (Q : FiniteProbability Ω) : FiniteProbability (Ω × Ω) where
  weight ω := P.weight ω.1 * Q.weight ω.2
  nonneg ω := mul_nonneg (P.nonneg ω.1) (Q.nonneg ω.2)
  total := by
    simp [Fintype.sum_prod_type, ← Finset.mul_sum, ← Finset.sum_mul, P.total, Q.total]

theorem expect_prod (Q : FiniteProbability Ω) (f g : Ω → ℝ) :
    (P.prod Q).expect (fun ω => f ω.1 * g ω.2) = P.expect f * Q.expect g := by
  simp only [expect, prod, Fintype.sum_prod_type]
  calc
    (∑ x, ∑ y, (P.weight x * Q.weight y) * (f x * g y)) =
        ∑ x, ∑ y, (P.weight x * f x) * (Q.weight y * g y) := by
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro y _
          ring
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]

@[simp] theorem expect_prod_left (Q : FiniteProbability Ω) (f : Ω → ℝ) :
    (P.prod Q).expect (fun ω => f ω.1) = P.expect f := by
  simpa using P.expect_prod Q f (fun _ => 1)

@[simp] theorem expect_prod_right (Q : FiniteProbability Ω) (f : Ω → ℝ) :
    (P.prod Q).expect (fun ω => f ω.2) = Q.expect f := by
  simpa using P.expect_prod Q (fun _ => 1) f

end FiniteProbability

/-- A coordinate of a centered four-endpoint outer product. `false` and
`true` select the first and second independent edge, respectively. -/
def twoEdgeQuadratic {Ω ι ρ : Type*}
    (ξ : ι → ρ → Ω → ℝ) (B : ι → ρ → ρ → ℝ)
    (i : ι) (p q : Bool × ρ) (ω : Ω × Ω) : ℝ :=
  match p.1, q.1 with
  | false, false => ξ i p.2 ω.1 * ξ i q.2 ω.1 - B i p.2 q.2
  | true, true => ξ i p.2 ω.2 * ξ i q.2 ω.2 - B i p.2 q.2
  | false, true => ξ i p.2 ω.1 * ξ i q.2 ω.2
  | true, false => ξ i q.2 ω.1 * ξ i p.2 ω.2

/-- Exact zero means and edge second moments center the full two-edge
quadratic mark, including entries joining the two independent edges. -/
theorem twoEdgeQuadratic_centered {Ω ι ρ : Type*} [Fintype Ω]
    (P : FiniteProbability Ω) (ξ : ι → ρ → Ω → ℝ)
    (B : ι → ρ → ρ → ℝ)
    (hmean : ∀ i r, P.expect (ξ i r) = 0)
    (hsecond : ∀ i r s, P.expect (fun ω => ξ i r ω * ξ i s ω) = B i r s)
    (i : ι) (p q : Bool × ρ) :
    (P.prod P).expect (twoEdgeQuadratic ξ B i p q) = 0 := by
  rcases p with ⟨b, r⟩
  rcases q with ⟨c, s⟩
  cases b <;> cases c
  · change (P.prod P).expect (fun ω => ξ i r ω.1 * ξ i s ω.1 - B i r s) = 0
    rw [P.expect_prod_left P (fun ω => ξ i r ω * ξ i s ω - B i r s)]
    rw [P.expect_sub, hsecond, P.expect_const, sub_self]
  · change (P.prod P).expect (fun ω => ξ i r ω.1 * ξ i s ω.2) = 0
    rw [P.expect_prod P (ξ i r) (ξ i s), hmean, zero_mul]
  · change (P.prod P).expect (fun ω => ξ i s ω.1 * ξ i r ω.2) = 0
    rw [P.expect_prod P (ξ i s) (ξ i r), hmean, zero_mul]
  · change (P.prod P).expect (fun ω => ξ i r ω.2 * ξ i s ω.2 - B i r s) = 0
    rw [P.expect_prod_right P (fun ω => ξ i r ω * ξ i s ω - B i r s)]
    rw [P.expect_sub, hsecond, P.expect_const, sub_self]

/-- The one-edge covariance estimate lifts to each coordinate of the
two-independent-edge outer product. No Gaussianity is used. -/
theorem twoEdgeQuadratic_covariance {Ω ι ρ : Type*}
    [Fintype Ω] [DecidableEq ι]
    (P : FiniteProbability Ω) (ξ : ι → ρ → Ω → ℝ)
    (B : ι → ρ → ρ → ℝ) (C a : ℝ) (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hsecond : ∀ i j r, P.expect (fun ω => ξ i r ω * ξ j r ω) =
      if i = j then 1 else 0)
    (hquad : ∀ i j r s,
      |P.expect (fun ω => (ξ i r ω * ξ i s ω - B i r s) *
        (ξ j r ω * ξ j s ω - B j r s))| ≤ (if i = j then C else 0) + a)
    (i j : ι) (p q : Bool × ρ) :
    |(P.prod P).expect (fun ω =>
      twoEdgeQuadratic ξ B i p q ω * twoEdgeQuadratic ξ B j p q ω)| ≤
      (if i = j then C + 1 else 0) + a := by
  rcases p with ⟨b, r⟩
  rcases q with ⟨c, s⟩
  have hcross (r s : ρ) :
      |(P.prod P).expect (fun ω => (ξ i r ω.1 * ξ i s ω.2) *
        (ξ j r ω.1 * ξ j s ω.2))| ≤ (if i = j then C + 1 else 0) + a := by
    have heq : (P.prod P).expect (fun ω => (ξ i r ω.1 * ξ i s ω.2) *
        (ξ j r ω.1 * ξ j s ω.2)) =
        P.expect (fun ω => ξ i r ω * ξ j r ω) *
          P.expect (fun ω => ξ i s ω * ξ j s ω) := by
      calc
        _ = (P.prod P).expect (fun ω =>
            (ξ i r ω.1 * ξ j r ω.1) * (ξ i s ω.2 * ξ j s ω.2)) := by
              congr 1
              funext ω
              ring
        _ = _ := P.expect_prod P (fun ω => ξ i r ω * ξ j r ω)
          (fun ω => ξ i s ω * ξ j s ω)
    rw [heq, hsecond, hsecond]
    split_ifs <;> simp only [one_mul, mul_zero, abs_one, abs_zero] <;> linarith
  cases b <;> cases c
  · simp only [twoEdgeQuadratic]
    rw [P.expect_prod_left P (fun ω =>
      (ξ i r ω * ξ i s ω - B i r s) * (ξ j r ω * ξ j s ω - B j r s))]
    have h := hquad i j r s
    split_ifs at * <;> linarith
  · exact hcross r s
  · exact hcross s r
  · simp only [twoEdgeQuadratic]
    rw [P.expect_prod_right P (fun ω =>
      (ξ i r ω * ξ i s ω - B i r s) * (ξ j r ω * ξ j s ω - B j r s))]
    have h := hquad i j r s
    split_ifs at * <;> linarith

/-- The reduced one-edge hypothesis yields the actual weighted two-edge
Frobenius estimate. With `ρ = Fin 2`, the coordinate count is sixteen. -/
theorem twoEdge_weighted_frobenius_bound {Ω ι ρ : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι] [Fintype ρ]
    (P : FiniteProbability Ω) (ξ : ι → ρ → Ω → ℝ)
    (B : ι → ρ → ρ → ℝ) (C a : ℝ) (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hsecond : ∀ i j r, P.expect (fun ω => ξ i r ω * ξ j r ω) =
      if i = j then 1 else 0)
    (hquad : ∀ i j r s,
      |P.expect (fun ω => (ξ i r ω * ξ i s ω - B i r s) *
        (ξ j r ω * ξ j s ω - B j r s))| ≤ (if i = j then C else 0) + a)
    (h : ι → ℂ) :
    (P.prod P).expect (fun ω => ∑ pq : (Bool × ρ) × (Bool × ρ),
      ‖∑ i, h i * (twoEdgeQuadratic ξ B i pq.1 pq.2 ω : ℂ)‖ ^ 2) ≤
      (Fintype.card ((Bool × ρ) × (Bool × ρ)) : ℝ) *
        ((C + 1) * (∑ i, ‖h i‖ ^ 2) + 2 * a * (∑ i, ‖h i‖) ^ 2) := by
  exact (P.prod P).weighted_frobenius_square_le
    (κ := (Bool × ρ) × (Bool × ρ)) h
    (fun (i : ι) (pq : (Bool × ρ) × (Bool × ρ)) =>
      twoEdgeQuadratic ξ B i pq.1 pq.2) (C + 1) a ha
    (fun pq i j => twoEdgeQuadratic_covariance P ξ B C a hC ha hsecond hquad i j pq.1 pq.2)

end GaussianWave.EdgeQuadratics
