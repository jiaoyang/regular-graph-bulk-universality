import Mathlib
import GaussianWave.BS.GaussianRadialProfiles

/-! Strict-bulk radial asymptotics, proved by a conserved recurrence energy.
No trigonometric parametrization or Cesaro-limit premise is used. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace GaussianWave.BS

/-- Consecutive Chebyshev second-kind values `(U_n(x), U_{n-1}(x))`,
with the genuine `U_{-1}=0` initial condition. -/
def radialChebyshevPair (x : ℝ) : ℕ → ℝ × ℝ
  | 0 => (1, 0)
  | n+1 => (2*x*(radialChebyshevPair x n).1 - (radialChebyshevPair x n).2,
      (radialChebyshevPair x n).1)

def radialChebyshev (x : ℝ) (n : ℕ) : ℝ := (radialChebyshevPair x n).1
def radialChebyshevPrev (x : ℝ) (n : ℕ) : ℝ := (radialChebyshevPair x n).2

@[simp] theorem radialChebyshev_zero (x : ℝ) : radialChebyshev x 0 = 1 := rfl
@[simp] theorem radialChebyshevPrev_zero (x : ℝ) : radialChebyshevPrev x 0 = 0 := rfl
@[simp] theorem radialChebyshev_succ (x : ℝ) (n : ℕ) :
    radialChebyshev x (n+1) = 2*x*radialChebyshev x n-radialChebyshevPrev x n := rfl
@[simp] theorem radialChebyshevPrev_succ (x : ℝ) (n : ℕ) :
    radialChebyshevPrev x (n+1) = radialChebyshev x n := rfl

/-- Exact conserved energy, including the initial pair. -/
theorem radialChebyshev_energy (x : ℝ) (n : ℕ) :
    radialChebyshev x n ^ 2 + radialChebyshevPrev x n ^ 2 -
      2*x*radialChebyshev x n*radialChebyshevPrev x n = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [radialChebyshev_succ, radialChebyshevPrev_succ]
    nlinarith [ih]

theorem radialChebyshev_square_bound {x : ℝ} (hx : |x| < 1) (n : ℕ) :
    radialChebyshev x n ^ 2 + radialChebyshevPrev x n ^ 2 ≤ 1/(1-|x|) := by
  have hden : 0 < 1-|x| := by linarith
  have he := radialChebyshev_energy x n
  have hprod : 2*x*radialChebyshev x n*radialChebyshevPrev x n ≤
      |x| *(radialChebyshev x n ^ 2+radialChebyshevPrev x n ^ 2) := by
    have h1 := sq_nonneg (radialChebyshev x n-radialChebyshevPrev x n)
    have h2 := sq_nonneg (radialChebyshev x n+radialChebyshevPrev x n)
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h]
      nlinarith
    · rw [abs_of_nonpos h]
      nlinarith
  apply (le_div_iff₀ hden).2
  nlinarith

/-- The square sum differs from its linear growth by an explicitly bounded
boundary term. This identity drives all four exceptional eigenvalue limits. -/
theorem radialChebyshev_square_sum (x : ℝ) (N : ℕ) :
    2*(1-x^2)*(∑ n ∈ Finset.range N, radialChebyshev x n ^ 2) =
      (N : ℝ) + radialChebyshevPrev x N ^ 2 -
        x*radialChebyshev x N*radialChebyshevPrev x N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    simp only [Nat.cast_add, Nat.cast_one, radialChebyshev_succ, radialChebyshevPrev_succ]
    have he := radialChebyshev_energy x N
    nlinarith [ih]

/-- The adjacent-product sum has a telescoping boundary term. -/
theorem radialChebyshev_product_sum (x : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, radialChebyshev x n*radialChebyshevPrev x n) =
      x*(∑ n ∈ Finset.range N, radialChebyshev x n ^ 2) -
        radialChebyshev x N*radialChebyshevPrev x N/2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    simp only [radialChebyshev_succ, radialChebyshevPrev_succ]
    ring

/-- A shifted square sum has only one boundary square. -/
theorem radialChebyshev_prev_square_sum (x : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, radialChebyshevPrev x n ^ 2) =
      (∑ n ∈ Finset.range N, radialChebyshev x n ^ 2)-radialChebyshevPrev x N ^ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, radialChebyshevPrev_succ]
    ring


private theorem radialChebyshev_square_div_tendsto_zero {x : ℝ} (hx : |x| < 1) :
    Tendsto (fun N : ℕ => radialChebyshevPrev x N ^ 2 / (N : ℝ)) atTop (𝓝 0) := by
  refine tendsto_bdd_div_atTop_nhds_zero (B := 1/(1-|x|))
    (Eventually.of_forall (fun N => sq_nonneg _)) ?_ tendsto_natCast_atTop_atTop
  filter_upwards [] with N
  exact (le_add_of_nonneg_left (sq_nonneg _)).trans (radialChebyshev_square_bound hx N)

private theorem radialChebyshev_product_div_tendsto_zero {x : ℝ} (hx : |x| < 1) :
    Tendsto (fun N : ℕ => radialChebyshev x N * radialChebyshevPrev x N / (N : ℝ))
      atTop (𝓝 0) := by
  have hb (N : ℕ) : |radialChebyshev x N * radialChebyshevPrev x N| ≤ 1/(1-|x|) := by
    have h := radialChebyshev_square_bound hx N
    have hs := sq_nonneg (|radialChebyshev x N|-|radialChebyshevPrev x N|)
    simp only [sub_sq, sq_abs] at hs
    rw [abs_mul]
    have hden : 0 < 1-|x| := by linarith
    have hC : 0 ≤ 1/(1-|x|) := by positivity
    nlinarith
  exact tendsto_bdd_div_atTop_nhds_zero
    (Eventually.of_forall (fun N => (abs_le.mp (hb N)).1))
    (Eventually.of_forall (fun N => (abs_le.mp (hb N)).2)) tendsto_natCast_atTop_atTop

/-- The genuine Cesaro limit of squared second-kind Chebyshev values. -/
theorem radialChebyshev_square_cesaro {x : ℝ} (hx : |x| < 1) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, radialChebyshev x n ^ 2)/(N : ℝ))
      atTop (𝓝 (1/(2*(1-x^2)))) := by
  have hx2 : 0 < 1-x^2 := by have h := abs_lt.mp hx; nlinarith
  have hlim := (((tendsto_const_nhds (x := (1 : ℝ))).add (radialChebyshev_square_div_tendsto_zero hx)).sub
    ((radialChebyshev_product_div_tendsto_zero hx).const_mul x)).div_const (2*(1-x^2))
  simp only [add_zero, mul_zero, sub_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have he := radialChebyshev_square_sum x N
  field_simp
  nlinarith [he]

/-- The genuine Cesaro limit of adjacent Chebyshev products. -/
theorem radialChebyshev_product_cesaro {x : ℝ} (hx : |x| < 1) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N,
      radialChebyshev x n*radialChebyshevPrev x n)/(N : ℝ))
      atTop (𝓝 (x/(2*(1-x^2)))) := by
  have h := ((radialChebyshev_square_cesaro hx).const_mul x).sub
    ((radialChebyshev_product_div_tendsto_zero hx).div_const 2)
  simp only [zero_div, sub_zero, ← mul_div_assoc, mul_one] at h
  convert h using 1
  funext N
  rw [radialChebyshev_product_sum]
  ring

/-- Shifting one index does not alter the square Cesaro limit. -/
theorem radialChebyshev_prev_square_cesaro {x : ℝ} (hx : |x| < 1) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, radialChebyshevPrev x n ^ 2)/(N : ℝ))
      atTop (𝓝 (1/(2*(1-x^2)))) := by
  have h := (radialChebyshev_square_cesaro hx).sub (radialChebyshev_square_div_tendsto_zero hx)
  simp only [sub_zero] at h
  convert h using 1
  funext N
  rw [radialChebyshev_prev_square_sum, sub_div]

/-- Every real linear combination of consecutive radial values has its
explicit quadratic Cesaro limit. -/
theorem radialChebyshev_linear_square_cesaro {x : ℝ} (hx : |x| < 1) (a b : ℝ) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N,
      (a*radialChebyshev x n+b*radialChebyshevPrev x n)^2)/(N : ℝ))
      atTop (𝓝 ((a^2+b^2+2*x*a*b)/(2*(1-x^2)))) := by
  have h := (((radialChebyshev_square_cesaro hx).const_mul (a^2)).add
    ((radialChebyshev_prev_square_cesaro hx).const_mul (b^2))).add
    ((radialChebyshev_product_cesaro hx).const_mul (2*a*b))
  convert h using 1
  · funext N
    simp only [← add_div, ← mul_div_assoc]
    congr 1
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  · ring


/-- These recursively defined values are exactly mathlib's Chebyshev
polynomials, including the negative index needed at the first boundary. -/
theorem radialChebyshev_eq_polynomial (x : ℝ) (n : ℕ) :
    radialChebyshev x n = (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval x ∧
    radialChebyshevPrev x n = (Polynomial.Chebyshev.U ℝ ((n : ℤ)-1)).eval x := by
  induction n with
  | zero => simp
  | succ n ih =>
    constructor
    · rw [radialChebyshev_succ, ih.1, ih.2]
      have h := congrArg (fun p : Polynomial ℝ => p.eval x)
        (Polynomial.Chebyshev.U_add_one ℝ (n : ℤ))
      simpa using h.symm
    · rw [radialChebyshevPrev_succ, ih.1]
      congr 2
      simp

/-- Innovation variance in branching parameter `q=d-1`, energy `2√q*x`. -/
def radialInnovationVariance (q x : ℝ) : ℝ := ((q+1)^2-4*q*x^2)/((q+1)*q)

def radialExceptionalSlope (q x : ℝ) : ℝ := radialInnovationVariance q x/(2*(1-x^2))

/-- Vertex-ball exceptional radial eigenvalue, radius `k+1`. -/
def radialVertexExceptional (q x : ℝ) (k : ℕ) : ℝ :=
  1+∑ n ∈ Finset.range (k+1),
    (q*radialChebyshev x (n+1)-radialChebyshevPrev x n)^2/((q+1)*q)

/-- Multiplicity-`d-1` exceptional vertex-ball eigenvalue. -/
def radialBranchExceptional (q x : ℝ) (k : ℕ) : ℝ :=
  radialInnovationVariance q x * ∑ n ∈ Finset.range (k+1), radialChebyshev x n ^ 2

/-- The two exceptional edge-ball eigenvalues. -/
def radialEdgePlusExceptional (q x : ℝ) (k : ℕ) : ℝ :=
  (1+2*Real.sqrt q*x/(q+1)) * ∑ n ∈ Finset.range (k+1),
    (radialChebyshev x n-radialChebyshevPrev x n/Real.sqrt q)^2

def radialEdgeMinusExceptional (q x : ℝ) (k : ℕ) : ℝ :=
  (1-2*Real.sqrt q*x/(q+1)) * ∑ n ∈ Finset.range (k+1),
    (radialChebyshev x n+radialChebyshevPrev x n/Real.sqrt q)^2

@[simp] theorem radialVertexExceptional_zero (q x : ℝ) :
    radialVertexExceptional q x 0 = 1+4*q^2*x^2/((q+1)*q) := by
  simp [radialVertexExceptional]
  ring
@[simp] theorem radialBranchExceptional_zero (q x : ℝ) :
    radialBranchExceptional q x 0 = radialInnovationVariance q x := by
  simp [radialBranchExceptional]
@[simp] theorem radialEdgePlusExceptional_zero (q x : ℝ) :
    radialEdgePlusExceptional q x 0 = 1+2*Real.sqrt q*x/(q+1) := by
  simp [radialEdgePlusExceptional]
@[simp] theorem radialEdgeMinusExceptional_zero (q x : ℝ) :
    radialEdgeMinusExceptional q x 0 = 1-2*Real.sqrt q*x/(q+1) := by
  simp [radialEdgeMinusExceptional]

theorem radialExceptionalSlope_pos {q x : ℝ} (hq : 1 < q) (hx : |x| < 1) :
    0 < radialExceptionalSlope q x := by
  have hx2 : 0 < 1-x^2 := by have h := abs_lt.mp hx; nlinarith
  have hn : 0 < (q+1)^2-4*q*x^2 := by
    nlinarith [sq_nonneg (q-1), mul_pos (show 0<q by linarith) hx2]
  unfold radialExceptionalSlope radialInnovationVariance
  positivity

/-- All normalized exceptional eigenvalues have the same positive limit. -/
theorem radialBranchExceptional_cesaro {x : ℝ} (hx : |x| < 1) (q : ℝ) :
    Tendsto (fun k => radialBranchExceptional q x k / (k+1 : ℕ)) atTop
      (𝓝 (radialExceptionalSlope q x)) := by
  have h := ((radialChebyshev_square_cesaro hx).comp (tendsto_add_atTop_nat 1)).const_mul
    (radialInnovationVariance q x)
  convert h using 1
  · funext k
    simp only [radialBranchExceptional, Function.comp_apply]
    ring
  · unfold radialExceptionalSlope
    ring

theorem radialVertexExceptional_cesaro {x : ℝ} (hx : |x| < 1) {q : ℝ} (hq : 1 < q) :
    Tendsto (fun k => radialVertexExceptional q x k / (k+1 : ℕ)) atTop
      (𝓝 (radialExceptionalSlope q x)) := by
  have h := ((radialChebyshev_linear_square_cesaro hx (2*q*x) (-(q+1))).comp
    (tendsto_add_atTop_nat 1)).div_const ((q+1)*q)
  have h0 : Tendsto (fun k : ℕ => (1 : ℝ)/((k+1 : ℕ) : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using tendsto_one_div_add_atTop_nhds_zero_nat
  have hh := h0.add h
  convert hh using 1
  · funext k
    unfold radialVertexExceptional
    rw [add_div]
    congr 1
    simp only [Function.comp_apply]
    rw [← Finset.sum_div]
    have heq : (∑ n ∈ Finset.range (k+1),
        (q*radialChebyshev x (n+1)-radialChebyshevPrev x n)^2) =
        ∑ n ∈ Finset.range (k+1),
          (2*q*x*radialChebyshev x n+ -(q+1)*radialChebyshevPrev x n)^2 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [radialChebyshev_succ]
      ring
    rw [heq]
    ring
  · unfold radialExceptionalSlope radialInnovationVariance
    ring


private theorem radial_edge_slope_identity {q x e : ℝ} (hq : 1 < q) (he : e^2=1) :
    (1+e*2*Real.sqrt q*x/(q+1)) *
      (1+(-e/Real.sqrt q)^2+2*x*(-e/Real.sqrt q)) = radialInnovationVariance q x := by
  have hq0 : 0 < q := by linarith
  have hs0 : Real.sqrt q ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hq0)
  have hqp : q+1 ≠ 0 := by linarith
  have hs := Real.sq_sqrt (le_of_lt hq0)
  have hterm : (-e/Real.sqrt q)^2=1/q := by rw [div_pow, neg_sq, he, hs]
  rw [hterm]
  unfold radialInnovationVariance
  field_simp [hs0, hqp, ne_of_gt hq0]
  ring_nf
  simp only [hs, he]
  ring

private theorem radial_edge_cesaro {x : ℝ} (hx : |x| < 1) {q e : ℝ}
    (hq : 1 < q) (he : e^2=1) :
    Tendsto (fun k : ℕ =>
      ((1+e*2*Real.sqrt q*x/(q+1)) * ∑ n ∈ Finset.range (k+1),
        (radialChebyshev x n-e*radialChebyshevPrev x n/Real.sqrt q)^2) / (k+1 : ℕ))
      atTop (𝓝 (radialExceptionalSlope q x)) := by
  have h := ((radialChebyshev_linear_square_cesaro hx 1 (-e/Real.sqrt q)).comp
    (tendsto_add_atTop_nat 1)).const_mul (1+e*2*Real.sqrt q*x/(q+1))
  convert h using 1
  · funext k
    simp only [Function.comp_apply, ← mul_div_assoc]
    congr 2
    apply Finset.sum_congr rfl
    intro n hn
    ring
  · congr 1
    unfold radialExceptionalSlope
    rw [← mul_div_assoc]
    congr 1
    simpa only [one_pow, mul_one] using (radial_edge_slope_identity hq he).symm

theorem radialEdgePlusExceptional_cesaro {x : ℝ} (hx : |x| < 1) {q : ℝ} (hq : 1 < q) :
    Tendsto (fun k => radialEdgePlusExceptional q x k / (k+1 : ℕ)) atTop
      (𝓝 (radialExceptionalSlope q x)) := by
  simpa only [radialEdgePlusExceptional, one_mul] using
    (radial_edge_cesaro hx hq (show (1 : ℝ)^2=1 by norm_num))

theorem radialEdgeMinusExceptional_cesaro {x : ℝ} (hx : |x| < 1) {q : ℝ} (hq : 1 < q) :
    Tendsto (fun k => radialEdgeMinusExceptional q x k / (k+1 : ℕ)) atTop
      (𝓝 (radialExceptionalSlope q x)) := by
  simpa [radialEdgeMinusExceptional, sub_eq_add_neg, neg_div] using
    (radial_edge_cesaro hx hq (show (-1 : ℝ)^2=1 by norm_num))


/-- The exceptional determinant contribution vanishes: the common linear
factor cancels exactly with coefficients `1,q,−(q+1)/2,−(q+1)/2`. -/
theorem radial_exceptional_log_balance_tendsto_zero {q x : ℝ} (hq : 1 < q) (hx : |x| < 1) :
    Tendsto (fun k => Real.log (radialVertexExceptional q x k) +
      q*Real.log (radialBranchExceptional q x k) -
      (q+1)/2*Real.log (radialEdgePlusExceptional q x k) -
      (q+1)/2*Real.log (radialEdgeMinusExceptional q x k)) atTop (𝓝 0) := by
  have hA := radialExceptionalSlope_pos hq hx
  have h1 := radialVertexExceptional_cesaro hx hq
  have h2 := radialBranchExceptional_cesaro hx q
  have hp := radialEdgePlusExceptional_cesaro hx hq
  have hm := radialEdgeMinusExceptional_cesaro hx hq
  have hlog := (Real.continuousAt_log (ne_of_gt hA)).tendsto
  have h := (((hlog.comp h1).add ((hlog.comp h2).const_mul q)).sub
    ((hlog.comp hp).const_mul ((q+1)/2))).sub ((hlog.comp hm).const_mul ((q+1)/2))
  have hz : Real.log (radialExceptionalSlope q x)+q*Real.log (radialExceptionalSlope q x)-
      (q+1)/2*Real.log (radialExceptionalSlope q x)-
      (q+1)/2*Real.log (radialExceptionalSlope q x)=0 := by ring
  rw [hz] at h
  apply h.congr'
  filter_upwards [h1.eventually (eventually_gt_nhds hA), h2.eventually (eventually_gt_nhds hA),
    hp.eventually (eventually_gt_nhds hA), hm.eventually (eventually_gt_nhds hA)] with k hk1 hk2 hkp hkm
  have hN : ((k+1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hn1 : radialVertexExceptional q x k ≠ 0 := by intro he; simp [he] at hk1
  have hn2 : radialBranchExceptional q x k ≠ 0 := by intro he; simp [he] at hk2
  have hnp : radialEdgePlusExceptional q x k ≠ 0 := by intro he; simp [he] at hkp
  have hnm : radialEdgeMinusExceptional q x k ≠ 0 := by intro he; simp [he] at hkm
  simp only [Function.comp_apply]
  rw [Real.log_div hn1 hN, Real.log_div hn2 hN, Real.log_div hnp hN, Real.log_div hnm hN]
  ring


/-- Exact bridge from the actual branch conditional-mean reconstruction to
second-kind Chebyshev values. -/
theorem branchMean_scaled_eq_radialChebyshev {q : ℝ} (hq : 0 < q) (x : ℝ) (n : ℕ) :
    Real.sqrt q ^ n * branchMeanA q (2*Real.sqrt q*x) n = radialChebyshev x n ∧
    Real.sqrt q ^ (n+1) * branchMeanB q (2*Real.sqrt q*x) n = -radialChebyshevPrev x n := by
  have hq0 : q ≠ 0 := ne_of_gt hq
  have hs : Real.sqrt q ^ 2 = q := Real.sq_sqrt (le_of_lt hq)
  induction n with
  | zero => simp [branchMeanA, branchMeanB]
  | succ n ih =>
    constructor
    · rw [(branchMean_succ _ _ _).1, radialChebyshev_succ]
      calc
        Real.sqrt q ^ (n+1) *
            ((2*Real.sqrt q*x)/q*branchMeanA q (2*Real.sqrt q*x) n+
              branchMeanB q (2*Real.sqrt q*x) n) =
            (Real.sqrt q^2/q)*(2*x*(Real.sqrt q^n*branchMeanA q (2*Real.sqrt q*x) n))+
              Real.sqrt q^(n+1)*branchMeanB q (2*Real.sqrt q*x) n := by
                rw [pow_succ]
                ring
        _ = 2*x*radialChebyshev x n-radialChebyshevPrev x n := by
          rw [hs, div_self hq0, one_mul, ih.1, ih.2]
          ring
    · rw [(branchMean_succ _ _ _).2, radialChebyshevPrev_succ]
      calc
        Real.sqrt q ^ (n+1+1) * (-branchMeanA q (2*Real.sqrt q*x) n/q) =
            -(Real.sqrt q^2/q)*(Real.sqrt q^n*branchMeanA q (2*Real.sqrt q*x) n) := by
              rw [show n+1+1=n+2 by omega, pow_add]
              ring
        _ = -radialChebyshev x n := by rw [hs, div_self hq0, ih.1]; ring

/-- Actual descendant-profile squares have exactly the stated Chebyshev
quadratic coefficients, with no asymptotic identification left to assume. -/
theorem branchMean_scaled_quadratic {q : ℝ} (hq : 0 < q) (x root parent : ℝ) (n : ℕ) :
    q^n*(branchMeanA q (2*Real.sqrt q*x) n*root+
      branchMeanB q (2*Real.sqrt q*x) n*parent)^2 =
    (radialChebyshev x n*root-radialChebyshevPrev x n/Real.sqrt q*parent)^2 := by
  have hs0 : Real.sqrt q ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hq)
  have hs : Real.sqrt q ^ 2 = q := Real.sq_sqrt (le_of_lt hq)
  have ha := (branchMean_scaled_eq_radialChebyshev hq x n).1
  have hb := (branchMean_scaled_eq_radialChebyshev hq x n).2
  have hpow : q^n=(Real.sqrt q^n)^2 := by rw [← pow_mul, mul_comm n 2, pow_mul, hs]
  have hb' : Real.sqrt q^n*branchMeanB q (2*Real.sqrt q*x) n =
      -radialChebyshevPrev x n/Real.sqrt q := by
    apply (eq_div_iff hs0).2
    rw [pow_succ] at hb
    linear_combination hb
  rw [hpow, ← mul_pow]
  congr 1
  rw [mul_add, ← mul_assoc, ← mul_assoc, ha, hb']
  ring


/-- Uniform bound for all linear radial profiles in the strict bulk. -/
theorem radialChebyshev_linear_square_bound {x : ℝ} (hx : |x| < 1) (a b : ℝ) (n : ℕ) :
    (a*radialChebyshev x n+b*radialChebyshevPrev x n)^2 ≤
      (a^2+b^2)/(1-|x|) := by
  have hs := sq_nonneg (a*radialChebyshevPrev x n-b*radialChebyshev x n)
  have hcs : (a*radialChebyshev x n+b*radialChebyshevPrev x n)^2 ≤
      (a^2+b^2)*(radialChebyshev x n^2+radialChebyshevPrev x n^2) := by nlinarith
  calc
    _ ≤ (a^2+b^2)*(radialChebyshev x n^2+radialChebyshevPrev x n^2) := hcs
    _ ≤ (a^2+b^2)*(1/(1-|x|)) :=
      mul_le_mul_of_nonneg_left (radialChebyshev_square_bound hx n) (by positivity)
    _ = _ := by ring

theorem radialVertexExceptional_tendsto_atTop {q x : ℝ} (hq : 1 < q) (hx : |x| < 1) :
    Tendsto (radialVertexExceptional q x) atTop atTop := by
  have hN : Tendsto (fun k : ℕ => ((k+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have h := (radialVertexExceptional_cesaro hx hq).pos_mul_atTop
    (radialExceptionalSlope_pos hq hx) hN
  convert h using 1
  funext k
  have hn : ((k+1 : ℕ) : ℝ) ≠ 0 := by positivity
  exact (div_mul_cancel₀ _ hn).symm

/-- The normalized spherical wave profile. Its unscaled coefficient is
this value divided by `(sqrt q)^n`. -/
def radialScaledWave (q x : ℝ) (n : ℕ) : ℝ :=
  radialChebyshev x n-(2*x/(q+1))*radialChebyshevPrev x n

/-- Exact squared boundary error of the radius-`k+1` truncation; the actual
tree-shell identity is independent of these numerical bounds. -/
def radialBoundaryError (q x : ℝ) (k : ℕ) : ℝ :=
  (q+1)*(radialScaledWave q x (k+1)^2+radialScaledWave q x (k+2)^2)

/-- The finite radial truncation's normalized squared eigen-equation error
vanishes, derived from its actual bounded boundary and growing norm. -/
theorem radialBoundaryError_div_variance_tendsto_zero {q x : ℝ}
    (hq : 1 < q) (hx : |x| < 1) :
    Tendsto (fun k => radialBoundaryError q x k / radialVertexExceptional q x k)
      atTop (𝓝 0) := by
  let C := (1+(2*x/(q+1))^2)/(1-|x|)
  have hb (n : ℕ) : radialScaledWave q x n ^ 2 ≤ C := by
    simpa only [radialScaledWave, sub_eq_add_neg, neg_mul, one_mul, one_pow, neg_sq]
      using radialChebyshev_linear_square_bound hx 1 (-(2*x/(q+1))) n
  apply tendsto_bdd_div_atTop_nhds_zero (b := 0) (B := 2*(q+1)*C)
    (Eventually.of_forall (fun k => ?_))
    (Eventually.of_forall (fun k => ?_)) (radialVertexExceptional_tendsto_atTop hq hx)
  · unfold radialBoundaryError
    positivity
  · unfold radialBoundaryError
    have h1 := hb (k+1)
    have h2 := hb (k+2)
    nlinarith


/-- The same actual vertex gain in the root/parent branch-energy chart. -/
theorem radialVertexExceptional_branch_form {q : ℝ} (hq : 0 < q) (x : ℝ) (k : ℕ) :
    radialVertexExceptional q x k = 1+(q+1)*∑ n ∈ Finset.range (k+1),
      (radialChebyshev x n*(2*Real.sqrt q*x/(q+1))-
        radialChebyshevPrev x n/Real.sqrt q)^2 := by
  have hs0 : Real.sqrt q ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hq)
  have hs : Real.sqrt q^2=q := Real.sq_sqrt hq.le
  have hd0 : q+1 ≠ 0 := by linarith
  unfold radialVertexExceptional
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [radialChebyshev_succ]
  field_simp [hs0,hd0,ne_of_gt hq]
  ring_nf
  simp only [hs, show Real.sqrt q^4=q^2 by calc
    Real.sqrt q^4=(Real.sqrt q^2)^2 := by ring
    _=q^2 := by rw [hs]]
  ring

end GaussianWave.BS
