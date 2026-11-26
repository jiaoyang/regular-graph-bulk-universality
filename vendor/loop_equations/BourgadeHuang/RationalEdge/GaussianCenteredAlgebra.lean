import BourgadeHuang.RationalBulk.FiniteLoopAlgebra
import BourgadeHuang.RationalBulk.GaussianFiniteDivergence

/-! Centered polynomial tests for the actual finite Gaussian beta density. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory
namespace BourgadeHuang.RationalEdge
open RationalBulk

def centeredResolventTest {N n : ℕ} (x : Fin N → ℝ) (center : ℝ) (w : ℂ)
    (aux : Fin n → ℂ) (i : Fin N) : ℂ :=
  ((x i : ℂ) - w)⁻¹ * ∏ a, microscopicResolvent x center (aux a)

def centeredResolventTestDerivative {N n : ℕ} (x : Fin N → ℝ) (center : ℝ) (w : ℂ)
    (aux : Fin n → ℂ) (i : Fin N) : ℂ :=
  -(((x i : ℂ) - w)⁻¹)^2 * (∏ a, microscopicResolvent x center (aux a)) -
    ((x i : ℂ) - w)⁻¹ * ∑ a, (((x i : ℂ) - aux a)⁻¹)^2 *
      excludedProduct (fun b => microscopicResolvent x center (aux b)) a

theorem hasDerivAt_centeredResolvent_particle {N : ℕ} (x : Fin N → ℝ) (center : ℝ)
    (i : Fin N) {w : ℂ} (hw : w.im ≠ 0) :
    HasDerivAt (fun t : ℝ => microscopicResolvent (Function.update x i t) center w)
      (-(((x i : ℂ) - w)⁻¹)^2) (x i) := by
  classical
  have h (j : Fin N) : HasDerivAt
      (fun t : ℝ => (((Function.update x i t j : ℝ) : ℂ) - w)⁻¹)
      (if j = i then -(((x i : ℂ)-w)⁻¹)^2 else 0) (x i) := by
    by_cases hj : j = i
    · subst j
      simpa using hasDerivAt_particle_reciprocal (x i) hw
    · simpa [Function.update_of_ne hj, hj] using hasDerivAt_const (x i) (((x j : ℂ)-w)⁻¹)
  have hs := HasDerivAt.sum (u := Finset.univ) (fun j _ => h j)
  simpa [microscopicResolvent, div_eq_mul_inv, inv_pow, Function.update_eq_self,
    ite_mul, mul_ite] using hs.sub_const (center : ℂ)

theorem hasDerivAt_centeredResolventTest {N n : ℕ} (x : Fin N → ℝ) (center : ℝ)
    (i : Fin N) {w : ℂ} {aux : Fin n → ℂ}
    (hw : w.im ≠ 0) (ha : ∀ a, (aux a).im ≠ 0) :
    HasDerivAt (fun t : ℝ => centeredResolventTest (Function.update x i t) center w aux i)
      (centeredResolventTestDerivative x center w aux i) (x i) := by
  classical
  have hp := HasDerivAt.finset_prod (u := Finset.univ)
    (fun a _ => hasDerivAt_centeredResolvent_particle x center i (ha a))
  have hh := (hasDerivAt_particle_reciprocal (x i) hw).mul hp
  convert hh using 1
  · funext t
    simp [centeredResolventTest]
  · simp only [Function.update_eq_self, smul_eq_mul, centeredResolventTestDerivative, excludedProduct]
    simp only [mul_neg, mul_comm]
    simp only [neg_mul, Finset.sum_neg_distrib]
    ring

theorem sum_centeredResolventTestDerivative {N n : ℕ} (x : Fin N → ℝ) (center : ℝ)
    (w : ℂ) (aux : Fin n → ℂ) :
    (∑ i, centeredResolventTestDerivative x center w aux i) =
      -resolventDerivative x w * (∏ a, microscopicResolvent x center (aux a)) -
        ∑ a, interaction x w (aux a) *
          excludedProduct (fun b => microscopicResolvent x center (aux b)) a := by
  simp only [centeredResolventTestDerivative, Finset.sum_sub_distrib, ← Finset.sum_mul,
    Finset.sum_neg_distrib, resolventDerivative, interaction]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring


/-- Exact finite-density loop polynomial tested against arbitrary real-centered
resolvent products. The leading resolvent is deliberately uncentered. -/
def centeredGaussianLoop {N n : ℕ} (β : ℝ) (x : Fin N → ℝ) (center : ℝ)
    (w : ℂ) (aux : Fin n → ℂ) : ℂ :=
  (((2-(β:ℂ))/(β:ℂ))*resolventDerivative x w +
    (microscopicResolvent x 0 w)^2 + 1 + (w/(N:ℂ))*microscopicResolvent x 0 w) *
      (∏ a, microscopicResolvent x center (aux a)) +
    (2/(β:ℂ)) * ∑ a, interaction x w (aux a) *
      excludedProduct (fun b => microscopicResolvent x center (aux b)) a

theorem centered_gaussian_divergence_identity {N n : ℕ} {β : ℝ} (hβ : β ≠ 0)
    (hN : N ≠ 0) (x : Fin N → ℝ) (center : ℝ) (hx : Function.Injective x)
    {w : ℂ} {aux : Fin n → ℂ} (hw : w.im ≠ 0) :
    (Finset.sum (Finset.univ : Finset (Fin N)) (fun i =>
      centeredResolventTestDerivative x center w aux i +
       complexGaussianScore β x i * centeredResolventTest x center w aux i)) =
      -(β:ℂ)/2 * centeredGaussianLoop β x center w aux := by
  rw [Finset.sum_add_distrib, sum_centeredResolventTestDerivative]
  have hs : (∑ i : Fin N, complexGaussianScore β x i * centeredResolventTest x center w aux i) =
      (∑ i, complexGaussianScore β x i * ((x i:ℂ)-w)⁻¹) *
        (∏ a, microscopicResolvent x center (aux a)) := by
    simp only [centeredResolventTest, ←mul_assoc, Finset.sum_mul]
  rw [hs, sum_complexGaussianScore_reciprocal β x hx hw]
  have hb : (β:ℂ) ≠ 0 := by exact_mod_cast hβ
  have hn : (N:ℂ) ≠ 0 := by exact_mod_cast hN
  unfold centeredGaussianLoop
  field_simp
  <;> ring

end BourgadeHuang.RationalEdge
