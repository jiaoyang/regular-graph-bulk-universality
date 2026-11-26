import BourgadeHuang.RationalBulk.FiniteParticleLaw
import BourgadeHuang.RationalBulk.Foundation
import Mathlib.Analysis.Complex.RealDeriv

/-! Finite labelled-particle differential algebra for the Gaussian beta loop
identity. Repeated spectral parameters are allowed throughout. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory
namespace BourgadeHuang.RationalBulk

def resolventTest {N n : ℕ} (x : Fin N → ℝ) (w : ℂ)
    (aux : Fin n → ℂ) (i : Fin N) : ℂ :=
  ((x i : ℂ) - w)⁻¹ * ∏ a, microscopicResolvent x 0 (aux a)

def resolventTestDerivative {N n : ℕ} (x : Fin N → ℝ) (w : ℂ)
    (aux : Fin n → ℂ) (i : Fin N) : ℂ :=
  -(((x i : ℂ) - w)⁻¹)^2 * (∏ a, microscopicResolvent x 0 (aux a)) -
    ((x i : ℂ) - w)⁻¹ * ∑ a, (((x i : ℂ) - aux a)⁻¹)^2 *
      excludedProduct (fun b => microscopicResolvent x 0 (aux b)) a

theorem hasDerivAt_particle_reciprocal (t : ℝ) {w : ℂ} (hw : w.im ≠ 0) :
    HasDerivAt (fun u : ℝ => ((u : ℂ) - w)⁻¹) (-(((t : ℂ) - w)⁻¹)^2) t := by
  convert (((hasDerivAt_id (t : ℂ)).sub_const w).inv
    (real_sub_ne_zero t hw)).comp_ofReal using 1 <;> simp [div_eq_mul_inv, inv_pow]

theorem hasDerivAt_microscopicResolvent_particle {N : ℕ} (x : Fin N → ℝ)
    (i : Fin N) {w : ℂ} (hw : w.im ≠ 0) :
    HasDerivAt (fun t : ℝ => microscopicResolvent (Function.update x i t) 0 w)
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
    ite_mul, mul_ite] using hs

theorem hasDerivAt_resolventTest {N n : ℕ} (x : Fin N → ℝ)
    (i : Fin N) {w : ℂ} {aux : Fin n → ℂ}
    (hw : w.im ≠ 0) (ha : ∀ a, (aux a).im ≠ 0) :
    HasDerivAt (fun t : ℝ => resolventTest (Function.update x i t) w aux i)
      (resolventTestDerivative x w aux i) (x i) := by
  classical
  have hp := HasDerivAt.finset_prod (u := Finset.univ)
    (fun a _ => hasDerivAt_microscopicResolvent_particle x i (ha a))
  have hh := (hasDerivAt_particle_reciprocal (x i) hw).mul hp
  convert hh using 1
  · funext t
    simp [resolventTest]
  · simp only [Function.update_eq_self, smul_eq_mul, resolventTestDerivative, excludedProduct]
    simp only [mul_neg, mul_comm]
    simp only [neg_mul, Finset.sum_neg_distrib]
    ring

theorem sum_resolventTestDerivative {N n : ℕ} (x : Fin N → ℝ)
    (w : ℂ) (aux : Fin n → ℂ) :
    (∑ i, resolventTestDerivative x w aux i) =
      -resolventDerivative x w * (∏ a, microscopicResolvent x 0 (aux a)) -
        ∑ a, interaction x w (aux a) *
          excludedProduct (fun b => microscopicResolvent x 0 (aux b)) a := by
  simp only [resolventTestDerivative, Finset.sum_sub_distrib, ← Finset.sum_mul,
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

theorem reciprocal_repulsion_pair {N : ℕ} (x : Fin N → ℝ)
    (hx : Function.Injective x) {w : ℂ} (hw : w.im ≠ 0) (i j : Fin N) :
    ((x i : ℂ)-w)⁻¹ / ((x i : ℂ)-(x j : ℂ)) +
      ((x j : ℂ)-w)⁻¹ / ((x j : ℂ)-(x i : ℂ)) =
      -(((x i : ℂ)-w)⁻¹ * ((x j : ℂ)-w)⁻¹) +
        if i=j then (((x i : ℂ)-w)⁻¹)^2 else 0 := by
  by_cases hij : i = j
  · subst j
    simp [pow_two]
  · have hdiff : (x i : ℂ)-(x j : ℂ) ≠ 0 := by
      exact sub_ne_zero.mpr (by exact_mod_cast (hx.ne hij))
    have hdiff' : (x j : ℂ)-(x i : ℂ) ≠ 0 := by
      exact sub_ne_zero.mpr (by exact_mod_cast (hx.ne (Ne.symm hij)))
    rw [if_neg hij]
    field_simp [hdiff, hdiff', real_sub_ne_zero (x i) hw, real_sub_ne_zero (x j) hw]
    ring

theorem sum_reciprocal_repulsion {N : ℕ} (x : Fin N → ℝ)
    (hx : Function.Injective x) {w : ℂ} (hw : w.im ≠ 0) :
    2 * (∑ i, ∑ j, ((x i : ℂ)-w)⁻¹ / ((x i : ℂ)-(x j : ℂ))) =
      -(microscopicResolvent x 0 w)^2 + resolventDerivative x w := by
  have hp := congrArg (fun f : Fin N → Fin N → ℂ => ∑ i, ∑ j, f i j)
    (funext fun i => funext fun j => reciprocal_repulsion_pair x hx hw i j)
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, if_true] at hp
  have hc : (∑ i, ∑ j, ((x j : ℂ)-w)⁻¹ / ((x j : ℂ)-(x i : ℂ))) =
      ∑ i, ∑ j, ((x i : ℂ)-w)⁻¹ / ((x i : ℂ)-(x j : ℂ)) := Finset.sum_comm
  rw [hc] at hp
  have hs : (microscopicResolvent x 0 w)^2 =
      ∑ i, ∑ j, ((x i : ℂ)-w)⁻¹ * ((x j : ℂ)-w)⁻¹ := by
    simp only [microscopicResolvent, Complex.ofReal_zero, sub_zero, pow_two,
      Finset.sum_mul_sum]
  rw [hs, two_mul]
  exact hp

def complexGaussianScore {N : ℕ} (β : ℝ) (x : Fin N → ℝ) (i : Fin N) : ℂ :=
  -(β : ℂ) / (2 * (N : ℂ)) * (x i : ℂ) +
    (β : ℂ) * ∑ j ∈ Finset.univ.erase i, ((x i : ℂ)-(x j : ℂ))⁻¹

theorem sum_position_reciprocal {N : ℕ} (x : Fin N → ℝ)
    {w : ℂ} (hw : w.im ≠ 0) :
    (∑ i, (x i : ℂ) * ((x i : ℂ)-w)⁻¹) = N + w*microscopicResolvent x 0 w := by
  have hi (i : Fin N) : (x i : ℂ)*((x i : ℂ)-w)⁻¹ = 1+w*((x i : ℂ)-w)⁻¹ := by
    field_simp [real_sub_ne_zero (x i) hw]
  simp_rw [hi]
  simp [microscopicResolvent, Finset.sum_add_distrib, Finset.mul_sum]

theorem sum_complexGaussianScore_reciprocal {N : ℕ} (β : ℝ) (x : Fin N → ℝ)
    (hx : Function.Injective x) {w : ℂ} (hw : w.im ≠ 0) :
    (∑ i, complexGaussianScore β x i * ((x i : ℂ)-w)⁻¹) =
      -(β : ℂ) / (2*(N:ℂ)) * (N + w*microscopicResolvent x 0 w) +
        (β : ℂ)/2 * (-(microscopicResolvent x 0 w)^2 + resolventDerivative x w) := by
  classical
  have hsum (i : Fin N) : (∑ j ∈ Finset.univ.erase i, ((x i : ℂ)-(x j : ℂ))⁻¹) =
      ∑ j, ((x i : ℂ)-(x j : ℂ))⁻¹ := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp
  simp only [complexGaussianScore, add_mul, Finset.sum_add_distrib]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [sum_position_reciprocal x hw]
  congr 1
  have ht : (∑ i, (∑ j ∈ Finset.univ.erase i, ((x i : ℂ)-(x j : ℂ))⁻¹) *
      ((x i : ℂ)-w)⁻¹) = ∑ i, ∑ j, ((x i : ℂ)-w)⁻¹ / ((x i : ℂ)-(x j : ℂ)) := by
    simp_rw [hsum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp [div_eq_mul_inv, mul_comm]
  rw [ht]
  have hh := sum_reciprocal_repulsion x hx hw
  linear_combination (β : ℂ)/2 * hh

theorem loopIntegrand_finite {N n : ℕ} (β : ℝ) (x : Fin N → ℝ)
    {w : ℂ} {aux : Fin n → ℂ} (hw : w.im ≠ 0) (ha : ∀ a, (aux a).im ≠ 0) :
    loopIntegrand β (finiteAnchoredState x 0) w aux =
      (((2-(β:ℂ))/(β:ℂ))*resolventDerivative x w + (microscopicResolvent x 0 w)^2+1)*
        (∏ a, microscopicResolvent x 0 (aux a)) +
      (2/(β:ℂ))*∑ a, interaction x w (aux a)*
        excludedProduct (fun b => microscopicResolvent x 0 (aux b)) a := by
  unfold loopIntegrand
  simp only [finiteAnchoredState_nevanlinna x 0 hw, finiteAnchoredState_nevanlinna x 0 (ha _)]
  rw [show anchoredDerivative (finiteAnchoredState x 0) w = resolventDerivative x w from
    anchoredDerivative_eq_finite x 0 _ rfl hw]
  congr 2
  apply Finset.sum_congr rfl
  intro a _
  rw [show anchoredInteraction (finiteAnchoredState x 0) w (aux a) = interaction x w (aux a) from
    anchoredInteraction_eq_finite x 0 _ rfl hw (ha a)]

theorem gaussian_divergence_identity {N n : ℕ} {β : ℝ} (hβ : β ≠ 0)
    (hN : N ≠ 0) (x : Fin N → ℝ) (hx : Function.Injective x)
    {w : ℂ} {aux : Fin n → ℂ} (hw : w.im ≠ 0) (ha : ∀ a, (aux a).im ≠ 0) :
    (Finset.sum (Finset.univ : Finset (Fin N)) (fun i =>
      resolventTestDerivative x w aux i + complexGaussianScore β x i * resolventTest x w aux i)) =
      -(β : ℂ)/2 * (loopIntegrand β (finiteAnchoredState x 0) w aux +
        (w/(N:ℂ)) * (microscopicResolvent x 0 w * ∏ a, microscopicResolvent x 0 (aux a))) := by
  rw [Finset.sum_add_distrib, sum_resolventTestDerivative, loopIntegrand_finite β x hw ha]
  have hs : (∑ i : Fin N, complexGaussianScore β x i * resolventTest x w aux i) =
      (∑ i, complexGaussianScore β x i * ((x i:ℂ)-w)⁻¹) *
        (∏ a, microscopicResolvent x 0 (aux a)) := by
    simp only [resolventTest, ← mul_assoc, Finset.sum_mul]
  rw [hs, sum_complexGaussianScore_reciprocal β x hx hw]
  have hb : (β:ℂ) ≠ 0 := by exact_mod_cast hβ
  have hn : (N:ℂ) ≠ 0 := by exact_mod_cast hN
  field_simp
  <;> ring

end BourgadeHuang.RationalBulk
