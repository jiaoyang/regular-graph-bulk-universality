import BourgadeHuang.RationalBulk.GaussianBetaDensity
import BourgadeHuang.RationalBulk.RepulsionDerivative

/-! The actual logarithmic coordinate derivative of the Gaussian beta density. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter Set
namespace BourgadeHuang.RationalBulk

def gaussianBetaScore (β : ℝ) (N : ℕ) (x : Fin N → ℝ) (i : Fin N) : ℝ :=
  -(β / (2 * (N : ℝ))) * x i +
    β * ∑ j ∈ Finset.univ.erase i, (x i - x j)⁻¹

theorem gaussianBetaDensity_eq_zero_of_collision {β : ℝ} (hβ : 0 < β)
    {N : ℕ} (x : Fin N → ℝ) {i j : Fin N} (hij : i ≠ j) (hijx : x i = x j) :
    gaussianBetaDensity β N x = 0 := by
  have hpair : ∃ p ∈ gaussianBetaPairs N, |x p.1 - x p.2| ^ β = 0 := by
    rcases lt_or_gt_of_ne hij with hijlt | hijgt
    · exact ⟨(i,j), by simp [gaussianBetaPairs, hijlt], by simp [hijx, hβ.ne']⟩
    · exact ⟨(j,i), by simp [gaussianBetaPairs, hijgt], by simp [hijx, hβ.ne']⟩
  unfold gaussianBetaDensity
  rw [Finset.prod_eq_zero_iff.mpr hpair, mul_zero]

theorem gaussianBetaDensity_eq_zero_of_not_injective {β : ℝ} (hβ : 0 < β)
    {N : ℕ} (x : Fin N → ℝ) (hx : ¬ Function.Injective x) :
    gaussianBetaDensity β N x = 0 := by
  classical
  obtain ⟨i, j, hijx, hij⟩ := Function.not_injective_iff.mp hx
  exact gaussianBetaDensity_eq_zero_of_collision hβ x hij hijx

theorem gaussianBeta_incident_pair_sum {N : ℕ} (x : Fin N → ℝ) (i : Fin N) :
    (∑ p ∈ gaussianBetaPairs N,
      ((if p.1 = i then 1 else 0) - (if p.2 = i then 1 else 0)) *
        (x p.1 - x p.2)⁻¹) =
      ∑ j ∈ Finset.univ.erase i, (x i - x j)⁻¹ := by
  classical
  simp only [sub_mul, Finset.sum_sub_distrib]
  have hfirst : (∑ p ∈ gaussianBetaPairs N,
      (if p.1 = i then (1 : ℝ) else 0) * (x p.1 - x p.2)⁻¹) =
      ∑ j : Fin N, if i < j then (x i - x j)⁻¹ else 0 := by
    simp only [gaussianBetaPairs, Finset.sum_filter, Fintype.sum_prod_type, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    have he : (fun k : Fin N => if k < j then if k = i then (x k - x j)⁻¹ else 0 else 0) =
        (fun k => if k = i then (if i < j then (x i - x j)⁻¹ else 0) else 0) := by
      funext k
      by_cases hk : k = i <;> simp [hk]
    rw [he]
    simp
  have hsecond : (∑ p ∈ gaussianBetaPairs N,
      (if p.2 = i then (1 : ℝ) else 0) * (x p.1 - x p.2)⁻¹) =
      ∑ j : Fin N, if j < i then (x j - x i)⁻¹ else 0 := by
    simp only [gaussianBetaPairs, Finset.sum_filter, Fintype.sum_prod_type, ite_mul, one_mul, zero_mul]
    apply Finset.sum_congr rfl
    intro j hj
    have he : (fun k : Fin N => if j < k then if k = i then (x j - x k)⁻¹ else 0 else 0) =
        (fun k => if k = i then (if j < i then (x j - x i)⁻¹ else 0) else 0) := by
      funext k
      by_cases hk : k = i <;> simp [hk]
    rw [he]
    simp
  rw [hfirst, hsecond, ← Finset.sum_sub_distrib]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  simp only [lt_self_iff_false, if_false, sub_self, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  rcases lt_or_gt_of_ne hji with hjlt | hjgt
  · rw [if_pos hjlt, if_neg (not_lt_of_ge hjlt.le), zero_sub,
      ← neg_sub (x i) (x j), inv_neg, neg_neg]
  · rw [if_pos hjgt, if_neg (not_lt_of_ge hjgt.le), sub_zero]

theorem hasDerivAt_update_coordinate {N : ℕ} (x : Fin N → ℝ) (i j : Fin N) :
    HasDerivAt (fun t => Function.update x i t j) (if j = i then 1 else 0) (x i) := by
  by_cases h : j = i
  · subst j
    simpa using hasDerivAt_id (x i)
  · simpa [Function.update_of_ne h, h] using hasDerivAt_const (x i) (x j)

theorem hasDerivAt_gaussianBetaDensity {β : ℝ} {N : ℕ}
    (x : Fin N → ℝ) (i : Fin N) (hxi : ∀ j, j ≠ i → x i ≠ x j) :
    HasDerivAt (fun t => gaussianBetaDensity β N (Function.update x i t))
      (gaussianBetaScore β N x i * gaussianBetaDensity β N x) (x i) := by
  classical
  have hsum : HasDerivAt (fun t => ∑ j, (Function.update x i t j) ^ 2)
      (2 * x i) (x i) := by
    have h := _root_.HasDerivAt.sum (u := Finset.univ)
      (fun j _ => (hasDerivAt_update_coordinate x i j).pow 2)
    convert h using 1
    simp only [Function.update_eq_self, pow_one, mul_ite, mul_one, mul_zero]
    simp
  have hexp := (hsum.const_mul (-(β / (4 * (N : ℝ))))).exp
  have hprod : HasDerivAt
      (fun t => ∏ p ∈ gaussianBetaPairs N,
        |Function.update x i t p.1 - Function.update x i t p.2| ^ β)
      ((β * ∑ j ∈ Finset.univ.erase i, (x i - x j)⁻¹) *
        ∏ p ∈ gaussianBetaPairs N, |x p.1 - x p.2| ^ β) (x i) := by
    have h := hasDerivAt_finset_prod_logarithmic (gaussianBetaPairs N)
      (fun p t => |Function.update x i t p.1 - Function.update x i t p.2| ^ β)
      (fun p _ => β * ((if p.1 = i then 1 else 0) -
        (if p.2 = i then 1 else 0)) / (x p.1 - x p.2)) (x i) ?_
    · convert h using 1
      simp only [Function.update_eq_self, div_eq_mul_inv, mul_assoc,
        ← Finset.mul_sum, gaussianBeta_incident_pair_sum]
    · intro p hp
      have hp' : p.1 < p.2 := (Finset.mem_filter.mp hp).2
      by_cases hne : x p.1 - x p.2 ≠ 0
      · simpa only [Function.update_eq_self] using
          HasDerivAt.abs_rpow_logarithmic ((hasDerivAt_update_coordinate x i p.1).sub
            (hasDerivAt_update_coordinate x i p.2)) β
            (by simpa only [Function.update_eq_self] using hne)
      · have he : x p.1 = x p.2 := sub_eq_zero.mp (not_not.mp hne)
        have hp1 : p.1 ≠ i := by
          intro hi
          apply hxi p.2 (by intro h; exact (ne_of_lt hp') (hi.trans h.symm))
          simpa only [hi] using he
        have hp2 : p.2 ≠ i := by
          intro hi
          apply hxi p.1 (by intro h; exact (ne_of_lt hp') (h.trans hi.symm))
          simpa only [hi] using he.symm
        simpa only [Function.update_of_ne hp1, Function.update_of_ne hp2,
          if_neg hp1, if_neg hp2, sub_self, mul_zero, zero_div, zero_mul] using
          hasDerivAt_const (x i) (|x p.1 - x p.2| ^ β)
  have h := hexp.mul hprod
  convert h using 1
  simp only [Function.update_eq_self, gaussianBetaScore, gaussianBetaDensity]
  ring

end BourgadeHuang.RationalBulk
