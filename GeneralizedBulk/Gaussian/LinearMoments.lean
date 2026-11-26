import GeneralizedBulk.Gaussian.Polynomial

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace GeneralizedBulk.Gaussian

private theorem sum2_integral (f : Fin 4 → Fin 4 → (Fin 4 → ℝ) → ℝ)
    (hf : ∀ i j, Integrable (f i j) standardFour) :
    (∫ x, ∑ i, ∑ j, f i j x ∂standardFour) =
      ∑ i, ∑ j, ∫ x, f i j x ∂standardFour := by
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hf i j))]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_finset_sum _ (fun j _ => hf i j)

private theorem sum4_integral
    (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → (Fin 4 → ℝ) → ℝ)
    (hf : ∀ i j a b, Integrable (f i j a b) standardFour) :
    (∫ x, ∑ i, ∑ j, ∑ a, ∑ b, f i j a b x ∂standardFour) =
      ∑ i, ∑ j, ∑ a, ∑ b, ∫ x, f i j a b x ∂standardFour := by
  rw [sum2_integral _ (fun i j => integrable_finset_sum _ (fun a _ =>
    integrable_finset_sum _ (fun b _ => hf i j a b)))]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact sum2_integral _ (hf i j)

theorem integral_linear_pair (c d : Fin 4 → ℝ) :
    (∫ x, linearForm c x * linearForm d x ∂standardFour) = ∑ i, c i * d i := by
  have heq : (fun x => linearForm c x * linearForm d x) =
      (fun x => ∑ i, ∑ j, (c j * d i) * (x j * x i)) := by
    funext x
    simp only [linearForm, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq, sum2_integral _ (fun i j => (integrable_coord_pair j i).const_mul _)]
  simp_rw [integral_const_mul, integral_coord_pair]
  simp

set_option maxHeartbeats 3000000 in
theorem integral_linear_four (c d e f : Fin 4 → ℝ) :
    (∫ x, linearForm c x * linearForm d x * linearForm e x * linearForm f x ∂standardFour) =
      (∑ i, c i * d i) * (∑ i, e i * f i) +
      (∑ i, c i * e i) * (∑ i, d i * f i) +
      (∑ i, c i * f i) * (∑ i, d i * e i) := by
  have heq : (fun x => linearForm c x * linearForm d x * linearForm e x * linearForm f x) =
      (fun x => ∑ i, ∑ j, ∑ a, ∑ b, (c b * d a * e j * f i) *
        (x b * x a * x j * x i)) := by
    funext x
    simp only [linearForm, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [heq, sum4_integral _ (fun i j a b => (integrable_coord_four b a j i).const_mul _)]
  simp_rw [integral_const_mul, integral_coord_four]
  simp +decide [Fin.sum_univ_four]
  <;> ring

end GeneralizedBulk.Gaussian
