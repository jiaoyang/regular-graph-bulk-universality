import GeneralizedBulk.Gaussian.SeriesRotation
import GeneralizedBulk.Gaussian.SeriesPresentedBounds

/-! A common samplewise rotation identity for all spectral values and derivatives. -/
noncomputable section
open MeasureTheory BourgadeHuang
open scoped BigOperators
namespace GeneralizedBulk.Gaussian

/-- The entry formula for ordinary matrix conjugation. -/
theorem matrix_conjugation_entry (O M : EndpointMatrix) (i j : Fin 4) :
    (O * M * O.transpose) i j = ∑ a : Fin 4, ∑ b : Fin 4, (O i a * O j b) * M a b := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

/-- Finite endpoint conjugation commutes with an absolutely convergent scalar
series, with its summability proved separately for each of the sixteen entries. -/
theorem tsum_conjugated_entries {I : Type*} (O : EndpointMatrix) (raw raw' : I → EndpointMatrix)
    (coeff : I → ℂ) (heq : ∀ n, raw' n = O * raw n * O.transpose)
    (hs : ∀ a b, Summable (fun n => coeff n * raw n a b)) (i j : Fin 4) :
    (∑' n, coeff n * raw' n i j) =
      ∑ a : Fin 4, ∑ b : Fin 4, (O i a * O j b) * ∑' n, coeff n * raw n a b := by
  have hn (n : I) : coeff n * raw' n i j =
      ∑ a : Fin 4, ∑ b : Fin 4, (O i a * O j b) * (coeff n * raw n a b) := by
    rw [heq n, matrix_conjugation_entry]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    ring
  simp_rw [hn]
  have ht (a b : Fin 4) : Summable (fun n => (O i a * O j b) * (coeff n * raw n a b)) :=
    (hs a b).mul_left _
  rw [Summable.tsum_finsetSum (fun a ha => summable_sum (fun b hb => ht a b))]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Summable.tsum_finsetSum (fun b hb => ht a b)]
  simp only [tsum_mul_left]

/-- The entire common analytic version, including all derivatives, transforms
on one deterministic weighted-summability event. Only the anchor comparison
needs an almost-everywhere L² argument. -/
theorem presented_matrixField_conjugate {I : Type*} {s : AnchoredCountingState}
    (p : ParticlePresentation s I) (O A A' : EndpointMatrix) (sigma : ℂ)
    (raw raw' : I → EndpointMatrix)
    (hA : A' = O * A * O.transpose)
    (hraw : ∀ n, raw' n = O * raw n * O.transpose)
    (hweight : ∀ a b, Summable (fun n => nevanlinnaWeight (p.location n) * ‖raw n a b‖))
    (v : ℂ × Bool) :
    Presented.matrixField p (fun _ : Unit => A') sigma (fun n _ => raw' n) v () =
      O * Presented.matrixField p (fun _ : Unit => A) sigma (fun n _ => raw n) v () * O.transpose := by
  ext i j
  rw [matrix_conjugation_entry]
  rcases v with ⟨w, tag⟩
  by_cases hw : w.im = 0
  · cases tag <;> simp [Presented.matrixField, Presented.derivative, Presented.value,
      Presented.anchoredEntry, hw]
  cases tag
  · simp only [Presented.matrixField, Bool.false_eq_true, ↓reduceIte, Presented.value,
      Presented.anchoredEntry, hw]
    rw [tsum_conjugated_entries O raw raw' (fun n => sigma * anchorCorrection (p.location n) w)
      hraw (fun a b => Presented.summable_correction p sigma (fun n => raw n a b) (hweight a b) hw)]
    rw [hA, matrix_conjugation_entry]
    simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add]
  · simp only [Presented.matrixField, ↓reduceIte, Presented.derivative, hw]
    exact tsum_conjugated_entries O raw raw' (fun n => sigma * particleCoefficient (p.location n) (w, true))
      hraw (fun a b => Presented.summable_derivative p sigma (fun n => raw n a b) (hweight a b) hw) i j

end GeneralizedBulk.Gaussian
