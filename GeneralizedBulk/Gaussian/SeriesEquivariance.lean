import GeneralizedBulk.Gaussian.Series

/-!
# Measure-preserving pullbacks and finite endpoint conjugation of L² series

Both operations commute with the actual infinite L² sum by continuity. These
lemmas provide the anchor identity for ordinary Gaussian rotation invariance.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace GeneralizedBulk.Gaussian

variable {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

def pullbackL2 (T : Ω → Ω) (hT : MeasurePreserving T μ μ) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (Lp.compMeasurePreservingₗᵢ ℂ T hT).toContinuousLinearMap

theorem pullbackL2_ae (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (f : Lp ℂ 2 μ) :
    pullbackL2 μ T hT f =ᵐ[μ] (fun ω => f (T ω)) :=
  Lp.coeFn_compMeasurePreserving f hT

theorem pullback_l2Series (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (marks : ι → Lp ℂ 2 μ) (coeff : ι → ℂ)
    (hs : Summable fun n => coeff n • marks n) :
    pullbackL2 μ T hT (l2Series μ marks coeff) =
      l2Series μ (fun n => pullbackL2 μ T hT (marks n)) coeff := by
  unfold l2Series
  rw [ContinuousLinearMap.map_tsum _ hs]
  simp only [map_smul]

/-- Conjugation of an L² matrix by an ordinary endpoint matrix. -/
def conjugateL2 (O : EndpointMatrix) (M : Matrix (Fin 4) (Fin 4) (Lp ℂ 2 μ)) :
    Matrix (Fin 4) (Fin 4) (Lp ℂ 2 μ) :=
  fun i j => ∑ a : Fin 4, ∑ b : Fin 4, (O i a * O j b) • M a b

/-- Finite endpoint conjugation commutes with the actual centered marked sum. -/
theorem conjugate_l2Series (O : EndpointMatrix)
    (marks : ι → Matrix (Fin 4) (Fin 4) (Lp ℂ 2 μ)) (coeff : ι → ℂ)
    (hs : ∀ a b, Summable fun n => coeff n • marks n a b) (i j : Fin 4) :
    l2Series μ (fun n => conjugateL2 μ O (marks n) i j) coeff =
      conjugateL2 μ O (fun a b => l2Series μ (fun n => marks n a b) coeff) i j := by
  unfold l2Series conjugateL2
  have heq (n : ι) :
      coeff n • (∑ a : Fin 4, ∑ b : Fin 4, (O i a * O j b) • marks n a b) =
      ∑ a : Fin 4, ∑ b : Fin 4, (O i a * O j b) • (coeff n • marks n a b) := by
    simp only [Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    rw [mul_comm]
  simp_rw [heq]
  have hsingle (a b : Fin 4) : Summable fun n => (O i a * O j b) • (coeff n • marks n a b) :=
    (hs a b).const_smul _
  rw [Summable.tsum_finsetSum (fun a ha => summable_sum (fun b hb => hsingle a b))]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Summable.tsum_finsetSum (fun b hb => hsingle a b)]
  apply Finset.sum_congr rfl
  intro b hb
  exact Summable.tsum_const_smul _ (hs a b)

/-- The finite quadratic mark equivariance passes to the infinite L² anchor. -/
theorem l2Series_equivariant (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (O : EndpointMatrix) (marks : ι → Matrix (Fin 4) (Fin 4) (Lp ℂ 2 μ))
    (coeff : ι → ℂ) (hs : ∀ a b, Summable fun n => coeff n • marks n a b)
    (heq : ∀ n i j, pullbackL2 μ T hT (marks n i j) = conjugateL2 μ O (marks n) i j)
    (i j : Fin 4) :
    pullbackL2 μ T hT (l2Series μ (fun n => marks n i j) coeff) =
      conjugateL2 μ O (fun a b => l2Series μ (fun n => marks n a b) coeff) i j := by
  rw [pullback_l2Series μ T hT _ coeff (hs i j)]
  simp_rw [heq]
  exact conjugate_l2Series μ O marks coeff hs i j

end GeneralizedBulk.Gaussian
