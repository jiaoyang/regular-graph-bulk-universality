import BourgadeHuang.OrthogonalMixedNormalization
import BourgadeHuang.BalancedRatioMatching

/-! Simultaneous denominator pairing does not change the genuine orthogonal
observable, and hence can be chosen to match numerator half-plane signs. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang

theorem orthogonalCharacteristicRatios_permute_denominators {q : ℕ}
    (s : AnchoredCountingState) (u v w : Fin q → ℂ) (p : Equiv.Perm (Fin q)) :
    orthogonalCharacteristicRatios s u (fun j=>v (p j)) (fun j=>w (p j))=
      orthogonalCharacteristicRatios s u v w := by
  unfold orthogonalCharacteristicRatios orthogonalCharacteristicRatio
  rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]
  change entireCharacteristicRatios s u (fun j=>v (p j))*_=entireCharacteristicRatios s u v*_
  rw [entireCharacteristicRatios_permute_denominators,
    Equiv.prod_comp p (fun j=>Complex.exp ((1/2:ℂ)*nevanlinnaPathPrimitive s (w j) (v j)))]

theorem expectedOrthogonalCharacteristicRatios_permute_denominators {q : ℕ}
    (ν : Measure AnchoredCountingState) (u v w : Fin q → ℂ) (p : Equiv.Perm (Fin q)) :
    expectedOrthogonalCharacteristicRatios ν u (fun j=>v (p j)) (fun j=>w (p j))=
      expectedOrthogonalCharacteristicRatios ν u v w := by
  apply integral_congr_ae
  exact Eventually.of_forall (fun s=>orthogonalCharacteristicRatios_permute_denominators s u v w p)

theorem orthogonalCharacteristicRatios_permute_numerators {q : ℕ}
    (s : AnchoredCountingState) (u v w : Fin q → ℂ) (p : Equiv.Perm (Fin q)) :
    orthogonalCharacteristicRatios s (fun j=>u (p j)) v w=orthogonalCharacteristicRatios s u v w := by
  unfold orthogonalCharacteristicRatios orthogonalCharacteristicRatio
  rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]
  change entireCharacteristicRatios s (fun j=>u (p j)) v*_=entireCharacteristicRatios s u v*_
  rw [entireCharacteristicRatios_permute_numerators]

theorem expectedOrthogonalCharacteristicRatios_permute_numerators {q : ℕ}
    (ν : Measure AnchoredCountingState) (u v w : Fin q → ℂ) (p : Equiv.Perm (Fin q)) :
    expectedOrthogonalCharacteristicRatios ν (fun j=>u (p j)) v w=
      expectedOrthogonalCharacteristicRatios ν u v w := by
  apply integral_congr_ae
  exact Eventually.of_forall (fun s=>orthogonalCharacteristicRatios_permute_numerators s u v w p)

/-- Matching signs may be selected before applying the proved small-source
limit; the original observable remains unchanged by the matching. -/
theorem tendsto_expectedOrthogonalCharacteristicRatios_matched_normalized
    {A : Type*} {l : Filter A} {q : ℕ}
    (ν : Measure AnchoredCountingState) [IsProbabilityMeasure ν]
    (hh : ExactAnchoredHierarchy ν .one) {a : ℝ} (ha : 0<a)
    (he : Integrable (fun s : AnchoredCountingState=>Real.exp (a*‖s.val.2‖^2)) ν)
    (ε : Fin q → Bool) (u v w : A → Fin q → ℂ) (p : Equiv.Perm (Fin q)) (η δ : A → ℝ)
    (hδ : Tendsto δ l (𝓝 0))
    (hgeom : ∀ᶠt in l,0<η t ∧ 0<δ t ∧
      (∀j,η t≤(reflectComplex (ε j) (u t j)).im) ∧
      (∀j,η t≤(reflectComplex (ε j) (v t (p j))).im) ∧
      (∀j,η t≤(reflectComplex (ε j) (w t (p j))).im) ∧
      (∀j,‖u t j-v t (p j)‖≤δ t*η t) ∧ ∀j,‖u t j-w t (p j)‖≤δ t*η t) :
    Tendsto (fun t=>Complex.exp (∑j,signedOrthogonalRatioPhase (ε j) (u t j) (v t (p j)) (w t (p j)))*
      expectedOrthogonalCharacteristicRatios ν (u t) (v t) (w t)) l (𝓝 1) := by
  simpa only [expectedOrthogonalCharacteristicRatios_permute_denominators] using
    tendsto_expectedOrthogonalCharacteristicRatios_signed_normalized ν hh ha he ε u
      (fun t j=>v t (p j)) (fun t j=>w t (p j)) η δ hδ hgeom

end BourgadeHuang
