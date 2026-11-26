import BourgadeHuang.OrthogonalRatioAnalytic

/-! True coordinate derivatives of orthogonal ratio products and their
expectations. Fractional denominator weights are retained in the second
 derivatives, rather than inferred from a formal symbolic substitution. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang

def orthogonalProductErase {q : ℕ} (s : AnchoredCountingState)
    (u v w : Fin q → ℂ) (i : Fin q) : ℂ :=
  ∏ j ∈ Finset.univ.erase i, orthogonalCharacteristicRatio s (u j) (v j) (w j)

theorem orthogonalProductErase_mul {q : ℕ} (s : AnchoredCountingState)
    (u v w : Fin q → ℂ) (i : Fin q) :
    orthogonalProductErase s u v w i * orthogonalCharacteristicRatio s (u i) (v i) (w i) =
      orthogonalCharacteristicRatios s u v w :=
  Finset.prod_erase_mul _ _ (Finset.mem_univ i)

theorem orthogonalCharacteristicRatios_update_numerator {q : ℕ} (s : AnchoredCountingState)
    (u v w : Fin q → ℂ) (i : Fin q) (z : ℂ) :
    orthogonalCharacteristicRatios s (Function.update u i z) v w =
      orthogonalProductErase s u v w i * orthogonalCharacteristicRatio s z (v i) (w i) := by
  rw [← orthogonalProductErase_mul s (Function.update u i z) v w i]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

theorem orthogonalCharacteristicRatios_update_firstDenominator {q : ℕ} (s : AnchoredCountingState)
    (u v w : Fin q → ℂ) (i : Fin q) (z : ℂ) :
    orthogonalCharacteristicRatios s u (Function.update v i z) w =
      orthogonalProductErase s u v w i * orthogonalCharacteristicRatio s (u i) z (w i) := by
  rw [← orthogonalProductErase_mul s u (Function.update v i z) w i]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

theorem orthogonalCharacteristicRatios_update_secondDenominator {q : ℕ} (s : AnchoredCountingState)
    (u v w : Fin q → ℂ) (i : Fin q) (z : ℂ) :
    orthogonalCharacteristicRatios s u v (Function.update w i z) =
      orthogonalProductErase s u v w i * orthogonalCharacteristicRatio s (u i) (v i) z := by
  rw [← orthogonalProductErase_mul s u v (Function.update w i z) i]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

theorem hasDerivAt_orthogonalCharacteristicRatio_numerator_second (s : AnchoredCountingState)
    {u v w : ℂ} (hu : u.im ≠ 0) :
    HasDerivAt (deriv (fun z => orthogonalCharacteristicRatio s z v w))
      ((anchoredNevanlinna s u^2-anchoredDerivative s u)*orthogonalCharacteristicRatio s u v w) u := by
  have hd := (hasDerivAt_anchoredNevanlinna s hu).neg.mul
    (hasDerivAt_orthogonalCharacteristicRatio_numerator s (v := v) (w := w) hu)
  have hd' : HasDerivAt (fun z => -anchoredNevanlinna s z * orthogonalCharacteristicRatio s z v w)
      ((anchoredNevanlinna s u^2-anchoredDerivative s u)*orthogonalCharacteristicRatio s u v w) u := by
    convert hd using 1
    ring
  apply hd'.congr_of_eventuallyEq
  filter_upwards [(isOpen_ne_fun Complex.continuous_im continuous_const).mem_nhds hu] with z hz
  exact (hasDerivAt_orthogonalCharacteristicRatio_numerator s hz).deriv

theorem hasDerivAt_orthogonalCharacteristicRatio_last_second (s : AnchoredCountingState)
    (u : ℂ) {v w : ℂ} (hwv : SameOpenHalfPlane w v) :
    HasDerivAt (deriv (fun z => orthogonalCharacteristicRatio s u v z))
      (((1/2:ℂ)*anchoredDerivative s w+(1/4:ℂ)*anchoredNevanlinna s w^2)*
        orthogonalCharacteristicRatio s u v w) w := by
  have hd := ((hasDerivAt_anchoredNevanlinna s hwv.left_offReal).const_mul (1/2:ℂ)).mul
    (hasDerivAt_orthogonalCharacteristicRatio_last s u hwv)
  have hd' : HasDerivAt (fun z => (1/2:ℂ)*anchoredNevanlinna s z * orthogonalCharacteristicRatio s u v z)
      (((1/2:ℂ)*anchoredDerivative s w+(1/4:ℂ)*anchoredNevanlinna s w^2)*
        orthogonalCharacteristicRatio s u v w) w := by
    convert hd using 1
    ring
  apply hd'.congr_of_eventuallyEq
  filter_upwards [sameOpenHalfPlane_nhds hwv] with z hz
  exact (hasDerivAt_orthogonalCharacteristicRatio_last s u hz).deriv

theorem hasDerivAt_orthogonalCharacteristicRatio_middle_second (s : AnchoredCountingState)
    (u : ℂ) {v w : ℂ} (hwv : SameOpenHalfPlane w v) :
    HasDerivAt (deriv (fun z => orthogonalCharacteristicRatio s u z w))
      (((1/2:ℂ)*anchoredDerivative s v+(1/4:ℂ)*anchoredNevanlinna s v^2)*
        orthogonalCharacteristicRatio s u v w) v := by
  have hd := ((hasDerivAt_anchoredNevanlinna s hwv.right_offReal).const_mul (1/2:ℂ)).mul
    (hasDerivAt_orthogonalCharacteristicRatio_middle s u hwv)
  have hd' : HasDerivAt (fun z => (1/2:ℂ)*anchoredNevanlinna s z * orthogonalCharacteristicRatio s u z w)
      (((1/2:ℂ)*anchoredDerivative s v+(1/4:ℂ)*anchoredNevanlinna s v^2)*
        orthogonalCharacteristicRatio s u v w) v := by
    convert hd using 1
    ring
  apply hd'.congr_of_eventuallyEq
  filter_upwards [sameOpenHalfPlane_nhds hwv.symm] with z hz
  exact (hasDerivAt_orthogonalCharacteristicRatio_middle s u hz.symm).deriv


theorem hasDerivAt_orthogonalCharacteristicRatios_numerator {q : ℕ}
    (s : AnchoredCountingState) (u v w : Fin q → ℂ) (i : Fin q) (hu : (u i).im ≠ 0) :
    HasDerivAt (fun z => orthogonalCharacteristicRatios s (Function.update u i z) v w)
      ((-anchoredNevanlinna s (u i))*orthogonalCharacteristicRatios s u v w) (u i) := by
  have heq : (fun z => orthogonalCharacteristicRatios s (Function.update u i z) v w) =
      (fun z => orthogonalProductErase s u v w i * (fun z => orthogonalCharacteristicRatio s z (v i) (w i)) z) :=
    funext (orthogonalCharacteristicRatios_update_numerator s u v w i)
  rw [heq]
  convert (hasDerivAt_orthogonalCharacteristicRatio_numerator s (v := v i) (w := w i) hu).const_mul (orthogonalProductErase s u v w i) using 1
  rw [← orthogonalProductErase_mul s u v w i]
  ring

theorem hasDerivAt_orthogonalCharacteristicRatios_numerator_second {q : ℕ}
    (s : AnchoredCountingState) (u v w : Fin q → ℂ) (i : Fin q) (hu : (u i).im ≠ 0) :
    HasDerivAt (deriv (fun z => orthogonalCharacteristicRatios s (Function.update u i z) v w))
      ((anchoredNevanlinna s (u i)^2-anchoredDerivative s (u i))*orthogonalCharacteristicRatios s u v w) (u i) := by
  have heq : (fun z => orthogonalCharacteristicRatios s (Function.update u i z) v w) =
      (fun z => orthogonalProductErase s u v w i * (fun z => orthogonalCharacteristicRatio s z (v i) (w i)) z) :=
    funext (orthogonalCharacteristicRatios_update_numerator s u v w i)
  rw [heq]
  have hd : HasDerivAt (fun z => orthogonalProductErase s u v w i * deriv (fun z => orthogonalCharacteristicRatio s z (v i) (w i)) z)
      ((anchoredNevanlinna s (u i)^2-anchoredDerivative s (u i))*orthogonalCharacteristicRatios s u v w) (u i) := by
    convert (hasDerivAt_orthogonalCharacteristicRatio_numerator_second s (v := v i) (w := w i) hu).const_mul (orthogonalProductErase s u v w i) using 1
    rw [← orthogonalProductErase_mul s u v w i]
    ring
  apply hd.congr_of_eventuallyEq
  filter_upwards [(isOpen_ne_fun Complex.continuous_im continuous_const).mem_nhds hu] with z hz
  exact deriv_const_mul _ (hasDerivAt_orthogonalCharacteristicRatio_numerator s (v := v i) (w := w i) hz).differentiableAt


theorem hasDerivAt_orthogonalCharacteristicRatios_firstDenominator {q : ℕ}
    (s : AnchoredCountingState) (u v w : Fin q → ℂ) (i : Fin q) (hi : SameOpenHalfPlane (w i) (v i)) :
    HasDerivAt (fun z => orthogonalCharacteristicRatios s u (Function.update v i z) w)
      (((1/2:ℂ)*anchoredNevanlinna s (v i))*orthogonalCharacteristicRatios s u v w) (v i) := by
  have heq : (fun z => orthogonalCharacteristicRatios s u (Function.update v i z) w) =
      (fun z => orthogonalProductErase s u v w i * (fun z => orthogonalCharacteristicRatio s (u i) z (w i)) z) :=
    funext (orthogonalCharacteristicRatios_update_firstDenominator s u v w i)
  rw [heq]
  convert (hasDerivAt_orthogonalCharacteristicRatio_middle s (u i) hi).const_mul (orthogonalProductErase s u v w i) using 1
  rw [← orthogonalProductErase_mul s u v w i]
  ring

theorem hasDerivAt_orthogonalCharacteristicRatios_firstDenominator_second {q : ℕ}
    (s : AnchoredCountingState) (u v w : Fin q → ℂ) (i : Fin q) (hi : SameOpenHalfPlane (w i) (v i)) :
    HasDerivAt (deriv (fun z => orthogonalCharacteristicRatios s u (Function.update v i z) w))
      (((1/2:ℂ)*anchoredDerivative s (v i)+(1/4:ℂ)*anchoredNevanlinna s (v i)^2)*orthogonalCharacteristicRatios s u v w) (v i) := by
  have heq : (fun z => orthogonalCharacteristicRatios s u (Function.update v i z) w) =
      (fun z => orthogonalProductErase s u v w i * (fun z => orthogonalCharacteristicRatio s (u i) z (w i)) z) :=
    funext (orthogonalCharacteristicRatios_update_firstDenominator s u v w i)
  rw [heq]
  have hd : HasDerivAt (fun z => orthogonalProductErase s u v w i * deriv (fun z => orthogonalCharacteristicRatio s (u i) z (w i)) z)
      (((1/2:ℂ)*anchoredDerivative s (v i)+(1/4:ℂ)*anchoredNevanlinna s (v i)^2)*orthogonalCharacteristicRatios s u v w) (v i) := by
    convert (hasDerivAt_orthogonalCharacteristicRatio_middle_second s (u i) hi).const_mul (orthogonalProductErase s u v w i) using 1
    rw [← orthogonalProductErase_mul s u v w i]
    ring
  apply hd.congr_of_eventuallyEq
  filter_upwards [sameOpenHalfPlane_nhds hi.symm] with z hz
  exact deriv_const_mul _ (hasDerivAt_orthogonalCharacteristicRatio_middle s (u i) hz.symm).differentiableAt


theorem hasDerivAt_orthogonalCharacteristicRatios_secondDenominator {q : ℕ}
    (s : AnchoredCountingState) (u v w : Fin q → ℂ) (i : Fin q) (hi : SameOpenHalfPlane (w i) (v i)) :
    HasDerivAt (fun z => orthogonalCharacteristicRatios s u v (Function.update w i z))
      (((1/2:ℂ)*anchoredNevanlinna s (w i))*orthogonalCharacteristicRatios s u v w) (w i) := by
  have heq : (fun z => orthogonalCharacteristicRatios s u v (Function.update w i z)) =
      (fun z => orthogonalProductErase s u v w i * (fun z => orthogonalCharacteristicRatio s (u i) (v i) z) z) :=
    funext (orthogonalCharacteristicRatios_update_secondDenominator s u v w i)
  rw [heq]
  convert (hasDerivAt_orthogonalCharacteristicRatio_last s (u i) hi).const_mul (orthogonalProductErase s u v w i) using 1
  rw [← orthogonalProductErase_mul s u v w i]
  ring

theorem hasDerivAt_orthogonalCharacteristicRatios_secondDenominator_second {q : ℕ}
    (s : AnchoredCountingState) (u v w : Fin q → ℂ) (i : Fin q) (hi : SameOpenHalfPlane (w i) (v i)) :
    HasDerivAt (deriv (fun z => orthogonalCharacteristicRatios s u v (Function.update w i z)))
      (((1/2:ℂ)*anchoredDerivative s (w i)+(1/4:ℂ)*anchoredNevanlinna s (w i)^2)*orthogonalCharacteristicRatios s u v w) (w i) := by
  have heq : (fun z => orthogonalCharacteristicRatios s u v (Function.update w i z)) =
      (fun z => orthogonalProductErase s u v w i * (fun z => orthogonalCharacteristicRatio s (u i) (v i) z) z) :=
    funext (orthogonalCharacteristicRatios_update_secondDenominator s u v w i)
  rw [heq]
  have hd : HasDerivAt (fun z => orthogonalProductErase s u v w i * deriv (fun z => orthogonalCharacteristicRatio s (u i) (v i) z) z)
      (((1/2:ℂ)*anchoredDerivative s (w i)+(1/4:ℂ)*anchoredNevanlinna s (w i)^2)*orthogonalCharacteristicRatios s u v w) (w i) := by
    convert (hasDerivAt_orthogonalCharacteristicRatio_last_second s (u i) hi).const_mul (orthogonalProductErase s u v w i) using 1
    rw [← orthogonalProductErase_mul s u v w i]
    ring
  apply hd.congr_of_eventuallyEq
  filter_upwards [sameOpenHalfPlane_nhds hi] with z hz
  exact deriv_const_mul _ (hasDerivAt_orthogonalCharacteristicRatio_last s (u i) hz).differentiableAt

end BourgadeHuang
