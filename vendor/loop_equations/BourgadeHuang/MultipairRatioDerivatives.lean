import BourgadeHuang.MultipairCharacteristicRatio
import BourgadeHuang.ExponentialRatioDenominatorSecond
import BourgadeHuang.CharacteristicRatioMeasurability
import BourgadeHuang.CMS.Gauge

/-! Exact coordinate derivatives of actual expected multipair ratios. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang

def expectedCharacteristicRatios {q : ℕ} (ν : Measure AnchoredCountingState)
    (u v : Fin q → ℂ) : ℂ := ∫ s, anchoredCharacteristicRatios s u v ∂ν

def ratioProductErase {q : ℕ} (u v : Fin q → ℂ) (i : Fin q) (s : AnchoredCountingState) : ℂ :=
  ∏ j ∈ Finset.univ.erase i, anchoredCharacteristicRatio s (u j) (v j)

theorem ratioProductErase_mul {q : ℕ} (s : AnchoredCountingState)
    (u v : Fin q → ℂ) (i : Fin q) :
    ratioProductErase u v i s * anchoredCharacteristicRatio s (u i) (v i) =
      anchoredCharacteristicRatios s u v :=
  Finset.prod_erase_mul _ _ (Finset.mem_univ i)

theorem characteristicRatios_update_left {q : ℕ} (s : AnchoredCountingState)
    (u v : Fin q → ℂ) (i : Fin q) (z : ℂ) :
    anchoredCharacteristicRatios s (Function.update u i z) v =
      ratioProductErase u v i s * anchoredCharacteristicRatio s z (v i) := by
  rw [← ratioProductErase_mul s (Function.update u i z) v i]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

theorem characteristicRatios_update_right {q : ℕ} (s : AnchoredCountingState)
    (u v : Fin q → ℂ) (i : Fin q) (z : ℂ) :
    anchoredCharacteristicRatios s u (Function.update v i z) =
      ratioProductErase u v i s * anchoredCharacteristicRatio s (u i) z := by
  rw [← ratioProductErase_mul s u (Function.update v i z) i]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

theorem measurable_ratioProductErase {q : ℕ} (u v : Fin q → ℂ)
    (huv : ∀ j, SameOpenHalfPlane (u j) (v j)) (i : Fin q) : Measurable (ratioProductErase u v i) :=
  Finset.measurable_prod _ (fun j _ => measurable_anchoredCharacteristicRatio (huv j))

theorem exponentialBound_ratioProductErase {q : ℕ} (u v : Fin q → ℂ)
    (huv : ∀ j, SameOpenHalfPlane (u j) (v j)) (i : Fin q) :
    AnchoredExponentialBound (ratioProductErase u v i) :=
  AnchoredExponentialBound.finset_prod _ _ (fun j _ => anchoredExponentialBound_characteristicRatio (huv j))

theorem expectedCharacteristicRatios_leftPartial {q : ℕ}
    (ν : Measure AnchoredCountingState) (β : Beta) (hh : ExactAnchoredHierarchy ν β)
    {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (u v : Fin q → ℂ) (huv : ∀ j, SameOpenHalfPlane (u j) (v j)) (i : Fin q) :
    Integrable (fun s => -anchoredNevanlinna s (u i)*anchoredCharacteristicRatios s u v) ν ∧
    CMS.leftPartial i (expectedCharacteristicRatios ν) u v =
      ∫ s, -anchoredNevanlinna s (u i)*anchoredCharacteristicRatios s u v ∂ν := by
  have h := exponentiallyWeightedRatio_numerator ν β hh ha he (ratioProductErase u v i)
    (measurable_ratioProductErase u v huv i).aestronglyMeasurable
    (exponentialBound_ratioProductErase u v huv i) (huv i)
  have hIns : (fun s => ratioProductErase u v i s * (-anchoredNevanlinna s (u i)*
      anchoredCharacteristicRatio s (u i) (v i))) =
      (fun s => -anchoredNevanlinna s (u i)*anchoredCharacteristicRatios s u v) := by
    funext s
    rw [← ratioProductErase_mul s u v i]
    ring
  rw [hIns] at h
  refine ⟨h.1, ?_⟩
  simpa only [CMS.leftPartial, expectedCharacteristicRatios, characteristicRatios_update_left]
    using h.2.deriv

theorem expectedCharacteristicRatios_rightPartial {q : ℕ}
    (ν : Measure AnchoredCountingState) (β : Beta) (hh : ExactAnchoredHierarchy ν β)
    {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (u v : Fin q → ℂ) (huv : ∀ j, SameOpenHalfPlane (u j) (v j)) (i : Fin q) :
    Integrable (fun s => anchoredNevanlinna s (v i)*anchoredCharacteristicRatios s u v) ν ∧
    CMS.rightPartial i (expectedCharacteristicRatios ν) u v =
      ∫ s, anchoredNevanlinna s (v i)*anchoredCharacteristicRatios s u v ∂ν := by
  have h := exponentiallyWeightedRatio_denominator ν β hh ha he (ratioProductErase u v i)
    (measurable_ratioProductErase u v huv i).aestronglyMeasurable
    (exponentialBound_ratioProductErase u v huv i) (huv i)
  have hIns : (fun s => ratioProductErase u v i s * (anchoredNevanlinna s (v i)*
      anchoredCharacteristicRatio s (u i) (v i))) =
      (fun s => anchoredNevanlinna s (v i)*anchoredCharacteristicRatios s u v) := by
    funext s
    rw [← ratioProductErase_mul s u v i]
    ring
  rw [hIns] at h
  refine ⟨h.1, ?_⟩
  simpa only [CMS.rightPartial, expectedCharacteristicRatios, characteristicRatios_update_right]
    using h.2.deriv

theorem expectedCharacteristicRatios_leftSecond {q : ℕ}
    (ν : Measure AnchoredCountingState) (β : Beta) (hh : ExactAnchoredHierarchy ν β)
    {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (u v : Fin q → ℂ) (huv : ∀ j, SameOpenHalfPlane (u j) (v j)) (i : Fin q) :
    Integrable (fun s => (anchoredNevanlinna s (u i)^2-anchoredDerivative s (u i))*
      anchoredCharacteristicRatios s u v) ν ∧
    CMS.leftPartial i (CMS.leftPartial i (expectedCharacteristicRatios ν)) u v =
      ∫ s, (anchoredNevanlinna s (u i)^2-anchoredDerivative s (u i))*
        anchoredCharacteristicRatios s u v ∂ν := by
  have h := exponentiallyWeightedRatio_second ν β hh ha he (ratioProductErase u v i)
    (measurable_ratioProductErase u v huv i).aestronglyMeasurable
    (exponentialBound_ratioProductErase u v huv i) (huv i)
  have hIns : (fun s => ratioProductErase u v i s * ((anchoredNevanlinna s (u i)^2-anchoredDerivative s (u i))*
      anchoredCharacteristicRatio s (u i) (v i))) =
      (fun s => (anchoredNevanlinna s (u i)^2-anchoredDerivative s (u i))*anchoredCharacteristicRatios s u v) := by
    funext s
    rw [← ratioProductErase_mul s u v i]
    ring
  rw [hIns] at h
  refine ⟨h.1, ?_⟩
  simpa only [CMS.leftPartial, Function.update_idem, Function.update_self,
    expectedCharacteristicRatios, characteristicRatios_update_left] using h.2.deriv

theorem expectedCharacteristicRatios_rightSecond {q : ℕ}
    (ν : Measure AnchoredCountingState) (β : Beta) (hh : ExactAnchoredHierarchy ν β)
    {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (u v : Fin q → ℂ) (huv : ∀ j, SameOpenHalfPlane (u j) (v j)) (i : Fin q) :
    Integrable (fun s => (anchoredNevanlinna s (v i)^2+anchoredDerivative s (v i))*
      anchoredCharacteristicRatios s u v) ν ∧
    CMS.rightPartial i (CMS.rightPartial i (expectedCharacteristicRatios ν)) u v =
      ∫ s, (anchoredNevanlinna s (v i)^2+anchoredDerivative s (v i))*
        anchoredCharacteristicRatios s u v ∂ν := by
  have h := exponentiallyWeightedRatio_denominator_second ν β hh ha he (ratioProductErase u v i)
    (measurable_ratioProductErase u v huv i).aestronglyMeasurable
    (exponentialBound_ratioProductErase u v huv i) (huv i)
  have hIns : (fun s => ratioProductErase u v i s * ((anchoredNevanlinna s (v i)^2+anchoredDerivative s (v i))*
      anchoredCharacteristicRatio s (u i) (v i))) =
      (fun s => (anchoredNevanlinna s (v i)^2+anchoredDerivative s (v i))*anchoredCharacteristicRatios s u v) := by
    funext s
    rw [← ratioProductErase_mul s u v i]
    ring
  rw [hIns] at h
  refine ⟨h.1, ?_⟩
  simpa only [CMS.rightPartial, Function.update_idem, Function.update_self,
    expectedCharacteristicRatios, characteristicRatios_update_right] using h.2.deriv

end BourgadeHuang
