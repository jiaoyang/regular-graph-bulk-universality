import BourgadeHuang.MultipairRatioDerivatives

/-! The actual expected characteristic-ratio products satisfy the beta-two
Calogero--Moser--Sutherland equations, with genuine coordinate derivatives. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang

private theorem left_loop_algebra {q : ℕ} (s : AnchoredCountingState)
    (u v : Fin q → ℂ) (huv : ∀ j, SameOpenHalfPlane (u j) (v j))
    (hu : Function.Injective u) (hc : CMS.CrossDistinct u v) (i : Fin q) :
    (anchoredNevanlinna s (u i)^2-anchoredDerivative s (u i))*anchoredCharacteristicRatios s u v +
      anchoredCharacteristicRatios s u v +
      (∑ j ∈ Finset.univ.erase i, ((-anchoredNevanlinna s (u i)+anchoredNevanlinna s (u j))/(u i-u j))*
        anchoredCharacteristicRatios s u v) -
      (∑ j, ((-anchoredNevanlinna s (u i)+anchoredNevanlinna s (v j))/(u i-v j))*
        anchoredCharacteristicRatios s u v) =
      (anchoredLoopHead .two s (u i)+(2/Beta.two.value)*
        ∑ j, (anchoredDividedDifference s (u i) (v j)-anchoredDividedDifference s (u i) (u j)))*
          anchoredCharacteristicRatios s u v := by
  have hleft (j : Fin q) (hj : j ∈ Finset.univ.erase i) :
      (-anchoredNevanlinna s (u i)+anchoredNevanlinna s (u j))/(u i-u j) =
        -anchoredDividedDifference s (u i) (u j) := by
    rw [anchoredDividedDifference_eq_quotient s (huv i).left_offReal (huv j).left_offReal
      (fun he => (Finset.mem_erase.mp hj).1 (hu he).symm)]
    ring
  have hcross (j : Fin q) :
      (-anchoredNevanlinna s (u i)+anchoredNevanlinna s (v j))/(u i-v j) =
        -anchoredDividedDifference s (u i) (v j) := by
    rw [anchoredDividedDifference_eq_quotient s (huv i).left_offReal (huv j).right_offReal (hc i j)]
    ring
  have hsum : (∑ j, anchoredDividedDifference s (u i) (u j)) =
      (∑ j ∈ Finset.univ.erase i, anchoredDividedDifference s (u i) (u j)) + anchoredDerivative s (u i) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), anchoredDividedDifference_self s (huv i).left_offReal]
  rw [Finset.sum_congr rfl (fun j hj => congrArg (fun z => z*anchoredCharacteristicRatios s u v) (hleft j hj))]
  simp_rw [hcross, neg_mul, Finset.sum_neg_distrib]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  simp only [anchoredLoopHead, Beta.value_two, sub_self, zero_div, zero_mul, zero_add,
    div_self (by norm_num : (2:ℂ)≠0), one_mul, Finset.sum_sub_distrib, hsum]
  ring

/-- The numerator-block CMS equation follows from the exact loop hierarchy,
not from an assumed differential equation for the expectation. -/
theorem expectedCharacteristicRatios_leftOriginal {q : ℕ}
    (ν : Measure AnchoredCountingState) (hh : ExactAnchoredHierarchy ν .two)
    {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (u v : Fin q → ℂ) (huv : ∀ j, SameOpenHalfPlane (u j) (v j))
    (hu : Function.Injective u) (hc : CMS.CrossDistinct u v) (i : Fin q) :
    CMS.leftOriginal i (expectedCharacteristicRatios ν) u v = 0 := by
  let P := fun s => anchoredCharacteristicRatios s u v
  let A := fun j s => -anchoredNevanlinna s (u j)*P s
  let B := fun j s => anchoredNevanlinna s (v j)*P s
  let Q := fun s => (anchoredNevanlinna s (u i)^2-anchoredDerivative s (u i))*P s
  have hA (j : Fin q) := expectedCharacteristicRatios_leftPartial ν .two hh ha he u v huv j
  have hB (j : Fin q) := expectedCharacteristicRatios_rightPartial ν .two hh ha he u v huv j
  have hQ := expectedCharacteristicRatios_leftSecond ν .two hh ha he u v huv i
  have hloop := characteristicRatios_integrable_and_endpoint_loop ν .two hh ha he u v huv (huv i).left_offReal
  have hiP : Integrable P ν := hloop.1
  have hiA (j : Fin q) : Integrable (A j) ν := (hA j).1
  have hiB (j : Fin q) : Integrable (B j) ν := (hB j).1
  have hiQ : Integrable Q ν := hQ.1
  let L := fun j s => (A i s-A j s)/(u i-u j)
  let M := fun j s => (A i s+B j s)/(u i-v j)
  have hiL (j : Fin q) : Integrable (L j) ν := ((hiA i).sub (hiA j)).div_const _
  have hiM (j : Fin q) : Integrable (M j) ν := ((hiA i).add (hiB j)).div_const _
  have hL (j : Fin q) :
      (CMS.leftPartial i (expectedCharacteristicRatios ν) u v -
        CMS.leftPartial j (expectedCharacteristicRatios ν) u v)/(u i-u j) = ∫ s, L j s ∂ν := by
    rw [(hA i).2, (hA j).2, ← integral_sub (hiA i) (hiA j), ← integral_div]
  have hM (j : Fin q) :
      (CMS.leftPartial i (expectedCharacteristicRatios ν) u v +
        CMS.rightPartial j (expectedCharacteristicRatios ν) u v)/(u i-v j) = ∫ s, M j s ∂ν := by
    rw [(hA i).2, (hB j).2, ← integral_add (hiA i) (hiB j), ← integral_div]
  have hOp : CMS.leftOriginal i (expectedCharacteristicRatios ν) u v =
      ∫ s, Q s+P s+(∑ j ∈ Finset.univ.erase i, L j s)-(∑ j, M j s) ∂ν := by
    unfold CMS.leftOriginal
    simp_rw [hL, hM]
    rw [hQ.2, ← integral_finset_sum _ (fun j _ => hiL j),
      ← integral_finset_sum _ (fun j _ => hiM j)]
    change (∫ s, Q s ∂ν)+(∫ s, P s ∂ν)+(∫ s, ∑ j ∈ Finset.univ.erase i, L j s ∂ν)-
      (∫ s, ∑ j, M j s ∂ν) = _
    have hiQP : Integrable (fun s => Q s+P s) ν := hiQ.add hiP
    have hiLs : Integrable (fun s => ∑ j ∈ Finset.univ.erase i, L j s) ν :=
      integrable_finset_sum _ (fun j _ => hiL j)
    have hiMs : Integrable (fun s => ∑ j, M j s) ν := integrable_finset_sum _ (fun j _ => hiM j)
    have hiQL : Integrable (fun s => Q s+P s+(∑ j ∈ Finset.univ.erase i, L j s)) ν := hiQP.add hiLs
    rw [← integral_add hiQ hiP, ← integral_add hiQP hiLs, ← integral_sub hiQL hiMs]
  rw [hOp]
  convert hloop.2.2 using 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro s
  have hLs (j : Fin q) : L j s = ((-anchoredNevanlinna s (u i)+anchoredNevanlinna s (u j))/(u i-u j))*P s := by
    dsimp [L,A]
    ring
  have hMs (j : Fin q) : M j s = ((-anchoredNevanlinna s (u i)+anchoredNevanlinna s (v j))/(u i-v j))*P s := by
    dsimp [M,A,B]
    ring
  simp_rw [hLs,hMs]
  exact left_loop_algebra s u v huv hu hc i

private theorem right_loop_algebra {q : ℕ} (s : AnchoredCountingState)
    (u v : Fin q → ℂ) (huv : ∀ j, SameOpenHalfPlane (u j) (v j))
    (hv : Function.Injective v) (hc : CMS.CrossDistinct u v) (i : Fin q) :
    (anchoredNevanlinna s (v i)^2+anchoredDerivative s (v i))*anchoredCharacteristicRatios s u v +
      anchoredCharacteristicRatios s u v +
      (∑ j ∈ Finset.univ.erase i, ((anchoredNevanlinna s (v i)-anchoredNevanlinna s (v j))/(v i-v j))*
        anchoredCharacteristicRatios s u v) -
      (∑ j, ((anchoredNevanlinna s (v i)-anchoredNevanlinna s (u j))/(v i-u j))*
        anchoredCharacteristicRatios s u v) =
      (anchoredLoopHead .two s (v i)+(2/Beta.two.value)*
        ∑ j, (anchoredDividedDifference s (v i) (v j)-anchoredDividedDifference s (v i) (u j)))*
          anchoredCharacteristicRatios s u v := by
  have hright (j : Fin q) (hj : j ∈ Finset.univ.erase i) :
      (anchoredNevanlinna s (v i)-anchoredNevanlinna s (v j))/(v i-v j) =
        anchoredDividedDifference s (v i) (v j) :=
    (anchoredDividedDifference_eq_quotient s (huv i).right_offReal (huv j).right_offReal
      (fun he => (Finset.mem_erase.mp hj).1 (hv he).symm)).symm
  have hcross (j : Fin q) :
      (anchoredNevanlinna s (v i)-anchoredNevanlinna s (u j))/(v i-u j) =
        anchoredDividedDifference s (v i) (u j) :=
    (anchoredDividedDifference_eq_quotient s (huv i).right_offReal (huv j).left_offReal (hc j i).symm).symm
  have hsum : (∑ j, anchoredDividedDifference s (v i) (v j)) =
      (∑ j ∈ Finset.univ.erase i, anchoredDividedDifference s (v i) (v j)) + anchoredDerivative s (v i) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), anchoredDividedDifference_self s (huv i).right_offReal]
  rw [Finset.sum_congr rfl (fun j hj => congrArg (fun z => z*anchoredCharacteristicRatios s u v) (hright j hj))]
  simp_rw [hcross]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  simp only [anchoredLoopHead, Beta.value_two, sub_self, zero_div, zero_mul, zero_add,
    div_self (by norm_num : (2:ℂ)≠0), one_mul, Finset.sum_sub_distrib, hsum]
  ring

/-- The denominator-block CMS equation uses the genuine second denominator
 derivative, including its positive resolvent-derivative term. -/
theorem expectedCharacteristicRatios_rightOriginal {q : ℕ}
    (ν : Measure AnchoredCountingState) (hh : ExactAnchoredHierarchy ν .two)
    {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (u v : Fin q → ℂ) (huv : ∀ j, SameOpenHalfPlane (u j) (v j))
    (hv : Function.Injective v) (hc : CMS.CrossDistinct u v) (i : Fin q) :
    CMS.rightOriginal i (expectedCharacteristicRatios ν) u v = 0 := by
  let P := fun s => anchoredCharacteristicRatios s u v
  let A := fun j s => anchoredNevanlinna s (v j)*P s
  let B := fun j s => -anchoredNevanlinna s (u j)*P s
  let Q := fun s => (anchoredNevanlinna s (v i)^2+anchoredDerivative s (v i))*P s
  have hA (j : Fin q) := expectedCharacteristicRatios_rightPartial ν .two hh ha he u v huv j
  have hB (j : Fin q) := expectedCharacteristicRatios_leftPartial ν .two hh ha he u v huv j
  have hQ := expectedCharacteristicRatios_rightSecond ν .two hh ha he u v huv i
  have hloop := characteristicRatios_integrable_and_endpoint_loop ν .two hh ha he u v huv (huv i).right_offReal
  have hiP : Integrable P ν := hloop.1
  have hiA (j : Fin q) : Integrable (A j) ν := (hA j).1
  have hiB (j : Fin q) : Integrable (B j) ν := (hB j).1
  have hiQ : Integrable Q ν := hQ.1
  let L := fun j s => (A i s-A j s)/(v i-v j)
  let M := fun j s => (A i s+B j s)/(v i-u j)
  have hiL (j : Fin q) : Integrable (L j) ν := ((hiA i).sub (hiA j)).div_const _
  have hiM (j : Fin q) : Integrable (M j) ν := ((hiA i).add (hiB j)).div_const _
  have hL (j : Fin q) :
      (CMS.rightPartial i (expectedCharacteristicRatios ν) u v -
        CMS.rightPartial j (expectedCharacteristicRatios ν) u v)/(v i-v j) = ∫ s, L j s ∂ν := by
    rw [(hA i).2, (hA j).2, ← integral_sub (hiA i) (hiA j), ← integral_div]
  have hM (j : Fin q) :
      (CMS.rightPartial i (expectedCharacteristicRatios ν) u v +
        CMS.leftPartial j (expectedCharacteristicRatios ν) u v)/(v i-u j) = ∫ s, M j s ∂ν := by
    rw [(hA i).2, (hB j).2, ← integral_add (hiA i) (hiB j), ← integral_div]
  have hOp : CMS.rightOriginal i (expectedCharacteristicRatios ν) u v =
      ∫ s, Q s+P s+(∑ j ∈ Finset.univ.erase i, L j s)-(∑ j, M j s) ∂ν := by
    unfold CMS.rightOriginal
    simp_rw [hL, hM]
    rw [hQ.2, ← integral_finset_sum _ (fun j _ => hiL j),
      ← integral_finset_sum _ (fun j _ => hiM j)]
    change (∫ s, Q s ∂ν)+(∫ s, P s ∂ν)+(∫ s, ∑ j ∈ Finset.univ.erase i, L j s ∂ν)-
      (∫ s, ∑ j, M j s ∂ν) = _
    have hiQP : Integrable (fun s => Q s+P s) ν := hiQ.add hiP
    have hiLs : Integrable (fun s => ∑ j ∈ Finset.univ.erase i, L j s) ν :=
      integrable_finset_sum _ (fun j _ => hiL j)
    have hiMs : Integrable (fun s => ∑ j, M j s) ν := integrable_finset_sum _ (fun j _ => hiM j)
    have hiQL : Integrable (fun s => Q s+P s+(∑ j ∈ Finset.univ.erase i, L j s)) ν := hiQP.add hiLs
    rw [← integral_add hiQ hiP, ← integral_add hiQP hiLs, ← integral_sub hiQL hiMs]
  rw [hOp]
  convert hloop.2.2 using 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro s
  have hLs (j : Fin q) : L j s = ((anchoredNevanlinna s (v i)-anchoredNevanlinna s (v j))/(v i-v j))*P s := by
    dsimp [L,A]
    ring
  have hMs (j : Fin q) : M j s = ((anchoredNevanlinna s (v i)-anchoredNevanlinna s (u j))/(v i-u j))*P s := by
    dsimp [M,A,B]
    ring
  simp_rw [hLs,hMs]
  exact right_loop_algebra s u v huv hv hc i

end BourgadeHuang
