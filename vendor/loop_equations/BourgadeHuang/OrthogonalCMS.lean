import BourgadeHuang.OrthogonalRatioExpectationDerivatives

/-! # The genuine beta-one CMS equations

The numerator block has coupling two. The combined denominator block has
coupling one half and potential one quarter. All partials below are the actual
complex derivatives of the proved analytic expected ratio function.
-/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang
namespace OrthogonalCMS

def numeratorOperator {q : ℕ} (i : Fin q) (F : RatioFunction q)
    (u v w : Fin q → ℂ) : ℂ :=
  numeratorPartial i (numeratorPartial i F) u v w + F u v w +
    2*∑ j ∈ Finset.univ.erase i,
      (numeratorPartial i F u v w-numeratorPartial j F u v w)/(u i-u j) -
    (∑ j, (numeratorPartial i F u v w+2*firstDenominatorPartial j F u v w)/(u i-v j)) -
    (∑ j, (numeratorPartial i F u v w+2*secondDenominatorPartial j F u v w)/(u i-w j))

def firstDenominatorOperator {q : ℕ} (i : Fin q) (F : RatioFunction q)
    (u v w : Fin q → ℂ) : ℂ :=
  firstDenominatorPartial i (firstDenominatorPartial i F) u v w + (1/4:ℂ)*F u v w +
    (1/2:ℂ)*∑ j ∈ Finset.univ.erase i,
      (firstDenominatorPartial i F u v w-firstDenominatorPartial j F u v w)/(v i-v j) +
    (1/2:ℂ)*∑ j,
      (firstDenominatorPartial i F u v w-secondDenominatorPartial j F u v w)/(v i-w j) -
    ∑ j, (firstDenominatorPartial i F u v w+(1/2:ℂ)*numeratorPartial j F u v w)/(v i-u j)

def secondDenominatorOperator {q : ℕ} (i : Fin q) (F : RatioFunction q)
    (u v w : Fin q → ℂ) : ℂ :=
  secondDenominatorPartial i (secondDenominatorPartial i F) u v w + (1/4:ℂ)*F u v w +
    (1/2:ℂ)*∑ j ∈ Finset.univ.erase i,
      (secondDenominatorPartial i F u v w-secondDenominatorPartial j F u v w)/(w i-w j) +
    (1/2:ℂ)*∑ j,
      (secondDenominatorPartial i F u v w-firstDenominatorPartial j F u v w)/(w i-v j) -
    ∑ j, (secondDenominatorPartial i F u v w+(1/2:ℂ)*numeratorPartial j F u v w)/(w i-u j)

end OrthogonalCMS

private theorem orthogonal_numerator_loop_algebra {q : ℕ} (s : AnchoredCountingState)
    (u v w : Fin q → ℂ) (huv : ∀ j, SameOpenHalfPlane (u j) (v j))
    (hwv : ∀ j, SameOpenHalfPlane (w j) (v j))
    (hu : Function.Injective u) (hcV : CMS.CrossDistinct u v) (hcW : CMS.CrossDistinct u w) (i : Fin q) :
    (anchoredNevanlinna s (u i)^2-anchoredDerivative s (u i))*orthogonalCharacteristicRatios s u v w +
      orthogonalCharacteristicRatios s u v w +
      2*(∑ j ∈ Finset.univ.erase i, ((-anchoredNevanlinna s (u i)+anchoredNevanlinna s (u j))/(u i-u j))*
        orthogonalCharacteristicRatios s u v w) -
      (∑ j, ((-anchoredNevanlinna s (u i)+anchoredNevanlinna s (v j))/(u i-v j))*
        orthogonalCharacteristicRatios s u v w) -
      (∑ j, ((-anchoredNevanlinna s (u i)+anchoredNevanlinna s (w j))/(u i-w j))*
        orthogonalCharacteristicRatios s u v w) =
      (anchoredLoopHead .one s (u i)+∑ j,
        (anchoredDividedDifference s (u i) (v j)+anchoredDividedDifference s (u i) (w j)-
          2*anchoredDividedDifference s (u i) (u j)))*orthogonalCharacteristicRatios s u v w := by
  have hleft (j : Fin q) (hj : j ∈ Finset.univ.erase i) :
      (-anchoredNevanlinna s (u i)+anchoredNevanlinna s (u j))/(u i-u j) =
        -anchoredDividedDifference s (u i) (u j) := by
    rw [anchoredDividedDifference_eq_quotient s (huv i).left_offReal (huv j).left_offReal
      (fun he => (Finset.mem_erase.mp hj).1 (hu he).symm)]
    ring
  have hcrossV (j : Fin q) :
      (-anchoredNevanlinna s (u i)+anchoredNevanlinna s (v j))/(u i-v j) =
        -anchoredDividedDifference s (u i) (v j) := by
    rw [anchoredDividedDifference_eq_quotient s (huv i).left_offReal (huv j).right_offReal (hcV i j)]
    ring
  have hcrossW (j : Fin q) :
      (-anchoredNevanlinna s (u i)+anchoredNevanlinna s (w j))/(u i-w j) =
        -anchoredDividedDifference s (u i) (w j) := by
    rw [anchoredDividedDifference_eq_quotient s (huv i).left_offReal (hwv j).left_offReal (hcW i j)]
    ring
  have hsum : (∑ j, anchoredDividedDifference s (u i) (u j)) =
      (∑ j ∈ Finset.univ.erase i, anchoredDividedDifference s (u i) (u j)) + anchoredDerivative s (u i) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), anchoredDividedDifference_self s (huv i).left_offReal]
  rw [Finset.sum_congr rfl (fun j hj => congrArg
    (fun z => z*orthogonalCharacteristicRatios s u v w) (hleft j hj))]
  simp_rw [hcrossV,hcrossW,neg_mul,Finset.sum_neg_distrib]
  simp only [← Finset.sum_mul,anchoredLoopHead,Beta.value_one,
    Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,hsum]
  ring

private theorem integral_five_terms {q : ℕ} (ν : Measure AnchoredCountingState)
    (Q P : AnchoredCountingState → ℂ) (L M N : Fin q → AnchoredCountingState → ℂ)
    (I : Finset (Fin q)) (a b c d : ℂ)
    (hQ : Integrable Q ν) (hP : Integrable P ν)
    (hL : ∀ j, Integrable (L j) ν) (hM : ∀ j, Integrable (M j) ν) (hN : ∀ j, Integrable (N j) ν) :
    (∫ s, Q s+a*P s+b*(∑ j ∈ I,L j s)+c*(∑ j,M j s)+d*(∑ j,N j s) ∂ν) =
      (∫ s,Q s∂ν)+a*(∫s,P s∂ν)+b*(∑j∈I,∫s,L j s∂ν)+
        c*(∑j,∫s,M j s∂ν)+d*(∑j,∫s,N j s∂ν) := by
  have hLs := integrable_finset_sum I (fun j _ => hL j)
  have hMs := integrable_finset_sum Finset.univ (fun j _ => hM j)
  have hNs := integrable_finset_sum Finset.univ (fun j _ => hN j)
  have hQP : Integrable (fun s => Q s+a*P s) ν := hQ.add (hP.const_mul a)
  have hQPL : Integrable (fun s => Q s+a*P s+b*(∑j∈I,L j s)) ν := hQP.add (hLs.const_mul b)
  have hQPLM : Integrable (fun s => Q s+a*P s+b*(∑j∈I,L j s)+c*(∑j,M j s)) ν :=
    hQPL.add (hMs.const_mul c)
  rw [integral_add hQPLM (hNs.const_mul d),integral_add hQPL (hMs.const_mul c),
    integral_add hQP (hLs.const_mul b),integral_add hQ (hP.const_mul a)]

  simp only [integral_const_mul,integral_finset_sum _ (fun j _ => hL j),
    integral_finset_sum _ (fun j _ => hM j),integral_finset_sum _ (fun j _ => hN j)]

theorem expectedOrthogonalCharacteristicRatios_numerator_CMS {q : ℕ}
    (ν : Measure AnchoredCountingState) (hh : ExactAnchoredHierarchy ν .one)
    {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (u v w : Fin q → ℂ) (huv : ∀ j, SameOpenHalfPlane (u j) (v j))
    (hwv : ∀ j, SameOpenHalfPlane (w j) (v j))
    (hu : Function.Injective u) (hcV : CMS.CrossDistinct u v) (hcW : CMS.CrossDistinct u w) (i : Fin q) :
    OrthogonalCMS.numeratorOperator i (expectedOrthogonalCharacteristicRatios ν) u v w = 0 := by
  let P := fun s => orthogonalCharacteristicRatios s u v w
  let A := fun j s => -anchoredNevanlinna s (u j)*P s
  let B := fun j s => (1/2:ℂ)*anchoredNevanlinna s (v j)*P s
  let C := fun j s => (1/2:ℂ)*anchoredNevanlinna s (w j)*P s
  let Q := fun s => (anchoredNevanlinna s (u i)^2-anchoredDerivative s (u i))*P s
  have hA j := expectedOrthogonalCharacteristicRatios_numerator_first ν ha he u v w hwv j (huv j).left_offReal
  have hB j := expectedOrthogonalCharacteristicRatios_firstDenominator_first ν ha he u v w hwv j
  have hC j := expectedOrthogonalCharacteristicRatios_secondDenominator_first ν ha he u v w hwv j
  have hQ := expectedOrthogonalCharacteristicRatios_numerator_second ν ha he u v w hwv i (huv i).left_offReal
  have hloop := orthogonalCharacteristicRatios_integrable_and_endpoint_loop ν hh ha he u v w huv hwv (huv i).left_offReal
  have hiP : Integrable P ν := hloop.1
  have hiA j : Integrable (A j) ν := (hA j).1
  have hiB j : Integrable (B j) ν := (hB j).1
  have hiC j : Integrable (C j) ν := (hC j).1
  have hiQ : Integrable Q ν := hQ.1
  let L := fun j s => (A i s-A j s)/(u i-u j)
  let M := fun j s => (A i s+2*B j s)/(u i-v j)
  let N := fun j s => (A i s+2*C j s)/(u i-w j)
  have hiL j : Integrable (L j) ν := ((hiA i).sub (hiA j)).div_const _
  have hiM j : Integrable (M j) ν := ((hiA i).add ((hiB j).const_mul 2)).div_const _
  have hiN j : Integrable (N j) ν := ((hiA i).add ((hiC j).const_mul 2)).div_const _
  have hL j :
      (OrthogonalCMS.numeratorPartial i (expectedOrthogonalCharacteristicRatios ν) u v w-
        OrthogonalCMS.numeratorPartial j (expectedOrthogonalCharacteristicRatios ν) u v w)/(u i-u j) =
          ∫s,L j s∂ν := by
    rw [(hA i).2,(hA j).2,← integral_sub (hiA i) (hiA j),← integral_div]
  have hM j :
      (OrthogonalCMS.numeratorPartial i (expectedOrthogonalCharacteristicRatios ν) u v w+
        2*OrthogonalCMS.firstDenominatorPartial j (expectedOrthogonalCharacteristicRatios ν) u v w)/(u i-v j) =
          ∫s,M j s∂ν := by
    rw [(hA i).2,(hB j).2,← integral_const_mul,← integral_add (hiA i) ((hiB j).const_mul 2),← integral_div]
  have hN j :
      (OrthogonalCMS.numeratorPartial i (expectedOrthogonalCharacteristicRatios ν) u v w+
        2*OrthogonalCMS.secondDenominatorPartial j (expectedOrthogonalCharacteristicRatios ν) u v w)/(u i-w j) =
          ∫s,N j s∂ν := by
    rw [(hA i).2,(hC j).2,← integral_const_mul,← integral_add (hiA i) ((hiC j).const_mul 2),← integral_div]
  have hOp : OrthogonalCMS.numeratorOperator i (expectedOrthogonalCharacteristicRatios ν) u v w =
      ∫s,Q s+1*P s+2*(∑j∈Finset.univ.erase i,L j s)+(-1)*(∑j,M j s)+(-1)*(∑j,N j s)∂ν := by
    rw [integral_five_terms ν Q P L M N _ 1 2 (-1) (-1) hiQ hiP hiL hiM hiN]
    unfold OrthogonalCMS.numeratorOperator
    simp_rw [hL,hM,hN,hQ.2]
    change _ = (∫s,Q s∂ν)+1*(∫s,P s∂ν)+2*(∑j∈Finset.univ.erase i,∫s,L j s∂ν)+
      (-1)*(∑j,∫s,M j s∂ν)+(-1)*(∑j,∫s,N j s∂ν)
    simp only [one_mul,neg_one_mul,sub_eq_add_neg]
    rfl
  rw [hOp]
  convert hloop.2.2 using 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro s
  have hLs j : L j s = ((-anchoredNevanlinna s (u i)+anchoredNevanlinna s (u j))/(u i-u j))*P s := by dsimp [L,A]; ring
  have hMs j : M j s = ((-anchoredNevanlinna s (u i)+anchoredNevanlinna s (v j))/(u i-v j))*P s := by dsimp [M,A,B]; ring
  have hNs j : N j s = ((-anchoredNevanlinna s (u i)+anchoredNevanlinna s (w j))/(u i-w j))*P s := by dsimp [N,A,C]; ring
  simp_rw [hLs,hMs,hNs]
  simpa only [one_mul,neg_one_mul,sub_eq_add_neg] using orthogonal_numerator_loop_algebra s u v w huv hwv hu hcV hcW i


private theorem orthogonal_firstDenominator_loop_algebra {q : ℕ} (s : AnchoredCountingState)
    (u v w : Fin q → ℂ) (huv : ∀ j, SameOpenHalfPlane (u j) (v j))
    (hwv : ∀ j, SameOpenHalfPlane (w j) (v j))
    (hd : Function.Injective v) (hcU : CMS.CrossDistinct u v)
    (hcO : CMS.CrossDistinct v w) (i : Fin q) :
    ((1/2:ℂ)*anchoredDerivative s (v i)+(1/4:ℂ)*anchoredNevanlinna s (v i)^2)*orthogonalCharacteristicRatios s u v w +
      (1/4:ℂ)*orthogonalCharacteristicRatios s u v w +
      (1/2:ℂ)*(∑ j ∈ Finset.univ.erase i, (((1/2:ℂ)*anchoredNevanlinna s (v i)-(1/2:ℂ)*anchoredNevanlinna s (v j))/(v i-v j))*
        orthogonalCharacteristicRatios s u v w) +
      (1/2:ℂ)*(∑ j, (((1/2:ℂ)*anchoredNevanlinna s (v i)-(1/2:ℂ)*anchoredNevanlinna s (w j))/(v i-w j))*
        orthogonalCharacteristicRatios s u v w) -
      (∑ j, (((1/2:ℂ)*anchoredNevanlinna s (v i)-(1/2:ℂ)*anchoredNevanlinna s (u j))/(v i-u j))*
        orthogonalCharacteristicRatios s u v w) =
      (1/4:ℂ)*((anchoredLoopHead .one s (v i)+∑ j,
        (anchoredDividedDifference s (v i) (v j)+anchoredDividedDifference s (v i) (w j)-
          2*anchoredDividedDifference s (v i) (u j)))*orthogonalCharacteristicRatios s u v w) := by
  have hleft (j : Fin q) (hj : j ∈ Finset.univ.erase i) :
      ((1/2:ℂ)*anchoredNevanlinna s (v i)-(1/2:ℂ)*anchoredNevanlinna s (v j))/(v i-v j) =
        (1/2:ℂ)*anchoredDividedDifference s (v i) (v j) := by
    rw [anchoredDividedDifference_eq_quotient s (huv i).right_offReal (huv j).right_offReal
      (fun he => (Finset.mem_erase.mp hj).1 (hd he).symm)]
    ring
  have hcrossO (j : Fin q) :
      ((1/2:ℂ)*anchoredNevanlinna s (v i)-(1/2:ℂ)*anchoredNevanlinna s (w j))/(v i-w j) =
        (1/2:ℂ)*anchoredDividedDifference s (v i) (w j) := by
    rw [anchoredDividedDifference_eq_quotient s (huv i).right_offReal (hwv j).left_offReal (hcO i j)]
    ring
  have hcrossU (j : Fin q) :
      ((1/2:ℂ)*anchoredNevanlinna s (v i)-(1/2:ℂ)*anchoredNevanlinna s (u j))/(v i-u j) =
        (1/2:ℂ)*anchoredDividedDifference s (v i) (u j) := by
    rw [anchoredDividedDifference_eq_quotient s (huv i).right_offReal (huv j).left_offReal (hcU j i).symm]
    ring
  have hsum : (∑ j, anchoredDividedDifference s (v i) (v j)) =
      (∑ j ∈ Finset.univ.erase i, anchoredDividedDifference s (v i) (v j)) + anchoredDerivative s (v i) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),anchoredDividedDifference_self s (huv i).right_offReal]
  rw [Finset.sum_congr rfl (fun j hj => congrArg
    (fun z => z*orthogonalCharacteristicRatios s u v w) (hleft j hj))]
  simp_rw [hcrossO,hcrossU]
  simp only [← Finset.sum_mul,anchoredLoopHead,Beta.value_one,
    Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,hsum]
  ring

theorem expectedOrthogonalCharacteristicRatios_firstDenominator_CMS {q : ℕ}
    (ν : Measure AnchoredCountingState) (hh : ExactAnchoredHierarchy ν .one)
    {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (u v w : Fin q → ℂ) (huv : ∀ j, SameOpenHalfPlane (u j) (v j))
    (hwv : ∀ j, SameOpenHalfPlane (w j) (v j))
    (hd : Function.Injective v) (hcU : CMS.CrossDistinct u v)
    (hcO : CMS.CrossDistinct v w) (i : Fin q) :
    OrthogonalCMS.firstDenominatorOperator i (expectedOrthogonalCharacteristicRatios ν) u v w = 0 := by
  let P := fun s => orthogonalCharacteristicRatios s u v w
  let A := fun j s => (1/2:ℂ)*anchoredNevanlinna s (v j)*P s
  let B := fun j s => (1/2:ℂ)*anchoredNevanlinna s (w j)*P s
  let C := fun j s => -anchoredNevanlinna s (u j)*P s
  let Q := fun s => ((1/2:ℂ)*anchoredDerivative s (v i)+(1/4:ℂ)*anchoredNevanlinna s (v i)^2)*P s
  have hA j := expectedOrthogonalCharacteristicRatios_firstDenominator_first ν ha he u v w hwv j
  have hB j := expectedOrthogonalCharacteristicRatios_secondDenominator_first ν ha he u v w hwv j
  have hC j := expectedOrthogonalCharacteristicRatios_numerator_first ν ha he u v w hwv j (huv j).left_offReal
  have hQ := expectedOrthogonalCharacteristicRatios_firstDenominator_second ν ha he u v w hwv i
  have hloop := orthogonalCharacteristicRatios_integrable_and_endpoint_loop ν hh ha he u v w huv hwv (huv i).right_offReal
  have hiP : Integrable P ν := hloop.1
  have hiA j : Integrable (A j) ν := (hA j).1
  have hiB j : Integrable (B j) ν := (hB j).1
  have hiC j : Integrable (C j) ν := (hC j).1
  have hiQ : Integrable Q ν := hQ.1
  let L := fun j s => (A i s-A j s)/(v i-v j)
  let M := fun j s => (A i s-B j s)/(v i-w j)
  let N := fun j s => (A i s+(1/2:ℂ)*C j s)/(v i-u j)
  have hiL j : Integrable (L j) ν := ((hiA i).sub (hiA j)).div_const _
  have hiM j : Integrable (M j) ν := ((hiA i).sub (hiB j)).div_const _
  have hiN j : Integrable (N j) ν := ((hiA i).add ((hiC j).const_mul (1/2:ℂ))).div_const _
  have hL j :
      (OrthogonalCMS.firstDenominatorPartial i (expectedOrthogonalCharacteristicRatios ν) u v w-
        OrthogonalCMS.firstDenominatorPartial j (expectedOrthogonalCharacteristicRatios ν) u v w)/(v i-v j) =
          ∫s,L j s∂ν := by
    rw [(hA i).2,(hA j).2,← integral_sub (hiA i) (hiA j),← integral_div]
  have hM j :
      (OrthogonalCMS.firstDenominatorPartial i (expectedOrthogonalCharacteristicRatios ν) u v w-
        OrthogonalCMS.secondDenominatorPartial j (expectedOrthogonalCharacteristicRatios ν) u v w)/(v i-w j) =
          ∫s,M j s∂ν := by
    rw [(hA i).2,(hB j).2,← integral_sub (hiA i) (hiB j),← integral_div]
  have hN j :
      (OrthogonalCMS.firstDenominatorPartial i (expectedOrthogonalCharacteristicRatios ν) u v w+
        (1/2:ℂ)*OrthogonalCMS.numeratorPartial j (expectedOrthogonalCharacteristicRatios ν) u v w)/(v i-u j) =
          ∫s,N j s∂ν := by
    rw [(hA i).2,(hC j).2,← integral_const_mul,← integral_add (hiA i) ((hiC j).const_mul (1/2:ℂ)),← integral_div]
  have hOp : OrthogonalCMS.firstDenominatorOperator i (expectedOrthogonalCharacteristicRatios ν) u v w =
      ∫s,Q s+(1/4:ℂ)*P s+(1/2:ℂ)*(∑j∈Finset.univ.erase i,L j s)+(1/2:ℂ)*(∑j,M j s)+(-1)*(∑j,N j s)∂ν := by
    rw [integral_five_terms ν Q P L M N _ (1/4:ℂ) (1/2:ℂ) (1/2:ℂ) (-1) hiQ hiP hiL hiM hiN]
    unfold OrthogonalCMS.firstDenominatorOperator
    simp_rw [hL,hM,hN,hQ.2]
    change _ = (∫s,Q s∂ν)+(1/4:ℂ)*(∫s,P s∂ν)+(1/2:ℂ)*(∑j∈Finset.univ.erase i,∫s,L j s∂ν)+
      (1/2:ℂ)*(∑j,∫s,M j s∂ν)+(-1)*(∑j,∫s,N j s∂ν)
    simp only [neg_one_mul,sub_eq_add_neg]
    rfl
  rw [hOp]
  have hzero : (∫s,(1/4:ℂ)*((anchoredLoopHead .one s (v i)+∑j,
      (anchoredDividedDifference s (v i) (v j)+anchoredDividedDifference s (v i) (w j)-
        2*anchoredDividedDifference s (v i) (u j)))*orthogonalCharacteristicRatios s u v w)∂ν) = 0 := by
    rw [integral_const_mul,hloop.2.2,mul_zero]
  convert hzero using 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro s
  have hLs j : L j s = (((1/2:ℂ)*anchoredNevanlinna s (v i)-(1/2:ℂ)*anchoredNevanlinna s (v j))/(v i-v j))*P s := by dsimp [L,A]; ring
  have hMs j : M j s = (((1/2:ℂ)*anchoredNevanlinna s (v i)-(1/2:ℂ)*anchoredNevanlinna s (w j))/(v i-w j))*P s := by dsimp [M,A,B]; ring
  have hNs j : N j s = (((1/2:ℂ)*anchoredNevanlinna s (v i)-(1/2:ℂ)*anchoredNevanlinna s (u j))/(v i-u j))*P s := by dsimp [N,A,C]; ring
  simp_rw [hLs,hMs,hNs]
  simpa only [neg_one_mul,sub_eq_add_neg] using orthogonal_firstDenominator_loop_algebra s u v w huv hwv hd hcU hcO i


private theorem orthogonal_secondDenominator_loop_algebra {q : ℕ} (s : AnchoredCountingState)
    (u v w : Fin q → ℂ) (huv : ∀ j, SameOpenHalfPlane (u j) (v j))
    (hwv : ∀ j, SameOpenHalfPlane (w j) (v j))
    (hd : Function.Injective w) (hcU : CMS.CrossDistinct u w)
    (hcO : CMS.CrossDistinct w v) (i : Fin q) :
    ((1/2:ℂ)*anchoredDerivative s (w i)+(1/4:ℂ)*anchoredNevanlinna s (w i)^2)*orthogonalCharacteristicRatios s u v w +
      (1/4:ℂ)*orthogonalCharacteristicRatios s u v w +
      (1/2:ℂ)*(∑ j ∈ Finset.univ.erase i, (((1/2:ℂ)*anchoredNevanlinna s (w i)-(1/2:ℂ)*anchoredNevanlinna s (w j))/(w i-w j))*
        orthogonalCharacteristicRatios s u v w) +
      (1/2:ℂ)*(∑ j, (((1/2:ℂ)*anchoredNevanlinna s (w i)-(1/2:ℂ)*anchoredNevanlinna s (v j))/(w i-v j))*
        orthogonalCharacteristicRatios s u v w) -
      (∑ j, (((1/2:ℂ)*anchoredNevanlinna s (w i)-(1/2:ℂ)*anchoredNevanlinna s (u j))/(w i-u j))*
        orthogonalCharacteristicRatios s u v w) =
      (1/4:ℂ)*((anchoredLoopHead .one s (w i)+∑ j,
        (anchoredDividedDifference s (w i) (v j)+anchoredDividedDifference s (w i) (w j)-
          2*anchoredDividedDifference s (w i) (u j)))*orthogonalCharacteristicRatios s u v w) := by
  have hleft (j : Fin q) (hj : j ∈ Finset.univ.erase i) :
      ((1/2:ℂ)*anchoredNevanlinna s (w i)-(1/2:ℂ)*anchoredNevanlinna s (w j))/(w i-w j) =
        (1/2:ℂ)*anchoredDividedDifference s (w i) (w j) := by
    rw [anchoredDividedDifference_eq_quotient s (hwv i).left_offReal (hwv j).left_offReal
      (fun he => (Finset.mem_erase.mp hj).1 (hd he).symm)]
    ring
  have hcrossO (j : Fin q) :
      ((1/2:ℂ)*anchoredNevanlinna s (w i)-(1/2:ℂ)*anchoredNevanlinna s (v j))/(w i-v j) =
        (1/2:ℂ)*anchoredDividedDifference s (w i) (v j) := by
    rw [anchoredDividedDifference_eq_quotient s (hwv i).left_offReal (huv j).right_offReal (hcO i j)]
    ring
  have hcrossU (j : Fin q) :
      ((1/2:ℂ)*anchoredNevanlinna s (w i)-(1/2:ℂ)*anchoredNevanlinna s (u j))/(w i-u j) =
        (1/2:ℂ)*anchoredDividedDifference s (w i) (u j) := by
    rw [anchoredDividedDifference_eq_quotient s (hwv i).left_offReal (huv j).left_offReal (hcU j i).symm]
    ring
  have hsum : (∑ j, anchoredDividedDifference s (w i) (w j)) =
      (∑ j ∈ Finset.univ.erase i, anchoredDividedDifference s (w i) (w j)) + anchoredDerivative s (w i) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),anchoredDividedDifference_self s (hwv i).left_offReal]
  rw [Finset.sum_congr rfl (fun j hj => congrArg
    (fun z => z*orthogonalCharacteristicRatios s u v w) (hleft j hj))]
  simp_rw [hcrossO,hcrossU]
  simp only [← Finset.sum_mul,anchoredLoopHead,Beta.value_one,
    Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,hsum]
  ring

theorem expectedOrthogonalCharacteristicRatios_secondDenominator_CMS {q : ℕ}
    (ν : Measure AnchoredCountingState) (hh : ExactAnchoredHierarchy ν .one)
    {a : ℝ} (ha : 0 < a)
    (he : Integrable (fun s : AnchoredCountingState => Real.exp (a*‖s.val.2‖^2)) ν)
    (u v w : Fin q → ℂ) (huv : ∀ j, SameOpenHalfPlane (u j) (v j))
    (hwv : ∀ j, SameOpenHalfPlane (w j) (v j))
    (hd : Function.Injective w) (hcU : CMS.CrossDistinct u w)
    (hcO : CMS.CrossDistinct w v) (i : Fin q) :
    OrthogonalCMS.secondDenominatorOperator i (expectedOrthogonalCharacteristicRatios ν) u v w = 0 := by
  let P := fun s => orthogonalCharacteristicRatios s u v w
  let A := fun j s => (1/2:ℂ)*anchoredNevanlinna s (w j)*P s
  let B := fun j s => (1/2:ℂ)*anchoredNevanlinna s (v j)*P s
  let C := fun j s => -anchoredNevanlinna s (u j)*P s
  let Q := fun s => ((1/2:ℂ)*anchoredDerivative s (w i)+(1/4:ℂ)*anchoredNevanlinna s (w i)^2)*P s
  have hA j := expectedOrthogonalCharacteristicRatios_secondDenominator_first ν ha he u v w hwv j
  have hB j := expectedOrthogonalCharacteristicRatios_firstDenominator_first ν ha he u v w hwv j
  have hC j := expectedOrthogonalCharacteristicRatios_numerator_first ν ha he u v w hwv j (huv j).left_offReal
  have hQ := expectedOrthogonalCharacteristicRatios_secondDenominator_second ν ha he u v w hwv i
  have hloop := orthogonalCharacteristicRatios_integrable_and_endpoint_loop ν hh ha he u v w huv hwv (hwv i).left_offReal
  have hiP : Integrable P ν := hloop.1
  have hiA j : Integrable (A j) ν := (hA j).1
  have hiB j : Integrable (B j) ν := (hB j).1
  have hiC j : Integrable (C j) ν := (hC j).1
  have hiQ : Integrable Q ν := hQ.1
  let L := fun j s => (A i s-A j s)/(w i-w j)
  let M := fun j s => (A i s-B j s)/(w i-v j)
  let N := fun j s => (A i s+(1/2:ℂ)*C j s)/(w i-u j)
  have hiL j : Integrable (L j) ν := ((hiA i).sub (hiA j)).div_const _
  have hiM j : Integrable (M j) ν := ((hiA i).sub (hiB j)).div_const _
  have hiN j : Integrable (N j) ν := ((hiA i).add ((hiC j).const_mul (1/2:ℂ))).div_const _
  have hL j :
      (OrthogonalCMS.secondDenominatorPartial i (expectedOrthogonalCharacteristicRatios ν) u v w-
        OrthogonalCMS.secondDenominatorPartial j (expectedOrthogonalCharacteristicRatios ν) u v w)/(w i-w j) =
          ∫s,L j s∂ν := by
    rw [(hA i).2,(hA j).2,← integral_sub (hiA i) (hiA j),← integral_div]
  have hM j :
      (OrthogonalCMS.secondDenominatorPartial i (expectedOrthogonalCharacteristicRatios ν) u v w-
        OrthogonalCMS.firstDenominatorPartial j (expectedOrthogonalCharacteristicRatios ν) u v w)/(w i-v j) =
          ∫s,M j s∂ν := by
    rw [(hA i).2,(hB j).2,← integral_sub (hiA i) (hiB j),← integral_div]
  have hN j :
      (OrthogonalCMS.secondDenominatorPartial i (expectedOrthogonalCharacteristicRatios ν) u v w+
        (1/2:ℂ)*OrthogonalCMS.numeratorPartial j (expectedOrthogonalCharacteristicRatios ν) u v w)/(w i-u j) =
          ∫s,N j s∂ν := by
    rw [(hA i).2,(hC j).2,← integral_const_mul,← integral_add (hiA i) ((hiC j).const_mul (1/2:ℂ)),← integral_div]
  have hOp : OrthogonalCMS.secondDenominatorOperator i (expectedOrthogonalCharacteristicRatios ν) u v w =
      ∫s,Q s+(1/4:ℂ)*P s+(1/2:ℂ)*(∑j∈Finset.univ.erase i,L j s)+(1/2:ℂ)*(∑j,M j s)+(-1)*(∑j,N j s)∂ν := by
    rw [integral_five_terms ν Q P L M N _ (1/4:ℂ) (1/2:ℂ) (1/2:ℂ) (-1) hiQ hiP hiL hiM hiN]
    unfold OrthogonalCMS.secondDenominatorOperator
    simp_rw [hL,hM,hN,hQ.2]
    change _ = (∫s,Q s∂ν)+(1/4:ℂ)*(∫s,P s∂ν)+(1/2:ℂ)*(∑j∈Finset.univ.erase i,∫s,L j s∂ν)+
      (1/2:ℂ)*(∑j,∫s,M j s∂ν)+(-1)*(∑j,∫s,N j s∂ν)
    simp only [neg_one_mul,sub_eq_add_neg]
    rfl
  rw [hOp]
  have hzero : (∫s,(1/4:ℂ)*((anchoredLoopHead .one s (w i)+∑j,
      (anchoredDividedDifference s (w i) (v j)+anchoredDividedDifference s (w i) (w j)-
        2*anchoredDividedDifference s (w i) (u j)))*orthogonalCharacteristicRatios s u v w)∂ν) = 0 := by
    rw [integral_const_mul,hloop.2.2,mul_zero]
  convert hzero using 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro s
  have hLs j : L j s = (((1/2:ℂ)*anchoredNevanlinna s (w i)-(1/2:ℂ)*anchoredNevanlinna s (w j))/(w i-w j))*P s := by dsimp [L,A]; ring
  have hMs j : M j s = (((1/2:ℂ)*anchoredNevanlinna s (w i)-(1/2:ℂ)*anchoredNevanlinna s (v j))/(w i-v j))*P s := by dsimp [M,A,B]; ring
  have hNs j : N j s = (((1/2:ℂ)*anchoredNevanlinna s (w i)-(1/2:ℂ)*anchoredNevanlinna s (u j))/(w i-u j))*P s := by dsimp [N,A,C]; ring
  simp_rw [hLs,hMs,hNs]
  simpa only [neg_one_mul,sub_eq_add_neg] using orthogonal_secondDenominator_loop_algebra s u v w huv hwv hd hcU hcO i

end BourgadeHuang
