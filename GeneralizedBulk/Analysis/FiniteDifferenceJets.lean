import GeneralizedBulk.Analysis.TightApproximation
import GeneralizedBulk.Exterior.JetLift
import GeneralizedBulk.Analysis.WeakRelations

/-! Finite-dimensional value laws determine the joint value/derivative laws
when the actual finite-difference errors have a tight random envelope. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace GeneralizedBulk.Analysis
open Exterior
variable {I J : Type*} [Fintype I] [Fintype J]

def finiteValueJet (w : I → ℂ) (Z L : ℂ → J → ℂ) : (I × Bool × J) → ℂ :=
  fun t => if t.2.1 then L (w t.1) t.2.2 else Z (w t.1) t.2.2

def finitePairedValues (w : I → ℂ) (h : ℝ) (Z : ℂ → J → ℂ) : (I × Bool) → J → ℂ :=
  fun t => Z (w t.1 + if t.2 then (h : ℂ) else 0)

def finiteDifferenceTransform (h : ℝ) (v : (I × Bool) → J → ℂ) : (I × Bool × J) → ℂ :=
  fun t => if t.2.1 then (h : ℂ)⁻¹ * (v (t.1,true) t.2.2 - v (t.1,false) t.2.2)
    else v (t.1,false) t.2.2

theorem continuous_finiteDifferenceTransform (h : ℝ) : Continuous (finiteDifferenceTransform (I := I) (J := J) h) := by
  apply continuous_pi
  intro t
  unfold finiteDifferenceTransform
  split_ifs <;> fun_prop

def finiteDifferenceJet (w : I → ℂ) (h : ℝ) (Z : ℂ → J → ℂ) : (I × Bool × J) → ℂ :=
  finiteDifferenceTransform h (finitePairedValues w h Z)

theorem measurable_finiteValueJet {S : Type*} [MeasurableSpace S]
    (w : I → ℂ) (Z L : S → ℂ → J → ℂ)
    (hZ : ∀ u,Measurable (fun z => Z z u)) (hL : ∀ u,Measurable (fun z => L z u)) :
    Measurable (fun z => finiteValueJet w (Z z) (L z)) := by
  apply measurable_pi_lambda
  intro t
  unfold finiteValueJet
  split_ifs
  · exact (measurable_pi_apply t.2.2).comp (hL _)
  · exact (measurable_pi_apply t.2.2).comp (hZ _)

theorem measurable_finitePairedValues {S : Type*} [MeasurableSpace S]
    (w : I → ℂ) (h : ℝ) (Z : S → ℂ → J → ℂ)
    (hZ : ∀ u,Measurable (fun z => Z z u)) :
    Measurable (fun z => finitePairedValues w h (Z z)) :=
  measurable_pi_lambda _ (fun t => hZ _)

theorem finiteDifferenceJet_tendsto_of_hasDerivAt (w : I → ℂ)
    (Z L : ℂ → J → ℂ) (hd : ∀ i j,HasDerivAt (fun u => Z u j) (L (w i) j) (w i)) :
    Tendsto (fun R : ℕ => finiteDifferenceJet w (1/((R : ℝ)+1)) Z) atTop
      (𝓝 (finiteValueJet w Z L)) := by
  apply tendsto_pi_nhds.mpr
  rintro ⟨i,b,j⟩
  cases b
  · simpa only [finiteDifferenceJet,finiteDifferenceTransform,finitePairedValues,
      Bool.false_eq_true,↓reduceIte,add_zero,finiteValueJet] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => Z (w i) j) atTop (𝓝 (Z (w i) j)))
  · have hs : Tendsto horizontalStep atTop (𝓝[≠] (0 : ℂ)) :=
      tendsto_nhdsWithin_iff.mpr ⟨horizontalStep_tendsto,
        Eventually.of_forall horizontalStep_ne_zero⟩
    have ht := (hd i j).tendsto_slope_zero.comp hs
    simpa only [finiteDifferenceJet,finiteDifferenceTransform,finitePairedValues,
      Bool.false_eq_true,↓reduceIte,add_zero,finiteValueJet,
      horizontalStep,Function.comp_def,smul_eq_mul] using ht

theorem weakLaw_valueJet_of_tight_difference_error
    {S : ℕ → Type*} {T : Type*} [∀ n,MeasurableSpace (S n)] [MeasurableSpace T]
    (P : ∀ n,Measure (S n)) [∀ n,IsProbabilityMeasure (P n)]
    (Q : Measure T) [IsProbabilityMeasure Q]
    (w : I → ℂ) (ZN LN : ∀ n,S n → ℂ → J → ℂ) (Z L : T → ℂ → J → ℂ)
    (hZN : ∀ n u,Measurable (fun z => ZN n z u)) (hLN : ∀ n u,Measurable (fun z => LN n z u))
    (hZ : ∀ u,Measurable (fun z => Z z u)) (hL : ∀ u,Measurable (fun z => L z u))
    (hvalues : ∀ R : ℕ,External.WeakLawConverges
      (fun n => (P n).map (fun z => finitePairedValues w (1/((R : ℝ)+1)) (ZN n z)))
      (Q.map (fun z => finitePairedValues w (1/((R : ℝ)+1)) (Z z))))
    (M : ∀ n,S n → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (htight : ∀ δ : ℝ,0 < δ → ∃ B : ℝ,0 < B ∧
      ∀ n,(P n).real {z | B < M n z} ≤ δ)
    (hbound : ∀ (R n : ℕ) z,dist (finiteValueJet w (ZN n z) (LN n z))
      (finiteDifferenceJet w (1/((R : ℝ)+1)) (ZN n z)) ≤
      (K/((R : ℝ)+1))*M n z)
    (hderiv : ∀ᵐ z ∂Q,∀ i j,HasDerivAt (fun u => Z z u j) (L z (w i) j) (w i)) :
    External.WeakLawConverges
      (fun n => (P n).map (fun z => finiteValueJet w (ZN n z) (LN n z)))
      (Q.map (fun z => finiteValueJet w (Z z) (L z))) := by
  have hmeasN (R n : ℕ) : Measurable (fun z => finiteDifferenceJet w (1/((R : ℝ)+1)) (ZN n z)) :=
    (continuous_finiteDifferenceTransform _).measurable.comp
      (measurable_finitePairedValues _ _ _ (hZN n))
  have hmeas (R : ℕ) : Measurable (fun z => finiteDifferenceJet w (1/((R : ℝ)+1)) (Z z)) :=
    (continuous_finiteDifferenceTransform _).measurable.comp
      (measurable_finitePairedValues _ _ _ hZ)
  apply weakLaw_of_tight_dominated_approximations P Q
    (fun n z => finiteValueJet w (ZN n z) (LN n z))
    (fun R n z => finiteDifferenceJet w (1/((R : ℝ)+1)) (ZN n z))
    (fun R z => finiteDifferenceJet w (1/((R : ℝ)+1)) (Z z))
    (fun z => finiteValueJet w (Z z) (L z))
    (fun n => measurable_finiteValueJet w _ _ (hZN n) (hLN n)) hmeasN hmeas
    (measurable_finiteValueJet w _ _ hZ hL)
    (fun R => ?_) M (fun R => K/((R : ℝ)+1)) (fun R => by positivity)
    (by simpa only [div_eq_mul_inv,mul_zero,one_mul] using
      (tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun R : ℕ => K*(1/((R : ℝ)+1))) atTop (𝓝 (K*0))))
    htight hbound (hderiv.mono (fun z hz => finiteDifferenceJet_tendsto_of_hasDerivAt w _ _ hz))
  have hw := weakLaw_map _ _ (hvalues R) (finiteDifferenceTransform (J := J) (1/((R : ℝ)+1)))
    (continuous_finiteDifferenceTransform _)
  simpa only [Measure.map_map (continuous_finiteDifferenceTransform _).measurable
    (measurable_finitePairedValues _ _ _ (hZN _)),
    Measure.map_map (continuous_finiteDifferenceTransform _).measurable
      (measurable_finitePairedValues _ _ _ hZ)] using hw

end GeneralizedBulk.Analysis
