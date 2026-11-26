import GaussianWave.BS.Lower.FiniteMarkers

/-! Independent uniform marker decoration of an arbitrary finite color law,
and its quantitative entropy effect under faithful finite orbit coding. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
set_option maxHeartbeats 1200000

namespace GaussianWave.BS.Lower
open GaussianWave.BS.Reused.Entropy GaussianWave.BS.Reused.Entropy.Finite

variable {V F : Type*} [Fintype V] [Fintype F]

def uniformFieldMass (V : Type*) [Fintype V] (m : ℕ) (_w : V → Fin m) : ℝ :=
  ((m : ℝ)^Fintype.card V)⁻¹

theorem uniformFieldMass_nonneg (m : ℕ) (w : V → Fin m) : 0 ≤ uniformFieldMass V m w := by
  unfold uniformFieldMass
  positivity

theorem uniformFieldMass_sum (m : ℕ) (hm : 0 < m) : (∑ w : V → Fin m,uniformFieldMass V m w) = 1 := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  simp only [uniformFieldMass,Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_pow]
  exact mul_inv_cancel₀ (pow_ne_zero _ hm0)

theorem uniformFieldMass_entropy (m : ℕ) (hm : 0 < m) :
    entropy (uniformFieldMass V m) = (Fintype.card V : ℝ)*Real.log m := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hp0 : (m : ℝ)^Fintype.card V ≠ 0 := pow_ne_zero _ hm0
  simp only [entropy,uniformFieldMass,Real.negMulLog,Real.log_inv,Real.log_pow,
    Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,nsmul_eq_mul,Nat.cast_pow]
  field_simp

theorem uniformFieldMass_fin_eq_productMass (N m : ℕ) :
    uniformFieldMass (Fin N) m = productMass (fun _ : Fin N => uniformMarkerMass m) := by
  funext w
  simp only [uniformFieldMass,Fintype.card_fin,productMass,uniformMarkerMass,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin,inv_pow]

/-- The collision bound is independent of any enumeration of the vertex set. -/
theorem uniformFieldMass_noninjective_bound (m : ℕ) (hm : 0 < m) :
    (∑ w : V → Fin m,if Function.Injective w then 0 else uniformFieldMass V m w) ≤
      (Fintype.card V : ℝ)^2/(m : ℝ) := by
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let E : (V → Fin m) ≃ (Fin (Fintype.card V) → Fin m) := Equiv.arrowCongr e (Equiv.refl _)
  have hinj (w : V → Fin m) : Function.Injective (E w) ↔ Function.Injective w := by
    constructor
    · intro h a b hab
      apply e.injective
      apply h
      simpa only [E,Equiv.arrowCongr_apply,Equiv.refl_apply,Function.comp_apply,e.symm_apply_apply] using hab
    · intro h
      exact h.comp e.symm.injective
  have heq : (∑ w : V → Fin m,if Function.Injective w then 0 else uniformFieldMass V m w) =
      ∑ w : Fin (Fintype.card V) → Fin m,if Function.Injective w then 0 else
        productMass (fun _ : Fin (Fintype.card V) => uniformMarkerMass m) w := by
    rw [← Equiv.sum_comp E]
    apply Finset.sum_congr rfl
    intro w hw
    simp only [hinj]
    split_ifs
    · rfl
    · simp only [uniformFieldMass,productMass,uniformMarkerMass,Finset.prod_const,
        Finset.card_univ,Fintype.card_fin,inv_pow]
  let P := uniformMarkerLaw (Fintype.card V) m hm
  have hmass : lawMass P id = productMass (fun _ : Fin (Fintype.card V) => uniformMarkerMass m) :=
    independentColoringLaw_lawMass _ _ _
  have hexp := finite_law_expectation P id measurable_id
    (fun w : Fin (Fintype.card V) → Fin m => if Function.Injective w then (0 : ℝ) else 1)
  rw [hmass] at hexp
  simp only [mul_ite,mul_zero,mul_one,Function.id_def] at hexp
  have hint : (∫ w : Fin (Fintype.card V) → Fin m,if Function.Injective w then (0 : ℝ) else 1 ∂P) =
      P.real {w | ¬Function.Injective w} := by
    simpa only [Set.indicator,Set.mem_setOf_eq,Pi.one_apply,ite_not] using
      (integral_indicator_one (μ := P) ((Set.toFinite {w | ¬Function.Injective w}).measurableSet))
  rw [heq,hexp,hint]
  exact uniformMarkerLaw_noninjective_probability (Fintype.card V) m hm

/-- Arbitrary original colors and an independent actual uniform marker field. -/
def markerDecoratedMass (p : (V → F) → ℝ) (m : ℕ) (w : V → F × Fin m) : ℝ :=
  p (fun v => (w v).1)*uniformFieldMass V m (fun v => (w v).2)

theorem markerDecoratedMass_nonneg (p : (V → F) → ℝ) (hp : ∀ w,0 ≤ p w) (m : ℕ)
    (w : V → F × Fin m) : 0 ≤ markerDecoratedMass p m w :=
  mul_nonneg (hp _) (uniformFieldMass_nonneg m _)

theorem markerDecoratedMass_sum (p : (V → F) → ℝ) (hs : ∑ w,p w = 1) (m : ℕ) (hm : 0 < m) :
    (∑ w,markerDecoratedMass p m w) = 1 := by
  let e := Equiv.arrowProdEquivProdArrow V (fun _ => F) (fun _ => Fin m)
  rw [← Equiv.sum_comp e.symm]
  change (∑ z : (V → F) × (V → Fin m),p z.1*uniformFieldMass V m z.2) = 1
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum,uniformFieldMass_sum m hm,mul_one]
  exact hs

/-- The exact independent-marker entropy contribution is the number of
vertices times `log m`, for every original finite color law. -/
theorem markerDecoratedMass_entropy (p : (V → F) → ℝ) (hs : ∑ w,p w = 1) (m : ℕ) (hm : 0 < m) :
    entropy (markerDecoratedMass p m) = entropy p+(Fintype.card V : ℝ)*Real.log m := by
  let e := Equiv.arrowProdEquivProdArrow V (fun _ => F) (fun _ => Fin m)
  have he : entropy (markerDecoratedMass p m) =
      entropy (fun z : (V → F) × (V → Fin m) => p z.1*uniformFieldMass V m z.2) := by
    unfold entropy
    rw [← Equiv.sum_comp e.symm]
    rfl
  rw [he,entropy_product p (uniformFieldMass V m) hs (uniformFieldMass_sum m hm),uniformFieldMass_entropy m hm]

/-- Marker collision mass is unchanged by mixing with any independent
original finite color law. -/
theorem markerDecoratedMass_collision_bound (p : (V → F) → ℝ) (hs : ∑ w,p w = 1)
    (m : ℕ) (hm : 0 < m) :
    (∑ w : V → F × Fin m,if Function.Injective (fun v => (w v).2) then 0 else markerDecoratedMass p m w) ≤
      (Fintype.card V : ℝ)^2/(m : ℝ) := by
  let e := Equiv.arrowProdEquivProdArrow V (fun _ => F) (fun _ => Fin m)
  rw [← Equiv.sum_comp e.symm]
  change (∑ z : (V → F) × (V → Fin m),if Function.Injective z.2 then 0 else p z.1*uniformFieldMass V m z.2) ≤ _
  have he : (∑ z : (V → F) × (V → Fin m),if Function.Injective z.2 then 0 else p z.1*uniformFieldMass V m z.2) =
      ∑ z : (V → F) × (V → Fin m),p z.1*(if Function.Injective z.2 then 0 else uniformFieldMass V m z.2) := by
    apply Finset.sum_congr rfl
    intro z hz
    split_ifs <;> simp
  rw [he,Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul,hs,one_mul]
  exact uniformFieldMass_noninjective_bound m hm

section OrbitDecoration
variable {G B : Type*} [Group G] [Fintype G] [Fintype B] [MulAction G V] [FaithfulSMul G V]

local instance reindexLabelAction (m : ℕ) : MulAction G (V → F × Fin m) := arrowAction

/-- Quantitative free-marker orbit coding with every entropy term computed
from the literal decorated mass function. -/
theorem marker_orbit_entropy_defect_bound (p : (V → F) → ℝ)
    (hp : ∀ w,0 ≤ p w) (hs : ∑ w,p w = 1)
    (hinv : ∀ (g : G) c,p (fun v => c (g⁻¹ • v)) = p c)
    (m : ℕ) (hm : 0 < m) (f : (V → F × Fin m) → B)
    (hcode : ∀ w w',f w = f w' ↔ w ∈ MulAction.orbit G w') :
    0 ≤ entropy (pushMass f (markerDecoratedMass p m))-entropy p-
        (Fintype.card V : ℝ)*Real.log m+Real.log (Fintype.card G) ∧
      entropy (pushMass f (markerDecoratedMass p m))-entropy p-
        (Fintype.card V : ℝ)*Real.log m+Real.log (Fintype.card G) ≤
          ((Fintype.card V : ℝ)^2/(m : ℝ))*Real.log (Fintype.card G) := by
  have hpinv (g : G) (w : V → F × Fin m) : markerDecoratedMass p m (g • w) = markerDecoratedMass p m w := by
    unfold markerDecoratedMass uniformFieldMass
    change p (fun v => (w (g⁻¹ • v)).1)*_ = _
    exact congrArg (fun a : ℝ => a*((m : ℝ)^Fintype.card V)⁻¹) (hinv g (fun v => (w v).1))
  have hbound := entropy_orbit_coding_defect_bound f hcode (markerDecoratedMass p m)
    (markerDecoratedMass_nonneg p hp m) (markerDecoratedMass_sum p hs m hm) hpinv
    (fun w => Function.Injective (fun v => (w v).2))
    (fun w hw => reindexing_free_of_injective_markers w hw)
  have hcoll := markerDecoratedMass_collision_bound p hs m hm
  have hlog : 0 ≤ Real.log (Fintype.card G) := Real.log_nonneg (by exact_mod_cast (Fintype.card_pos (α := G)))
  have hupper : Real.log (Fintype.card G)-(entropy (markerDecoratedMass p m)-
      entropy (pushMass f (markerDecoratedMass p m))) ≤
        ((Fintype.card V : ℝ)^2/(m : ℝ))*Real.log (Fintype.card G) := by
    apply hbound.2.trans
    convert mul_le_mul_of_nonneg_right hcoll hlog using 1
    congr 1
    apply Finset.sum_congr rfl
    intro w hw
    by_cases hg : Function.Injective (fun v => (w v).2)
    · simp only [if_pos hg]
    · simp only [if_neg hg]
  have hent := markerDecoratedMass_entropy p hs m hm
  constructor <;> linarith [hbound.1,hupper,hent]

end OrbitDecoration
end GaussianWave.BS.Lower
