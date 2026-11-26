import BourgadeHuang.RationalBulk.ChargedObservables
import BourgadeHuang.RationalChargeGeometry
import BourgadeHuang.OrthogonalMixedNormalization

/-! Exact cancellation of the two half-plane anchors for neutral charged
observables. These are path primitive identities before expectation. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace BourgadeHuang.RationalBulk

/-- A function of one sign has only constant and signed components. -/
theorem sum_charge_bool_eq_zero {d : ℕ} (c : Fin d → ℂ) (sigma : Fin d → Bool)
    (hzero : ∑i,c i=0) (hsigned : ∑i,c i*CMS.signValue (sigma i)=0) (f : Bool → ℂ) :
    (∑i,c i*f (sigma i))=0 := by
  have hpoint i : c i*f (sigma i)=
      ((f true+f false)/2)*c i+((f true-f false)/2)*(c i*CMS.signValue (sigma i)) := by
    cases hs : sigma i <;> simp [hs,CMS.signValue] <;> ring
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,hzero,hsigned]
  simp

def signAnchor (sigma : Bool) (height : ℝ) : ℂ :=
  CMS.signValue sigma * Complex.I * (height:ℂ)

@[simp] theorem reflect_signAnchor_im (sigma : Bool) (height : ℝ) :
    (reflectComplex sigma (signAnchor sigma height)).im=height := by
  cases sigma <;> simp [signAnchor,CMS.signValue,reflectComplex]

theorem signAnchor_sameHalf (sigma : Bool) {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    SameOpenHalfPlane (signAnchor sigma a) (signAnchor sigma b) := by
  apply sameOpenHalfPlane_of_reflect_pos sigma
  · simpa using ha
  · simpa using hb

/-- Both half-plane charge balances remove a common moving anchor exactly. -/
theorem chargedObservable_reanchor_signs {d : ℕ}
    (c : Fin d → ℂ) (sigma : Fin d → Bool) (z : Fin d → ℂ)
    (hzero : ∑i,c i=0) (hsigned : ∑i,c i*CMS.signValue (sigma i)=0)
    {a b : ℝ} (ha : 0<a) (hb : 0<b)
    (hz : ∀i,0<(reflectComplex (sigma i) (z i)).im) (s : AnchoredCountingState) :
    chargedObservable c (fun i=>signAnchor (sigma i) a) s z =
      chargedObservable c (fun i=>signAnchor (sigma i) b) s z := by
  have hza i : SameOpenHalfPlane (z i) (signAnchor (sigma i) a) :=
    sameOpenHalfPlane_of_reflect_pos (sigma i) (hz i) (by simpa using ha)
  have hzb i : SameOpenHalfPlane (z i) (signAnchor (sigma i) b) :=
    sameOpenHalfPlane_of_reflect_pos (sigma i) (hz i) (by simpa using hb)
  rw [chargedObservable_eq_exp _ _ _ hza,chargedObservable_eq_exp _ _ _ hzb]
  congr 1
  have hp i := nevanlinnaPathPrimitive_cocycle s (hza i) (signAnchor_sameHalf (sigma i) hb ha)
  have he i : c i*nevanlinnaPathPrimitive s (z i) (signAnchor (sigma i) a)=
      c i*nevanlinnaPathPrimitive s (z i) (signAnchor (sigma i) b)+
      c i*nevanlinnaPathPrimitive s (signAnchor (sigma i) b) (signAnchor (sigma i) a) := by
    rw [hp]
    ring
  simp_rw [he]
  rw [Finset.sum_add_distrib,sum_charge_bool_eq_zero c sigma hzero hsigned
    (fun t=>nevanlinnaPathPrimitive s (signAnchor t b) (signAnchor t a))]
  simp

/-- The deterministic phase has no anchor contribution for neutral charges. -/
theorem signedPhase_sum_eq_generalRayPhase {d : ℕ}
    (c : Fin d → ℂ) (sigma : Fin d → Bool) (z : Fin d → ℂ)
    (hzero : ∑i,c i=0) (height : ℝ) :
    (∑i,c i*signedRatioPhase (sigma i) (z i) (signAnchor (sigma i) height))=
      CMS.generalRayPhase c sigma z := by
  have hp i : c i*signedRatioPhase (sigma i) (z i) (signAnchor (sigma i) height)=
      Complex.I*(c i*CMS.signValue (sigma i)*z i)+c i*(height:ℂ) := by
    cases hs : sigma i <;> simp [signedRatioPhase,signAnchor,CMS.signValue,hs] <;>
      ring_nf <;> simp [Complex.I_sq]
  simp_rw [hp]
  rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul,hzero,zero_mul,add_zero]
  rfl

end BourgadeHuang.RationalBulk
