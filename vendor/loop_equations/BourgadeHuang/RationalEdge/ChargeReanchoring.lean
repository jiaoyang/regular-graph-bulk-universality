import BourgadeHuang.RationalBulk.ChargeReanchoring

/-! Half-plane balance cancels arbitrary moving common bases, including the
edge bases on rays of angle ±π/3. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace BourgadeHuang.RationalEdge
open RationalBulk

theorem chargedObservable_reanchor_halfplanes {d : ℕ}
    (c : Fin d → ℂ) (sigma : Fin d → Bool) (z : Fin d → ℂ)
    (b v : Bool → ℂ) (hzero : ∑ i,c i=0)
    (hsigned : ∑ i,c i*CMS.signValue (sigma i)=0)
    (hzb : ∀ i, SameOpenHalfPlane (z i) (b (sigma i)))
    (hvb : ∀ e, SameOpenHalfPlane (v e) (b e)) (s : AnchoredCountingState) :
    chargedObservable c (fun i => b (sigma i)) s z =
      chargedObservable c (fun i => v (sigma i)) s z := by
  have hzv i := (hzb i).trans (hvb (sigma i)).symm
  rw [chargedObservable_eq_exp _ _ _ hzb, chargedObservable_eq_exp _ _ _ hzv]
  congr 1
  have hp i := nevanlinnaPathPrimitive_cocycle s (hzb i) (hvb (sigma i))
  have he i : c i*nevanlinnaPathPrimitive s (z i) (b (sigma i)) =
      c i*nevanlinnaPathPrimitive s (z i) (v (sigma i)) +
        c i*nevanlinnaPathPrimitive s (v (sigma i)) (b (sigma i)) := by
    rw [hp]
    ring
  simp_rw [he]
  rw [Finset.sum_add_distrib,sum_charge_bool_eq_zero c sigma hzero hsigned
    (fun e => nevanlinnaPathPrimitive s (v e) (b e))]
  simp

theorem expectedChargedObservable_reanchor_halfplanes {d : ℕ}
    (ν : Measure AnchoredCountingState)
    (c : Fin d → ℂ) (sigma : Fin d → Bool) (z : Fin d → ℂ)
    (b v : Bool → ℂ) (hzero : ∑ i,c i=0)
    (hsigned : ∑ i,c i*CMS.signValue (sigma i)=0)
    (hzb : ∀ i, SameOpenHalfPlane (z i) (b (sigma i)))
    (hvb : ∀ e, SameOpenHalfPlane (v e) (b e)) :
    expectedChargedObservable ν c (fun i => b (sigma i)) z =
      expectedChargedObservable ν c (fun i => v (sigma i)) z := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall
    (chargedObservable_reanchor_halfplanes c sigma z b v hzero hsigned hzb hvb)

end BourgadeHuang.RationalEdge
