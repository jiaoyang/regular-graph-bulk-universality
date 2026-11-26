import BourgadeHuang.RationalChargeGeometry

/-! Rational neutrality is realized by actual finite same-half-plane blocks:
`p` numerator coordinates and `q` denominator coordinates per block. -/
noncomputable section
open scoped BigOperators
namespace BourgadeHuang.RationalBulk

def repeatedSigns {k : ℕ} (r : ℕ) (eta : Fin k → CMS.Sign) : Fin (k*r) → CMS.Sign :=
  fun i=>eta (finProdFinEquiv.symm i).1

theorem signCount_repeated {k : ℕ} (r : ℕ) (eta : Fin k → CMS.Sign) (b : CMS.Sign) :
    CMS.signCount (repeatedSigns r eta) b = r * CMS.signCount eta b := by
  classical
  have hs : (∑i : Fin (k*r), if repeatedSigns r eta i=b then (1:ℕ) else 0) =
      ∑ij : Fin k × Fin r, if eta ij.1=b then (1:ℕ) else 0 := by
    symm
    simpa only [repeatedSigns,Equiv.symm_apply_apply] using
      (Equiv.sum_comp (finProdFinEquiv : Fin k × Fin r ≃ Fin (k*r))
        (fun i=>if repeatedSigns r eta i=b then (1:ℕ) else 0))
  rw [Fintype.sum_prod_type] at hs
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hpoint (i : Fin k) : (∑ _j : Fin r, if eta i=b then (1:ℕ) else 0) = r*(if eta i=b then 1 else 0) := by simp
  simp only [hpoint] at hs
  rw [← Finset.mul_sum] at hs
  simpa [CMS.signCount] using hs

/-- Rational charge neutrality gives the exact cardinality of positive
numerator signs from that of positive denominator signs. -/
theorem balanced_count_of_rational {beta : ℝ} {p q : ℕ}
    (hq : 0<q) (hrat : beta*(q:ℝ)=2*(p:ℝ)) {n m kp : ℕ}
    (epsilon : Fin n → CMS.Sign) (eta : Fin m → CMS.Sign)
    (hden : CMS.signCount eta true=kp*q)
    (hbal : beta*(CMS.signCount eta true:ℝ)=2*(CMS.signCount epsilon true:ℝ)) :
    CMS.signCount epsilon true=kp*p := by
  have h : (CMS.signCount epsilon true:ℝ)=(kp*p:ℕ) := by
    rw [hden] at hbal
    push_cast at hbal ⊢
    nlinarith
  exact_mod_cast h

/-- Any numerator sign pattern with the correct multiplicities is an actual
permutation of the `p`-fold block signs. -/
theorem exists_numerator_blockMatching {k p : ℕ}
    (epsilon : Fin (k*p) → CMS.Sign) (eta : Fin k → CMS.Sign)
    (h : CMS.signCount epsilon true=p*CMS.signCount eta true) :
    ∃e : Equiv.Perm (Fin (k*p)),∀i,repeatedSigns p eta (e i)=epsilon i := by
  apply OrthogonalCMS.exists_signMatching epsilon (repeatedSigns p eta)
  rw [signCount_repeated]
  exact h

/-- Each rational sign-balanced configuration can be regrouped into same-sign
neutral blocks without changing the coordinates themselves. -/
theorem exists_rational_blockMatching {beta : ℝ} {p q k : ℕ}
    (hq : 0<q) (hrat : beta*(q:ℝ)=2*(p:ℝ))
    (epsilon : Fin (k*p) → CMS.Sign) (eta : Fin k → CMS.Sign)
    (hbal : beta*(CMS.signCount (repeatedSigns q eta) true:ℝ)=
      2*(CMS.signCount epsilon true:ℝ)) :
    ∃e : Equiv.Perm (Fin (k*p)),∀i,repeatedSigns p eta (e i)=epsilon i := by
  apply exists_numerator_blockMatching epsilon eta
  have he := balanced_count_of_rational hq hrat epsilon (repeatedSigns q eta)
    (kp:=CMS.signCount eta true) (by rw [signCount_repeated]; exact Nat.mul_comm _ _) hbal
  simpa [Nat.mul_comm] using he

end BourgadeHuang.RationalBulk
