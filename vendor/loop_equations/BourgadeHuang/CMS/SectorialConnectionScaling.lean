import BourgadeHuang.CMS.SectorialRadialSystem

/-! Algebraic equivalence of the scaled radial system and the actual
square-free connection, for arbitrary vectors rather than assumed jets. -/
noncomputable section
open scoped BigOperators
namespace BourgadeHuang.CMS
set_option maxHeartbeats 800000
namespace SquareFreeTerm

/-- Homogeneous splitting of a correction row acts on every finite vector. -/
theorem scaled_matrixEntry_split {d n : ℕ} (ts : List (SquareFreeTerm d))
    (h : ∀a∈ts,a.IsCorrection n) (T : Finset (Fin d)) (z : Point d)
    {t : ℂ} (ht : t≠0) :
    t^n*matrixEntry ts T z=
      homogeneousEntry ts n T z t*t^T.card+
        t⁻¹*(homogeneousEntry ts (n+1) T z t*t^T.card) := by
  classical
  induction ts with
  | nil => simp [matrixEntry,homogeneousEntry]
  | cons a ts ih =>
    have hh := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    change t^n*((if a.target=T then a.coefficient.eval z else 0)+matrixEntry ts T z)=
      ((if a.target=T ∧ a.weight+a.target.card=n then a.scaledCoefficient z t else 0)+
        homogeneousEntry ts n T z t)*t^T.card+
      t⁻¹*(((if a.target=T ∧ a.weight+a.target.card=n+1 then a.scaledCoefficient z t else 0)+
        homogeneousEntry ts (n+1) T z t)*t^T.card)
    by_cases ha : a.target=T
    · have hs := a.scaled_term_split (h a (List.mem_cons_self ..)) z ht 1
      simp only [mul_one] at hs
      rw [ha] at hs
      simp only [ha,true_and,if_true]
      have he1 : (if a.weight+T.card=n then a.scaledCoefficient z t else 0)*t^T.card=
        if a.weight+T.card=n then a.scaledCoefficient z t*t^T.card else 0 := by split_ifs <;> simp
      have he2 : (if a.weight+T.card=n+1 then a.scaledCoefficient z t else 0)*t^T.card=
        if a.weight+T.card=n+1 then a.scaledCoefficient z t*t^T.card else 0 := by split_ifs <;> simp
      simp only [mul_add,add_mul,he1,he2]
      linear_combination hs+hh
    · simp only [ha,false_and,if_false,zero_add,mul_zero]
      exact hh

end SquareFreeTerm
namespace SectorialData
variable {d : ℕ} (D : SectorialData d)

/-- One row of the connection is conjugated by the exact degree weights. -/
theorem scaled_connection_entry (ω z : Point d) (S T : Finset (Fin d)) (i : Fin d)
    {t : ℂ} (ht : t≠0) :
    t^S.card*ω i*D.connection i z S T=
      (if i∈S then -(ω i*D.phase i) else 0)*(if T=S then t^T.card else 0)+
        D.lowCoordinate ω z t S T i*t^T.card+
        t⁻¹*(D.highCoordinate ω z t S T i*t^T.card) := by
  classical
  by_cases hi : i∈S
  · have hh := SquareFreeTerm.scaled_matrixEntry_split (D.correctionRow S i)
      (D.correctionRow_spec S i) T z ht
    simp only [connection,lowCoordinate,highCoordinate,if_pos hi]
    by_cases hT : T=S
    · subst T
      simp only [if_true]
      linear_combination -(ω i)*hh
    · simp only [if_neg hT,mul_zero,zero_mul,zero_sub,zero_add]
      linear_combination -(ω i)*hh
  · simp only [connection,lowCoordinate,highCoordinate,if_neg hi,zero_mul,zero_add]
    by_cases hT : T=insert i S
    · subst T
      simp only [if_true,mul_one,Finset.card_insert_of_not_mem hi,pow_succ]
      field_simp
      ring
    · simp [hT]

/-- Full degree-weight conjugation, including the derivative of the weights.
This is a finite matrix identity and makes no PDE-solution assumption. -/
theorem scaled_connection_action (ω z : Point d) (S : Finset (Fin d))
    (X : Finset (Fin d) → ℂ) {t : ℂ} (ht : t≠0) :
    (S.card:ℂ)/t*(t^S.card*X S)+t^S.card*
        (∑i,ω i*∑T : Finset (Fin d),D.connection i z S T*X T)=
      D.principalDiagonal ω S*(t^S.card*X S)+
        (∑T : Finset (Fin d),D.principalRemainder ω z t S T*(t^T.card*X T))+
        t⁻¹*(∑T : Finset (Fin d),D.radialRemainder ω z t S T*(t^T.card*X T)) := by
  classical
  let Y := fun T => t^T.card*X T
  have hh : ∀i,t^S.card*(ω i*∑T : Finset (Fin d),D.connection i z S T*X T)=
      (if i∈S then -(ω i*D.phase i) else 0)*Y S+
      (∑T : Finset (Fin d),D.lowCoordinate ω z t S T i*Y T)+
      t⁻¹*(∑T : Finset (Fin d),D.highCoordinate ω z t S T i*Y T) := by
    intro i
    rw [Finset.mul_sum,Finset.mul_sum]
    have he : ∀T,t^S.card*(ω i*(D.connection i z S T*X T))=
        (if i∈S then -(ω i*D.phase i) else 0)*
            (if T=S then t^T.card*X T else 0)+
          D.lowCoordinate ω z t S T i*Y T+
          t⁻¹*(D.highCoordinate ω z t S T i*Y T) := by
      intro T
      have hc := congrArg (fun a : ℂ => a*X T) (D.scaled_connection_entry ω z S T i ht)
      dsimp only [Y]
      by_cases hT : T=S
      · simpa only [if_pos hT,add_mul,mul_assoc] using hc
      · simpa only [if_neg hT,mul_zero,zero_mul,zero_add,add_mul,mul_assoc] using hc
    simp_rw [he]
    rw [Finset.sum_add_distrib,Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true,Y]
  change (S.card:ℂ)/t*Y S+t^S.card*(∑i,ω i*∑T : Finset (Fin d),D.connection i z S T*X T)=_
  rw [Finset.mul_sum]
  simp_rw [hh]
  simp only [principalDiagonal,principalRemainder,radialRemainder,Finset.sum_add_distrib,
    Finset.sum_mul,add_mul,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rw [Finset.sum_comm (f:=fun T i => D.lowCoordinate ω z t S T i*Y T),
    Finset.sum_comm (f:=fun T i => D.highCoordinate ω z t S T i*Y T)]
  rw [←Finset.mul_sum]
  ring

end SectorialData
end BourgadeHuang.CMS
