import BourgadeHuang.CMS.SectorialRows

/-! Symbolic connection entries with retained differential-ideal certificates.
These identities hold on every analytic test, before a solution basis is
constructed. -/
noncomputable section
open scoped BigOperators
open Set
namespace BourgadeHuang.CMS
namespace SquareFreeTerm

/-- The explicit inverse-gap expression represented by a collected matrix entry. -/
def matrixExpression {d : ℕ} : List (SquareFreeTerm d) → Finset (Fin d) → GapExpression d
  | [],_ => .const 0
  | t::ts,T => .add (if t.target=T then t.coefficient else .const 0) (matrixExpression ts T)

@[simp] theorem eval_matrixExpression {d : ℕ} (ts : List (SquareFreeTerm d))
    (T : Finset (Fin d)) (z : Point d) : (matrixExpression ts T).eval z=matrixEntry ts T z := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      simp only [matrixExpression,GapExpression.eval,matrixEntry,List.map_cons,List.sum_cons]
      rw [ih]
      split <;> rfl

end SquareFreeTerm
namespace SectorialData
open GapExpression
variable {d : ℕ} (D : SectorialData d)

/-- A genuine rational expression for every connection coefficient. -/
def connectionCoefficient (i : Fin d) (S T : Finset (Fin d)) : GapExpression d :=
  if i∈S then .add (.const (-(D.phase i)*(if T=S then 1 else 0)))
    (.mul (.const (-1)) (SquareFreeTerm.matrixExpression (D.correctionRow S i) T))
  else .const (if T=insert i S then 1 else 0)

@[simp] theorem eval_connectionCoefficient (i : Fin d) (S T : Finset (Fin d)) (z : Point d) :
    (D.connectionCoefficient i S T).eval z=D.connection i z S T := by
  unfold connectionCoefficient connection
  split <;> simp only [eval,SquareFreeTerm.eval_matrixExpression,neg_one_mul,sub_eq_add_neg]

/-- The complete square-free row, including the explicit phase diagonal. -/
def connectionTerms (i : Fin d) (S : Finset (Fin d)) : List (LeibnizTerm d) :=
  (Finset.univ : Finset (Finset (Fin d))).toList.map
    (fun T => (D.connectionCoefficient i S T,T.toList))

private theorem termSum_map {ι : Type*} (l : List ι)
    (a : ι → GapExpression d) (w : ι → List (Fin d)) (f : Point d → ℂ) (z : Point d) :
    termSum (l.map (fun t => (a t,w t))) f z=
      (l.map (fun t => (a t).eval z*wordDerivative (w t) f z)).sum := by
  induction l with
  | nil => rfl
  | cons t l ih => simp only [List.map_cons,termSum,List.sum_cons,ih]

theorem termSum_connectionTerms (i : Fin d) (S : Finset (Fin d))
    (f : Point d → ℂ) (z : Point d) :
    termSum (D.connectionTerms i S) f z=
      ∑T : Finset (Fin d),D.connection i z S T*squareFreeDerivative T f z := by
  unfold connectionTerms
  rw [termSum_map]
  simp only [eval_connectionCoefficient,squareFreeDerivative]
  rw [← List.sum_toFinset _ (Finset.nodup_toList _),Finset.toList_toFinset]

/-- A certificate for the genuine row reduction, with no solution-existence
or confluence assumption. -/
theorem connectionTerms_certificate (i : Fin d) (S : Finset (Fin d)) :
    D.OperatorCongruent [(.const 1,i::S.toList)] (D.connectionTerms i S) := by
  classical
  by_cases hi : i∈S
  · apply (D.correctionRow_certificate S hi).trans
    apply OperatorCongruent.of_identity
    intro f hf z hz
    rw [D.termSum_connectionTerms]
    simp only [termSum,eval,termSum_scaleTerms,SquareFreeTerm.termSum_asTerms,
      neg_one_mul,← sub_eq_add_neg,squareFreeDerivative,connection,if_pos hi]
    rw [SquareFreeTerm.evalSum_eq_matrix]
    simp only [sub_mul,Finset.sum_sub_distrib]
    congr 1
    simp [ite_mul,Finset.mul_sum,squareFreeDerivative]
  · apply OperatorCongruent.of_identity
    intro f hf z hz
    rw [D.termSum_connectionTerms]
    simp only [termSum,eval,one_mul,add_zero,wordDerivative]
    rw [show wordDerivative S.toList f=squareFreeDerivative S f from rfl,
      coordDeriv_squareFreeDerivative_of_not_mem S hi hf hz]
    simp [connection,hi,ite_mul]

end SectorialData
end BourgadeHuang.CMS
