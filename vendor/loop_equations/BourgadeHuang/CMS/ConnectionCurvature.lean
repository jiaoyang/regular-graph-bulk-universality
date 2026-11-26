import BourgadeHuang.CMS.SquareFreeConfluence
import BourgadeHuang.CMS.SectorialConnectionRows

/-! Zero curvature of the actual square-free connection, derived from the
certified differential ideal and its confluent monic reduction. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace BourgadeHuang.CMS
open GapExpression
variable {d : ℕ}

theorem wordIndex_toList_injective (S T : Finset (Fin d)) :
    wordIndex S.toList=wordIndex T.toList ↔ S=T := by
  constructor
  · intro h
    have hp := (wordIndex_eq_iff_perm _ _).mp h
    simpa using List.toFinset_eq_of_perm _ _ hp
  · rintro rfl
    rfl

namespace SectorialData
variable (D : SectorialData d)

theorem connectionTerms_squareFree (i : Fin d) (S : Finset (Fin d)) :
    ∀e u,(e,u)∈D.connectionTerms i S→u.Nodup := by
  intro e u hu
  obtain ⟨T,hT,he⟩ := List.mem_map.mp hu
  exact (Prod.mk.inj he).2 ▸ Finset.nodup_toList T

/-- Differentiating one connection row and reducing the differentiated jets. -/
def connectionSecondTerms (i j : Fin d) (S : Finset (Fin d)) : List (LeibnizTerm d) :=
  (Finset.univ : Finset (Finset (Fin d))).toList.flatMap (fun U=>
    [((D.connectionCoefficient j S U).derivative i,U.toList)]++
      scaleTerms (D.connectionCoefficient j S U) (D.connectionTerms i U))

private theorem connection_step_reduction (i : Fin d) (a : Finset (Fin d) → GapExpression d)
    (l : List (Finset (Fin d))) :
    D.OperatorCongruent (stepTerms i (l.map (fun U=>(a U,U.toList))))
      (l.flatMap (fun U=>[((a U).derivative i,U.toList)]++scaleTerms (a U) (D.connectionTerms i U))) := by
  induction l with
  | nil=>exact OperatorCongruent.refl _
  | cons U l ih=>
    have hscaled : D.OperatorCongruent [(a U,i::U.toList)] (scaleTerms (a U) (D.connectionTerms i U)) := by
      apply OperatorCongruent.trans (us:=scaleTerms (a U) [(.const 1,i::U.toList)])
      · apply OperatorCongruent.of_identity
        intro f hf z hz
        simp [termSum,termSum_scaleTerms,eval]
      · exact (D.connectionTerms_certificate i U).scale (a U)
    exact ((OperatorCongruent.refl [((a U).derivative i,U.toList)]).append hscaled).append ih

theorem connectionSecondTerms_certificate (i j : Fin d) (S : Finset (Fin d)) :
    D.OperatorCongruent [(.const 1,i::j::S.toList)] (D.connectionSecondTerms i j S) := by
  apply OperatorCongruent.trans (us:=stepTerms i [(.const 1,j::S.toList)])
  · apply OperatorCongruent.of_identity
    intro f hf z hz
    simp [stepTerms,termSum,derivative,eval]
  · exact ((D.connectionTerms_certificate j S).step i).trans
      (D.connection_step_reduction i (D.connectionCoefficient j S) _)

theorem connectionSecondTerms_squareFree (i j : Fin d) (S : Finset (Fin d)) :
    ∀e u,(e,u)∈D.connectionSecondTerms i j S→u.Nodup := by
  intro e u hu
  obtain ⟨U,hU,hu⟩ := List.mem_flatMap.mp hu
  rcases List.mem_append.mp hu with hu|hu
  · have he := List.mem_singleton.mp hu
    exact (Prod.mk.inj he).2 ▸ Finset.nodup_toList U
  · obtain ⟨t,ht,he⟩ := List.mem_map.mp hu
    exact (Prod.mk.inj he).2 ▸ D.connectionTerms_squareFree i U t.1 t.2 ht

theorem coeff_connectionTerms (i : Fin d) (S T : Finset (Fin d)) (z : Point d) :
    MvPolynomial.coeff (wordIndex T.toList) (operatorSymbol (D.connectionTerms i S) z)=D.connection i z S T := by
  classical
  rw [coeff_operatorSymbol]
  simp only [connectionTerms,List.map_map,Function.comp_def,wordIndex_toList_injective,eval_connectionCoefficient]
  rw [←List.sum_toFinset _ (Finset.nodup_toList _),Finset.toList_toFinset]
  simp

private theorem coeff_connectionSecond_list (i j : Fin d) (S T : Finset (Fin d))
    (l : List (Finset (Fin d))) (z : Point d) :
    MvPolynomial.coeff (wordIndex T.toList) (operatorSymbol (l.flatMap (fun U=>
      [((D.connectionCoefficient j S U).derivative i,U.toList)]++
        scaleTerms (D.connectionCoefficient j S U) (D.connectionTerms i U))) z)=
    (l.map (fun U=>(if U=T then ((D.connectionCoefficient j S U).derivative i).eval z else 0)+
      D.connection j z S U*D.connection i z U T)).sum := by
  induction l with
  | nil=>simp [operatorSymbol]
  | cons U l ih=>
    simp only [List.flatMap_cons,operatorSymbol_append,MvPolynomial.coeff_add,operatorSymbol_scale,
      MvPolynomial.coeff_C_mul,D.coeff_connectionTerms,eval_connectionCoefficient,
      List.map_cons,List.sum_cons,ih]
    congr 1
    rw [coeff_operatorSymbol]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,wordIndex_toList_injective]

theorem coeff_connectionSecondTerms (i j : Fin d) (S T : Finset (Fin d))
    {z : Point d} (hz : z∈OrderedDomain d) :
    MvPolynomial.coeff (wordIndex T.toList) (operatorSymbol (D.connectionSecondTerms i j S) z)=
      coordDeriv i (fun w=>D.connection j w S T) z+
        ∑U : Finset (Fin d),D.connection j z S U*D.connection i z U T := by
  rw [connectionSecondTerms,D.coeff_connectionSecond_list]
  rw [←List.sum_toFinset _ (Finset.nodup_toList _),Finset.toList_toFinset,Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_pos]
  rw [←GapExpression.coordDeriv_eval _ (orderedDomain_collisionFree hz)]
  congr 1
  congr 1
  funext w
  exact D.eval_connectionCoefficient j S T w

/-- The actual induced connection is flat for the physical charges.
No PDE solution or invertible fundamental matrix is assumed. -/
theorem general_connection_flat (β : ℂ) (c : Fin d → ℂ) (σ : Fin d → Sign)
    (hβ : β≠0) (hc : ∀i,c i= -1 ∨ c i=β/2)
    (i j : Fin d) (S T : Finset (Fin d)) {z : Point d} (hz : z∈OrderedDomain d) :
    coordDeriv i (fun w=>(general β c σ).connection j w S T) z-
      coordDeriv j (fun w=>(general β c σ).connection i w S T) z+
      (∑U : Finset (Fin d),(general β c σ).connection j z S U*(general β c σ).connection i z U T)-
      (∑U : Finset (Fin d),(general β c σ).connection i z S U*(general β c σ).connection j z U T)=0 := by
  let D := general β c σ
  have hperm : D.OperatorCongruent [(.const 1,i::j::S.toList)] [(.const 1,j::i::S.toList)] :=
    OperatorCongruent.word_perm (List.Perm.swap _ _ _) (.const 1)
  have he := ((D.connectionSecondTerms_certificate i j S).symm.trans
    (hperm.trans (D.connectionSecondTerms_certificate j i S))).squareFree_symbol β c σ hβ hc
    (D.connectionSecondTerms_squareFree i j S) (D.connectionSecondTerms_squareFree j i S) hz
  have hh := congrArg (MvPolynomial.coeff (wordIndex T.toList)) he
  rw [D.coeff_connectionSecondTerms i j S T hz,D.coeff_connectionSecondTerms j i S T hz] at hh
  change _-_+_-_=0
  linear_combination hh

end SectorialData
end BourgadeHuang.CMS
