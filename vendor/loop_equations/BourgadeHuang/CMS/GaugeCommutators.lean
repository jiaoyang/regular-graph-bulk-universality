import BourgadeHuang.CMS.CommutatorAssembly
import BourgadeHuang.CMS.GeneralBranches

/-! Compatibility is preserved by the actual analytic branch conjugation. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace BourgadeHuang.CMS
variable {d : ℕ} {f g L W : Point d → ℂ} {z : Point d}

theorem secondPartial_congr_nhds (hfg : f =ᶠ[𝓝 z] g) (i : Fin d) :
    secondPartial i f z = secondPartial i g z :=
  coordDeriv_congr_nhds (hfg.eventuallyEq_nhds.mono
    (fun _ hw => coordDeriv_congr_nhds hw i)) i

theorem deformedOperator_congr_nhds (β : ℂ) (c : Fin d → ℂ) (i : Fin d)
    (hfg : f =ᶠ[𝓝 z] g) : deformedOperator β c i f z = deformedOperator β c i g z := by
  simp only [deformedOperator,secondPartial_congr_nhds hfg,
    coordDeriv_congr_nhds hfg,hfg.eq_of_nhds]

theorem conjugatedDeformedOperator_congr_nhds (β : ℂ) (c : Fin d → ℂ)
    (L : Point d → ℂ) (i : Fin d) (hfg : f =ᶠ[𝓝 z] g) :
    conjugatedDeformedOperator β c L i f z = conjugatedDeformedOperator β c L i g z := by
  simp only [conjugatedDeformedOperator,secondPartial_congr_nhds hfg,
    coordDeriv_congr_nhds hfg,hfg.eq_of_nhds]

theorem analyticAt_deformedOperator (β : ℂ) (c : Fin d → ℂ) (i : Fin d)
    (hf : AnalyticAt ℂ f z) (hz : CollisionFree z) :
    AnalyticAt ℂ (deformedOperator β c i f) z := by
  have he : deformedOperator β c i f = fun w =>
      ∑a : Option (Fin d),cmsAtomWeight β a*cmsAtom c i a f w := by
    funext w
    exact deformedOperator_eq_atom_sum β c i f w
  rw [he]
  exact Finset.analyticAt_sum _ (fun a _ =>
    analyticAt_const.mul (analyticAt_cmsAtom c i a hf hz))

theorem analyticAt_conjugatedDeformedOperator (β : ℂ) (c : Fin d → ℂ) (i : Fin d)
    (hL : AnalyticAt ℂ L z) (hW : AnalyticAt ℂ W z) (hz : CollisionFree z) :
    AnalyticAt ℂ (conjugatedDeformedOperator β c L i W) z := by
  have hdl k := analyticAt_coordDeriv hL k
  have hdw k := analyticAt_coordDeriv hW k
  have hddl : AnalyticAt ℂ (secondPartial i L) z := analyticAt_coordDeriv (hdl i) i
  have hddw : AnalyticAt ℂ (secondPartial i W) z := analyticAt_coordDeriv (hdw i) i
  unfold conjugatedDeformedOperator
  apply AnalyticAt.add
  · exact (hddw.add ((analyticAt_const.mul (hdl i)).mul (hdw i))).add
      (((hddl.add ((hdl i).pow 2)).add analyticAt_const).mul hW)
  · apply AnalyticAt.mul analyticAt_const
    apply Finset.analyticAt_sum
    intro j hj
    apply AnalyticAt.div
    · exact ((analyticAt_const.mul (hdw i)).sub (analyticAt_const.mul (hdw j))).add
        (((analyticAt_const.mul (hdl i)).sub (analyticAt_const.mul (hdl j))).mul hW)
    · exact ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt z).sub
        ((ContinuousLinearMap.proj (R := ℂ) j).analyticAt z)
    · exact hz.sub_ne_zero (Finset.mem_erase.mp hj).1.symm

/-- Compatibility of the true conjugated operators, for any analytic phase. -/
theorem conjugatedDeformedOperator_commutator (β : ℂ) (c : Fin d → ℂ) (i j : Fin d)
    (hL : AnalyticAt ℂ L z) (hW : AnalyticAt ℂ W z) (hz : CollisionFree z)
    (hij : i≠j) (hβ : β≠0) (hc : ∀k,c k = -1 ∨ c k = β/2) :
    conjugatedDeformedOperator β c L i (conjugatedDeformedOperator β c L j W) z-
      conjugatedDeformedOperator β c L j (conjugatedDeformedOperator β c L i W) z =
      (4/β)/(z i-z j)^2*
        (c i^2*conjugatedDeformedOperator β c L j W z-
         c j^2*conjugatedDeformedOperator β c L i W z) := by
  let E : Point d → ℂ := fun w => Complex.exp (L w)*W w
  have hE : AnalyticAt ℂ E z := hL.cexp.mul hW
  have he k : (fun w => Complex.exp (L w)*conjugatedDeformedOperator β c L k W w) =ᶠ[𝓝 z]
      deformedOperator β c k E := by
    filter_upwards [hL.eventually_analyticAt,hW.eventually_analyticAt] with w hwl hww
    exact (deformedOperator_exp_mul β c hwl hww k).symm
  have hcomp a b : deformedOperator β c a (deformedOperator β c b E) z =
      Complex.exp (L z)*conjugatedDeformedOperator β c L a
        (conjugatedDeformedOperator β c L b W) z := by
    rw [deformedOperator_congr_nhds β c a (he b).symm]
    exact deformedOperator_exp_mul β c hL
      (analyticAt_conjugatedDeformedOperator β c b hL hW hz) a
  have h := deformedOperator_commutator β c i j hE hz hij hβ hc
  rw [hcomp i j,hcomp j i] at h
  have hez k : deformedOperator β c k E z =
      Complex.exp (L z)*conjugatedDeformedOperator β c L k W z :=
    deformedOperator_exp_mul β c hL hW k
  rw [hez i,hez j] at h
  apply mul_left_cancel₀ (Complex.exp_ne_zero (L z))
  linear_combination h

theorem analyticAt_sectorialOperator (β : ℂ) (c : Fin d → ℂ) (σ : Fin d → Sign)
    (i : Fin d) (hW : AnalyticAt ℂ W z) (hz : z∈OrderedDomain d) :
    AnalyticAt ℂ (sectorialOperator β c σ i W) z := by
  apply (analyticAt_conjugatedDeformedOperator β c i
    (analyticAt_generalBranchLog β c σ hz) hW (orderedDomain_collisionFree hz)).congr
  filter_upwards [(orderedDomain_isOpen d).mem_nhds hz] with w hw
  exact conjugatedDeformedOperator_generalBranchLog β c σ hw i W

/-- The branch-reduced sectorial system has the same compatibility identity,
with every derivative interpreted as an actual analytic derivative. -/
theorem sectorialOperator_commutator (β : ℂ) (c : Fin d → ℂ) (σ : Fin d → Sign)
    (i j : Fin d) (hW : AnalyticAt ℂ W z) (hz : z∈OrderedDomain d)
    (hij : i≠j) (hβ : β≠0) (hc : ∀k,c k = -1 ∨ c k = β/2) :
    sectorialOperator β c σ i (sectorialOperator β c σ j W) z-
      sectorialOperator β c σ j (sectorialOperator β c σ i W) z =
      (4/β)/(z i-z j)^2*
        (c i^2*sectorialOperator β c σ j W z-c j^2*sectorialOperator β c σ i W z) := by
  let L := generalBranchLog β c σ
  have he k : conjugatedDeformedOperator β c L k W =ᶠ[𝓝 z] sectorialOperator β c σ k W := by
    filter_upwards [(orderedDomain_isOpen d).mem_nhds hz] with w hw
    exact conjugatedDeformedOperator_generalBranchLog β c σ hw k W
  have hcomp a b : conjugatedDeformedOperator β c L a
      (conjugatedDeformedOperator β c L b W) z =
      sectorialOperator β c σ a (sectorialOperator β c σ b W) z := by
    rw [conjugatedDeformedOperator_congr_nhds β c L a (he b)]
    exact conjugatedDeformedOperator_generalBranchLog β c σ hz a _
  have h := conjugatedDeformedOperator_commutator β c i j
    (analyticAt_generalBranchLog β c σ hz) hW (orderedDomain_collisionFree hz) hij hβ hc
  change conjugatedDeformedOperator β c L i (conjugatedDeformedOperator β c L j W) z-
    conjugatedDeformedOperator β c L j (conjugatedDeformedOperator β c L i W) z = _ at h
  rw [hcomp i j,hcomp j i,(he i).eq_of_nhds,(he j).eq_of_nhds] at h
  exact h

end BourgadeHuang.CMS
