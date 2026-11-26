import BourgadeHuang.CMS.CanonicalSectorialFamily
import BourgadeHuang.CMS.SectorialConnectionScaling

/-! The canonical normalized family satisfies the full subset-indexed scaled
radial system, including the empty component. -/
noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction BigOperators
namespace BourgadeHuang.CMS
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
variable {d : ℕ}

/-- Reassemble the empty and nonempty blocks into one genuine finite vector. -/
def subsetVector (e : ℂ) (v : NonemptySubset d → ℂ) (S : Finset (Fin d)) : ℂ :=
  if h : S.Nonempty then v ⟨S,h⟩ else e

@[simp] theorem subsetVector_empty (e : ℂ) (v : NonemptySubset d → ℂ) :
    subsetVector e v ∅=e := by simp [subsetVector]

@[simp] theorem subsetVector_nonempty (e : ℂ) (v : NonemptySubset d → ℂ)
    (S : NonemptySubset d) : subsetVector e v S.val=v S := by simp [subsetVector,S.property]

theorem sum_subsets (f : Finset (Fin d) → ℂ) :
    (∑S,f S)=f ∅+∑S : NonemptySubset d,f S.val := by
  classical
  have hs := Finset.sum_subtype (p:=fun S : Finset (Fin d) => S.Nonempty)
    (F:=inferInstanceAs (Fintype (NonemptySubset d))) (Finset.univ.erase ∅) (fun S => by simp [Finset.nonempty_iff_ne_empty]) f
  rw [←hs]
  exact (Finset.add_sum_erase _ _ (Finset.mem_univ ∅)).symm

namespace SectorialData
variable (D : SectorialData d)

/-- The full scaled radial generator on arbitrary finite vectors. -/
def scaledRadialAction (ω z : Point d) (t : ℂ)
    (X : Finset (Fin d) → ℂ) (S : Finset (Fin d)) : ℂ :=
  D.principalDiagonal ω S*X S+
    (∑T : Finset (Fin d),D.principalRemainder ω z t S T*X T)+
    t⁻¹*(∑T : Finset (Fin d),D.radialRemainder ω z t S T*X T)

theorem scaledRadialAction_empty (ω z : Point d) (t : ℂ) (e : ℂ)
    (v : NonemptySubset d → ℂ) :
    D.scaledRadialAction ω z t (subsetVector e v) ∅=
      t⁻¹*∑T : NonemptySubset d,D.radialRemainder ω z t ∅ T.val*v T := by
  classical
  have hn : ∀T,D.principalRemainder ω z t ∅ T=0 := fun T =>
    D.principalRemainder_strict_degree ω z t ∅ T (by simp)
  have h00 : D.radialRemainder ω z t ∅ ∅=0 := by
    simp only [radialRemainder,Finset.card_empty,Nat.cast_zero,ite_self,
      highCoordinate,Finset.not_mem_empty,if_false,Finset.insert_empty,zero_add]
    apply Finset.sum_eq_zero
    intro i hi
    rw [if_neg (Ne.symm (Finset.singleton_ne_empty i))]
  simp only [scaledRadialAction,principalDiagonal,Finset.not_mem_empty,if_false,
    Finset.sum_const_zero,zero_mul,hn,zero_add]
  rw [sum_subsets]
  simp [h00]

theorem scaledRadialAction_nonempty (ω z : Point d) (t : ℂ) (e : ℂ)
    (v : NonemptySubset d → ℂ) (S : NonemptySubset d) :
    D.scaledRadialAction ω z t (subsetVector e v) S.val=
      D.principalDiagonal ω S.val*v S+
        (∑T : NonemptySubset d,D.principalRemainder ω z t S.val T.val*v T)+
        t⁻¹*(D.radialRemainder ω z t S.val ∅*e+
          ∑T : NonemptySubset d,D.radialRemainder ω z t S.val T.val*v T) := by
  rw [scaledRadialAction,sum_subsets,sum_subsets]
  simp only [subsetVector_nonempty,subsetVector_empty,principalRemainder_empty_column,
    zero_mul,zero_add]

end SectorialData
namespace RadialConstructionData
variable (P : RadialConstructionData d)

/-- The actual scaled full vector, extended constantly before the tail endpoint. -/
def fullFamily (z : Point d) (t : ℝ) : Finset (Fin d) → ℂ :=
  subsetVector (tailExtension (P.emptyFamily z) t ())
    (tailExtension (P.nonemptyFamily z) t)

@[simp] theorem fullFamily_empty (z : Point d) (t : ℝ) :
    P.fullFamily z t ∅=tailExtension (P.emptyFamily z) t () := by simp [fullFamily]

@[simp] theorem fullFamily_nonempty (z : Point d) (t : ℝ) (S : NonemptySubset d) :
    P.fullFamily z t S.val=tailExtension (P.nonemptyFamily z) t S := by simp [fullFamily]

/-- Every full component obeys the actual scaled rational radial equation. -/
theorem hasDerivAt_fullFamily {z : Point d} (hz : z∈OrderedGapDomain d P.radius)
    (t : Tail P.radius) (ht : P.radius<t.val) (S : Finset (Fin d)) :
    HasDerivAt (fun s => P.fullFamily z s S)
      (P.D.scaledRadialAction (shiftedDirection P.sign)
        (sectorialRay P.sign z P.radius t) (t:ℝ) (P.fullFamily z t) S) t.val := by
  have hf := (P.localFamily_spec z hz).2.2.self_of_nhds
  have hd := (P.localFamily z hz).normalized_component_equations P.radius_pos P.gap_pos P.lam P.lam_gap
    P.D (shiftedDirection P.sign) P.sign hf.1 hf.2 t ht
  have h0 : P.emptyFamily z=(P.localFamily z hz).normalizedEmpty
      P.radius_pos P.gap_pos P.lam P.lam_gap z := by simp [emptyFamily,hz]
  have h1 : P.nonemptyFamily z=(P.localFamily z hz).normalizedNonempty
      P.radius_pos P.gap_pos P.lam P.lam_gap z := by simp [nonemptyFamily,weightedFamily,hz,RadialOperatorFamily.normalizedNonempty]
  have hval : P.fullFamily z t=subsetVector (P.emptyFamily z t ()) (P.nonemptyFamily z t) := by
    simp only [fullFamily,tailExtension_apply]
  by_cases hS : S.Nonempty
  · have hh := hd.2 ⟨S,hS⟩
    rw [P.lam_eq] at hh
    rw [hval,P.D.scaledRadialAction_nonempty _ _ _ _ _ ⟨S,hS⟩]
    simpa only [fullFamily,subsetVector,dif_pos hS,
      h0,h1,Complex.real_smul,Complex.ofReal_inv] using hh
  · have hSe : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    simpa only [fullFamily_empty,hval,P.D.scaledRadialAction_empty,
      h0,h1,Complex.real_smul,Complex.ofReal_inv] using hd.1

end RadialConstructionData
end BourgadeHuang.CMS
