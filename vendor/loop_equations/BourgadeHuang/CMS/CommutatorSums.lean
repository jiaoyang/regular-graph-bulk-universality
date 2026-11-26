import BourgadeHuang.CMS.CommutatorCalculus

/-! Finite linear-combination rules and a genuine expansion of CMS commutators. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace BourgadeHuang.CMS
variable {d : ℕ} {z : Point d}

theorem coordDeriv_finset_sum_analytic {ι : Type*} (s : Finset ι)
    (F : ι → Point d → ℂ) (hF : ∀a∈s,AnalyticAt ℂ (F a) z) (i : Fin d) :
    coordDeriv i (fun w => ∑a∈s,F a w) z = ∑a∈s,coordDeriv i (F a) z := by
  have h (a) (ha : a∈s) : HasDerivAt (fun w => F a (Function.update z i w))
      (coordDeriv i (F a) z) (z i) := by
    rw [coordDeriv_eq_fderiv (hF a ha).differentiableAt]
    exact (hF a ha).differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq (z i)
      (hasDerivAt_update z i (z i)) (Function.update_eq_self i z).symm
  exact (HasDerivAt.sum h).deriv

theorem secondPartial_finset_sum_analytic {ι : Type*} (s : Finset ι)
    (F : ι → Point d → ℂ) (hF : ∀a∈s,AnalyticAt ℂ (F a) z) (i : Fin d) :
    secondPartial i (fun w => ∑a∈s,F a w) z = ∑a∈s,secondPartial i (F a) z := by
  have he : coordDeriv i (fun w => ∑a∈s,F a w) =ᶠ[𝓝 z]
      (fun w => ∑a∈s,coordDeriv i (F a) w) := by
    have hh : ∀ᶠ w in 𝓝 z,∀a∈s,AnalyticAt ℂ (F a) w :=
      (s.eventually_all).mpr (fun a ha => (hF a ha).eventually_analyticAt)
    filter_upwards [hh] with w hw
    exact coordDeriv_finset_sum_analytic s F hw i
  unfold secondPartial
  rw [coordDeriv_congr_nhds he]
  exact coordDeriv_finset_sum_analytic s (fun a => coordDeriv i (F a))
    (fun a ha => analyticAt_coordDeriv (hF a ha) i) i

theorem pairOperator_linear_combination {ι : Type*} (s : Finset ι)
    (F : ι → Point d → ℂ) (hF : ∀a∈s,AnalyticAt ℂ (F a) z)
    (a : ι → ℂ) (c : Fin d → ℂ) (i j : Fin d) :
    pairOperator c i j (fun w => ∑r∈s,a r*F r w) z = ∑r∈s,a r*pairOperator c i j (F r) z := by
  simp only [pairOperator,chargeDirection,
    coordDeriv_finset_sum_analytic s (fun r w => a r*F r w)
      (fun r hr => analyticAt_const.mul (hF r hr)),
    coordDeriv_const_mul_analytic (hF _ _)]
  simp only [Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  rw [coordDeriv_const_mul_analytic (hF r hr),coordDeriv_const_mul_analytic (hF r hr)]
  ring

theorem freeOperator_linear_combination {ι : Type*} (s : Finset ι)
    (F : ι → Point d → ℂ) (hF : ∀a∈s,AnalyticAt ℂ (F a) z)
    (a : ι → ℂ) (c : Fin d → ℂ) (i : Fin d) :
    freeOperator c i (fun w => ∑r∈s,a r*F r w) z = ∑r∈s,a r*freeOperator c i (F r) z := by
  unfold freeOperator
  rw [secondPartial_finset_sum_analytic s (fun r w => a r*F r w)
    (fun r hr => analyticAt_const.mul (hF r hr))]
  simp only [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  rw [secondPartial_const_mul_analytic (hF r hr)]
  ring

/-- The free atom and every pair atom; the self-pair is identically zero. -/
def cmsAtom (c : Fin d → ℂ) (i : Fin d) : Option (Fin d) → (Point d → ℂ) → Point d → ℂ
  | none => freeOperator c i
  | some j => pairOperator c i j

def cmsAtomWeight (β : ℂ) : Option (Fin d) → ℂ
  | none => 1
  | some _ => 2/β

theorem pairOperator_self (c : Fin d → ℂ) (i : Fin d) (f : Point d → ℂ) :
    pairOperator c i i f = 0 := by
  funext z
  simp [pairOperator,inverseGap]

theorem analyticAt_cmsAtom (c : Fin d → ℂ) (i : Fin d) (a : Option (Fin d))
    {f : Point d → ℂ} (hf : AnalyticAt ℂ f z) (hz : CollisionFree z) :
    AnalyticAt ℂ (cmsAtom c i a f) z := by
  cases a with
  | none => exact analyticAt_freeOperator c i hf
  | some j =>
    by_cases h : i=j
    · subst j
      simpa only [cmsAtom,pairOperator_self] using (analyticAt_const : AnalyticAt ℂ (fun _ : Point d => (0:ℂ)) z)
    · exact analyticAt_pairOperator c i j hf (hz.sub_ne_zero h)

theorem cmsAtom_linear_combination {ι : Type*} (s : Finset ι)
    (F : ι → Point d → ℂ) (hF : ∀a∈s,AnalyticAt ℂ (F a) z)
    (a : ι → ℂ) (c : Fin d → ℂ) (i : Fin d) (b : Option (Fin d)) :
    cmsAtom c i b (fun w => ∑r∈s,a r*F r w) z = ∑r∈s,a r*cmsAtom c i b (F r) z := by
  cases b with
  | none => exact freeOperator_linear_combination s F hF a c i
  | some j => exact pairOperator_linear_combination s F hF a c i j

theorem deformedOperator_eq_atom_sum (β : ℂ) (c : Fin d → ℂ) (i : Fin d)
    (f : Point d → ℂ) (z : Point d) :
    deformedOperator β c i f z = ∑a : Option (Fin d),cmsAtomWeight β a*cmsAtom c i a f z := by
  rw [Fintype.sum_option]
  simp only [cmsAtomWeight,cmsAtom,one_mul,← Finset.mul_sum]
  have hs : (∑j,pairOperator c i j f z) = ∑j∈Finset.univ.erase i,pairOperator c i j f z := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),pairOperator_self]
    simp
  rw [hs]
  unfold deformedOperator freeOperator
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  simp only [pairOperator,inverseGap,chargeDirection,div_eq_mul_inv,mul_comm]

/-- A finite double sum of actual pair/free brackets, with every higher
coordinate derivative cancellation deferred to its local identity. -/
theorem deformedOperator_commutator_atom_sum (β : ℂ) (c : Fin d → ℂ) (i j : Fin d)
    {f : Point d → ℂ} (hf : AnalyticAt ℂ f z) (hz : CollisionFree z) :
    operatorCommutator (deformedOperator β c i) (deformedOperator β c j) f z =
      ∑a : Option (Fin d),∑b : Option (Fin d),
        cmsAtomWeight β a*cmsAtomWeight β b*
          operatorCommutator (cmsAtom c i a) (cmsAtom c j b) f z := by
  have he k : deformedOperator β c k f = fun w =>
      ∑a : Option (Fin d),cmsAtomWeight β a*cmsAtom c k a f w := by
    funext w
    exact deformedOperator_eq_atom_sum β c k f w
  unfold operatorCommutator
  rw [deformedOperator_eq_atom_sum,deformedOperator_eq_atom_sum,he j,he i]
  simp only [cmsAtom_linear_combination Finset.univ _
    (fun a _ => analyticAt_cmsAtom c _ a hf hz),Finset.mul_sum]
  rw [Finset.sum_comm (f := fun a b => cmsAtomWeight β a*
    (cmsAtomWeight β b*cmsAtom c j a (cmsAtom c i b f) z))]
  simp only [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

end BourgadeHuang.CMS
