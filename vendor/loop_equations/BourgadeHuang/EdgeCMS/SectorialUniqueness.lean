import BourgadeHuang.EdgeCMS.SectorialRows
import BourgadeHuang.EdgeCMS.FiniteJets
import BourgadeHuang.CMS.RadialJets

/-! Square-free jets determine actual analytic solutions of the normalized
homogeneous system. This removes any need to assume uniqueness for its jets. -/
noncomputable section
open scoped BigOperators Topology ContDiff
open Set Filter
namespace BourgadeHuang.EdgeCMS
open CMS
namespace SectorialData

private theorem word_eq_coordinate {d : ℕ} (w : List (Fin d))
    {U : Set (Point d)} (hU : IsOpen U) (f : Point d → ℂ)
    (hf : AnalyticOnNhd ℂ f U) (z : Point d) (hz : z ∈ U) :
    wordDerivative w f z = coordinateJet w.length f z w.get := by
  induction w generalizing z with
  | nil => simp [wordDerivative, coordinateJet]
  | cons i w ih =>
    have heq : wordDerivative w f =ᶠ[𝓝 z]
        fun y => coordinateJet w.length f y w.get :=
      Filter.eventuallyEq_of_mem (hU.mem_nhds hz) ih
    rw [wordDerivative, coordDeriv_congr_nhds heq, coordDeriv_coordinateJet (hf z hz)]
    congr 1
    funext j
    refine Fin.cases ?_ (fun k => ?_) j <;> rfl


private theorem weighted_first_zero {d n : ℕ} {C : OpenCone d}
    {D : SectorialData C} {f : Point d → ℂ} (hf : D.IsSolution f)
    {z : Point d} (hz : z ∈ C.carrier)
    (hzero : ∀ m < n + 2, iteratedFDeriv ℂ m f z = 0)
    (a : Point d → ℂ) (ha : AnalyticOnNhd ℂ a C.carrier) (j : Fin d) :
    iteratedFDeriv ℂ n (fun w => a w * coordDeriv j f w) z = 0 := by
  apply iteratedFDeriv_mul_eq_zero_of_lower_jets C.isOpen hz
    (fun w hw => (ha w hw).contDiffAt.contDiffWithinAt)
    (fun w hw => (analyticAt_coordDeriv (hf.1 w hw) j).contDiffAt.contDiffWithinAt)
  intro m hm
  exact iteratedFDeriv_coordDeriv_eq_zero C.isOpen hf.1 hz j (hzero (m+1) (by omega))

/-- Repeated derivatives are reduced by the genuine normalized differential
system with its actual analytic coefficient functions. -/
theorem iteratedFDeriv_secondPartial_zero_of_lower_jets {d n : ℕ}
    {C : OpenCone d} {D : SectorialData C} {f : Point d → ℂ}
    (hf : D.IsSolution f) {z : Point d} (hz : z ∈ C.carrier)
    (hzero : ∀ m < n + 2, iteratedFDeriv ℂ m f z = 0) (i : Fin d) :
    iteratedFDeriv ℂ n (secondPartial i f) z = 0 := by
  let P := fun w => D.phase i * coordDeriv i f w
  let T := fun j w => (D.first i j).eval w * coordDeriv j f w
  let V := fun w => (D.scalar i).eval w * f w
  have hP : AnalyticOnNhd ℂ P C.carrier :=
    analyticOnNhd_const.mul (analyticOnNhd_coordDeriv hf.1 i)
  have hT (j : Fin d) : AnalyticOnNhd ℂ (T j) C.carrier :=
    (D.first i j).analytic.mul (analyticOnNhd_coordDeriv hf.1 j)
  have hV : AnalyticOnNhd ℂ V C.carrier := (D.scalar i).analytic.mul hf.1
  have hP0 : iteratedFDeriv ℂ n P z = 0 :=
    weighted_first_zero hf hz hzero _ analyticOnNhd_const i
  have hT0 (j : Fin d) : iteratedFDeriv ℂ n (T j) z = 0 :=
    weighted_first_zero hf hz hzero _ (D.first i j).analytic j
  have hV0 : iteratedFDeriv ℂ n V z = 0 := by
    apply iteratedFDeriv_mul_eq_zero_of_lower_jets C.isOpen hz
      (fun w hw => ((D.scalar i).analytic w hw).contDiffAt.contDiffWithinAt)
      (fun w hw => (hf.1 w hw).contDiffAt.contDiffWithinAt)
    intro m hm
    exact hzero m (by omega)
  have hS : AnalyticOnNhd ℂ (fun w => ∑ j, T j w) C.carrier :=
    Finset.analyticOnNhd_sum _ (fun j _ => hT j)
  have hS0 : iteratedFDeriv ℂ n (fun w => ∑ j, T j w) z = 0 := by
    rw [← iteratedFDerivWithin_of_isOpen n C.isOpen hz,
      iteratedFDerivWithin_sum_apply C.isOpen.uniqueDiffOn hz
        (fun j _ => (hT j z hz).contDiffAt.contDiffWithinAt)]
    apply Finset.sum_eq_zero
    intro j _
    rw [iteratedFDerivWithin_of_isOpen n C.isOpen hz, hT0]
  have he : EqOn (secondPartial i f) (fun w => -(P w + (∑ j, T j w) + V w)) C.carrier := by
    intro w hw
    apply eq_neg_of_add_eq_zero_left
    have hh := hf.2 w hw i
    simpa only [operator, P, T, V, add_assoc] using hh
  rw [iteratedFDeriv_eq_of_eqOn_open C.isOpen hz he]
  change iteratedFDeriv ℂ n (-(fun w => P w + (∑ j, T j w) + V w)) z = 0
  rw [iteratedFDeriv_neg_apply,
    iteratedFDeriv_add_apply' (f := fun w => P w + ∑ j, T j w)
      (g := V) ((hP.add hS) z hz).contDiffAt (hV z hz).contDiffAt,
    iteratedFDeriv_add_apply' (hP z hz).contDiffAt (hS z hz).contDiffAt,
    hP0, hS0, hV0]
  simp

theorem all_jets_zero_of_squareFree {d : ℕ} {C : OpenCone d}
    {D : SectorialData C} {f : Point d → ℂ} (hf : D.IsSolution f)
    {z : Point d} (hz : z ∈ C.carrier) (hsq : SquareFreeJetsVanish f z) :
    ∀ n v, coordinateJet n f z v = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro v
    by_cases hv : Function.Injective v
    · exact hsq n v hv
    · cases n with
      | zero => exact (hv (Function.injective_of_subsingleton v)).elim
      | succ n =>
        cases n with
        | zero =>
          have hvinj : Function.Injective v := by
            intro a b _
            apply Fin.ext
            omega
          exact (hv hvinj).elim
        | succ k =>
          obtain ⟨i, j, hvij, hij⟩ := Function.not_injective_iff.mp hv
          have hpair : (Fin.last k).castSucc ≠ Fin.last (k + 1) := by
            intro h
            have hh := congrArg Fin.val h
            simp at hh
          obtain ⟨π, hπa, hπb⟩ := exists_perm_map_pair hpair hij
          have hzero : ∀ m < k + 2, iteratedFDeriv ℂ m f z = 0 := by
            intro m hm
            exact multilinear_eq_zero_of_coordinate_values _ (ih m hm)
          have hsecond := iteratedFDeriv_secondPartial_zero_of_lower_jets hf hz hzero (v i)
          let w : Fin (k + 2) → Point d := fun q => Pi.single (v (π q)) 1
          have hwlast : w (Fin.last (k + 1)) = Pi.single (v i) 1 := by
            dsimp [w]
            rw [hπb, ← hvij]
          have hwsecond : Fin.init w (Fin.last k) = Pi.single (v i) 1 := by
            change Pi.single (v (π (Fin.last k).castSucc)) 1 = _
            rw [hπa]
          have hwinit : Fin.init w = Fin.snoc (Fin.init (Fin.init w)) (Pi.single (v i) 1) := by
            simpa only [hwsecond] using (Fin.snoc_init_self (Fin.init w)).symm
          have hw : w = Fin.snoc (Fin.snoc (Fin.init (Fin.init w))
              (Pi.single (v i) 1)) (Pi.single (v i) 1) := by
            calc
              w = Fin.snoc (Fin.init w) (w (Fin.last (k + 1))) :=
                (Fin.snoc_init_self w).symm
              _ = _ := by
                conv_lhs => rw [hwinit, hwlast]
          rw [← coordinateJet_comp_perm (hf.1 z hz) v π]
          change iteratedFDeriv ℂ (k + 2) f z w = 0
          rw [hw, ← iteratedFDeriv_secondPartial_apply C.isOpen hf.1 hz (v i)]
          simp only [hsecond, ContinuousMultilinearMap.zero_apply]


/-- A zero family of actual square-free word derivatives determines the
zero analytic germ of the normalized function. -/
theorem locally_zero_of_squareFree {d : ℕ} {C : OpenCone d}
    {D : SectorialData C} {f : Point d → ℂ} (hf : D.IsSolution f)
    {z : Point d} (hz : z ∈ C.carrier)
    (hsq : ∀ S, squareFreeDerivative S f z = 0) :
    f =ᶠ[𝓝 z] 0 := by
  have hsf : SquareFreeJetsVanish f z := by
    intro n v hv
    have hn : (List.ofFn v).Nodup := List.nodup_ofFn.mpr hv
    have hw := wordDerivative_eq_squareFreeDerivative_cone hn hf.1 hz
    rw [hsq, word_eq_coordinate _ C.isOpen f hf.1 z hz] at hw
    have hlen : (List.ofFn v).length = n := List.length_ofFn
    have heq : (List.ofFn v).get = fun k => v (Fin.cast hlen k) := by
      funext k
      exact List.get_ofFn v k
    rw [heq] at hw
    have hcast (m : ℕ) (e : m = n) :
        coordinateJet m f z (fun k => v (Fin.cast e k)) = coordinateJet n f z v := by
      subst m
      rfl
    rw [hcast _ hlen] at hw
    exact hw
  have hall := all_jets_zero_of_squareFree hf hz hsf
  exact analytic_eventually_zero_of_coordinateJet (hf.1 z hz) hall

end SectorialData
end BourgadeHuang.EdgeCMS
