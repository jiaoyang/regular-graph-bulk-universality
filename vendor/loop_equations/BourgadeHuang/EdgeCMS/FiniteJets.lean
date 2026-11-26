import BourgadeHuang.EdgeCMS.Basic

/-! Edge-CMS square-free jet uniqueness. The edge equations reduce
repeated derivatives to lower order, so the actual analytic solution is fixed
by the 2^d canonical subset jets at one point. -/
noncomputable section
open scoped BigOperators Topology ContDiff
open Set Filter
namespace BourgadeHuang.EdgeCMS
open CMS

private theorem iteratedFDeriv_const_mul_zero {d n : ℕ} {f : Point d → ℂ} {z : Point d}
    (hf : ContDiffAt ℂ n f z) (hzero : iteratedFDeriv ℂ n f z = 0) (a : ℂ) :
    iteratedFDeriv ℂ n (fun w => a*f w) z = 0 := by
  change iteratedFDeriv ℂ n (a • f) z = 0
  rw [iteratedFDeriv_const_smul_apply hf,hzero,smul_zero]

/-- Actual general-order reduction of the edge CMS equations. -/
theorem iteratedFDeriv_secondPartial_edge_zero_of_lower_jets {d n : ℕ}
    (β : ℂ) (c : Fin d → ℂ) {U : Set (Point d)} (hU : IsOpen U)
    (hcf : ∀ z∈U, CollisionFree z) {f : Point d → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hsolve : ∀z∈U,∀i,edgeOperator β c i f z = 0)
    {z : Point d} (hz : z∈U)
    (hzero : ∀m<n+2,iteratedFDeriv ℂ m f z = 0) (i : Fin d) :
    iteratedFDeriv ℂ n (secondPartial i f) z = 0 := by
  let T (j : Fin d) (w : Point d) :=
    ((2/β)*(w i-w j)⁻¹)*(c i*c j*coordDeriv i f w-c i^2*coordDeriv j f w)
  let J := Finset.univ.erase i
  have ha j (hj : j∈J) : AnalyticOnNhd ℂ (fun w : Point d => (2/β)*(w i-w j)⁻¹) U :=
    analyticOnNhd_const.mul (analyticOnNhd_inverse_difference hcf (Finset.ne_of_mem_erase hj).symm)
  have hg j : AnalyticOnNhd ℂ
      (fun w => c i*c j*coordDeriv i f w-c i^2*coordDeriv j f w) U :=
    (analyticOnNhd_const.mul (analyticOnNhd_coordDeriv hf i)).sub
      (analyticOnNhd_const.mul (analyticOnNhd_coordDeriv hf j))
  have hT j (hj : j∈J) : AnalyticOnNhd ℂ (T j) U := (ha j hj).mul (hg j)
  have hTzero j (hj : j∈J) : iteratedFDeriv ℂ n (T j) z = 0 := by
    apply iteratedFDeriv_mul_eq_zero_of_lower_jets hU hz
      (fun w hw => (ha j hj w hw).contDiffAt.contDiffWithinAt)
      (fun w hw => (hg j w hw).contDiffAt.contDiffWithinAt)
    intro m hm
    have hdi : iteratedFDeriv ℂ m (coordDeriv i f) z = 0 :=
      iteratedFDeriv_coordDeriv_eq_zero hU hf hz i (hzero (m+1) (by omega))
    have hdj : iteratedFDeriv ℂ m (coordDeriv j f) z = 0 :=
      iteratedFDeriv_coordDeriv_eq_zero hU hf hz j (hzero (m+1) (by omega))
    have hAi : ContDiffAt ℂ m (fun w => c i*c j*coordDeriv i f w) z :=
      (analyticAt_const.mul (analyticAt_coordDeriv (hf z hz) i)).contDiffAt
    have hAj : ContDiffAt ℂ m (fun w => c i^2*coordDeriv j f w) z :=
      (analyticAt_const.mul (analyticAt_coordDeriv (hf z hz) j)).contDiffAt
    have hi0 := iteratedFDeriv_const_mul_zero (analyticAt_coordDeriv (hf z hz) i).contDiffAt hdi (c i*c j)
    have hj0 := iteratedFDeriv_const_mul_zero (analyticAt_coordDeriv (hf z hz) j).contDiffAt hdj (c i^2)
    simp only [sub_eq_add_neg]
    rw [iteratedFDeriv_add_apply' hAi hAj.neg,hi0]
    change 0 + iteratedFDeriv ℂ m (-(fun w => c i^2*coordDeriv j f w)) z = 0
    rw [iteratedFDeriv_neg_apply,hj0]
    simp
  have hsum : AnalyticOnNhd ℂ (fun w => ∑j∈J,T j w) U := J.analyticOnNhd_sum hT
  have hsumzero : iteratedFDeriv ℂ n (fun w => ∑j∈J,T j w) z = 0 := by
    rw [← iteratedFDerivWithin_of_isOpen n hU hz,
      iteratedFDerivWithin_sum_apply hU.uniqueDiffOn hz
        (fun j hj => (hT j hj z hz).contDiffAt.contDiffWithinAt)]
    apply Finset.sum_eq_zero
    intro j hj
    rw [iteratedFDerivWithin_of_isOpen n hU hz,hTzero j hj]
  have hpot : AnalyticOnNhd ℂ (fun w : Point d => -(c i^2*w i)) U :=
    fun w _ => (analyticAt_const.mul ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt w)).neg
  have hbase : AnalyticOnNhd ℂ (fun w => -(c i^2*w i)*f w) U := hpot.mul hf
  have hbasezero : iteratedFDeriv ℂ n (fun w => -(c i^2*w i)*f w) z = 0 := by
    apply iteratedFDeriv_mul_eq_zero_of_lower_jets hU hz
      (fun w hw => (hpot w hw).contDiffAt.contDiffWithinAt)
      (fun w hw => (hf w hw).contDiffAt.contDiffWithinAt)
    intro m hm
    exact hzero m (by omega)
  have hpde : EqOn (secondPartial i f) (fun w => -(-(c i^2*w i)*f w+∑j∈J,T j w)) U := by
    intro w hw
    apply eq_neg_of_add_eq_zero_left
    have heq := hsolve w hw i
    have ht j : T j w = (2/β)*((c i*c j*coordDeriv i f w-c i^2*coordDeriv j f w)/(w i-w j)) := by
      dsimp [T]
      ring
    simpa only [edgeOperator,ht,← Finset.mul_sum,J,sub_eq_add_neg,neg_mul,add_assoc] using heq
  rw [iteratedFDeriv_eq_of_eqOn_open hU hz hpde]
  change iteratedFDeriv ℂ n (-(fun w => -(c i^2*w i)*f w+∑j∈J,T j w)) z = 0
  rw [iteratedFDeriv_neg_apply,iteratedFDeriv_add_apply' (hbase z hz).contDiffAt (hsum z hz).contDiffAt,
    hbasezero,hsumzero]
  simp

/-- Square-free jets determine every actual analytic derivative for all couplings. -/
theorem all_jets_zero_of_squareFree_edge {d : ℕ}
    (β : ℂ) (c : Fin d → ℂ)
    {U : Set (Point d)} (hU : IsOpen U) (hcf : ∀ z ∈ U, CollisionFree z)
    {f : Point d → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hsolve : ∀ z ∈ U, ∀ i, edgeOperator β c i f z = 0)
    {z : Point d} (hz : z ∈ U) (hsq : SquareFreeJetsVanish f z) :
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
          have hsecond := iteratedFDeriv_secondPartial_edge_zero_of_lower_jets
            β c hU hcf hf hsolve hz hzero (v i)
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
          rw [← coordinateJet_comp_perm (hf z hz) v π]
          change iteratedFDeriv ℂ (k + 2) f z w = 0
          rw [hw, ← iteratedFDeriv_secondPartial_apply hU hf hz (v i)]
          simp only [hsecond, ContinuousMultilinearMap.zero_apply]


/-- Uniqueness from the canonical 2^d subset derivatives for the genuine
 general-coupling equations, on every connected open collision-free domain. -/
theorem analytic_eqOn_zero_of_subsetJet_edge {d : ℕ}
    (β : ℂ) (c : Fin d → ℂ) {U : Set (Point d)}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hcf : ∀z∈U,CollisionFree z)
    {f : Point d → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hsolve : ∀z∈U,∀i,edgeOperator β c i f z = 0)
    {z : Point d} (hz : z∈U) (hjets : ∀s,subsetJet f z s = 0) : EqOn f 0 U :=
  analytic_eqOn_zero_of_coordinateJet hf hconn hz
    (all_jets_zero_of_squareFree_edge β c hU hcf hf hsolve hz
      (squareFreeJetsVanish_of_subsetJet (hf z hz) hjets))

end BourgadeHuang.EdgeCMS
