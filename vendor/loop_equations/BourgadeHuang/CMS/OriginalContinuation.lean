import BourgadeHuang.CMS.OriginalBasis

/-! Polynomial clearing of the original CMS equations. The cleared residuals
are analytic across every numerator collision, permitting continuation in the
whole numerator space with the off-real denominator coordinates fixed. -/
noncomputable section
open scoped Topology BigOperators
open Filter
namespace BourgadeHuang.CMS

def rowClearing {d : ℕ} (i : Fin d) (z : Point d) : ℂ :=
  ∏ j ∈ Finset.univ.erase i, (z i-z j)

def rowClearingErase {d : ℕ} (i j : Fin d) (z : Point d) : ℂ :=
  ∏ k ∈ (Finset.univ.erase i).erase j, (z i-z k)

theorem rowClearing_ne_zero {d : ℕ} {z : Point d} (hz : CollisionFree z) (i : Fin d) :
    rowClearing i z ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact hz.sub_ne_zero (Ne.symm (Finset.mem_erase.mp hj).1)

theorem rowClearing_mul_div {d : ℕ} {z : Point d} (hz : CollisionFree z)
    (i j : Fin d) (hij : i ≠ j) (a : ℂ) :
    rowClearing i z*(a/(z i-z j)) = rowClearingErase i j z*a := by
  have hp : rowClearing i z = (z i-z j)*rowClearingErase i j z :=
    (Finset.mul_prod_erase (Finset.univ.erase i) (fun k => z i-z k)
      (Finset.mem_erase.mpr ⟨hij.symm,Finset.mem_univ j⟩)).symm
  rw [hp]
  field_simp [hz.sub_ne_zero hij]
  ring

lemma analyticAt_rowClearing {d : ℕ} (i : Fin d) (z : Point d) :
    AnalyticAt ℂ (rowClearing i) z := by
  apply analyticAt_finset_prod
  intro j _
  exact (analyticAt_coord z i).sub (analyticAt_coord z j)

lemma analyticAt_rowClearingErase {d : ℕ} (i j : Fin d) (z : Point d) :
    AnalyticAt ℂ (rowClearingErase i j) z := by
  apply analyticAt_finset_prod
  intro k _
  exact (analyticAt_coord z i).sub (analyticAt_coord z k)

def clearedLeftOriginal {n m : ℕ} (i : Fin n) (F : Point (n+m) → ℂ) (z : Point (n+m)) : ℂ :=
  rowClearing (Fin.castAdd m i) z*(secondPartial (Fin.castAdd m i) F z+F z)+
    (∑ j ∈ Finset.univ.erase i, rowClearingErase (Fin.castAdd m i) (Fin.castAdd m j) z*
      (coordDeriv (Fin.castAdd m i) F z-coordDeriv (Fin.castAdd m j) F z))-
    (∑ a, rowClearingErase (Fin.castAdd m i) (Fin.natAdd n a) z*
      (coordDeriv (Fin.castAdd m i) F z+coordDeriv (Fin.natAdd n a) F z))

def clearedRightOriginal {n m : ℕ} (a : Fin m) (F : Point (n+m) → ℂ) (z : Point (n+m)) : ℂ :=
  rowClearing (Fin.natAdd n a) z*(secondPartial (Fin.natAdd n a) F z+F z)+
    (∑ b ∈ Finset.univ.erase a, rowClearingErase (Fin.natAdd n a) (Fin.natAdd n b) z*
      (coordDeriv (Fin.natAdd n a) F z-coordDeriv (Fin.natAdd n b) F z))-
    (∑ i, rowClearingErase (Fin.natAdd n a) (Fin.castAdd m i) z*
      (coordDeriv (Fin.natAdd n a) F z+coordDeriv (Fin.castAdd m i) F z))

theorem analyticAt_clearedLeftOriginal {n m : ℕ} (i : Fin n)
    {F : Point (n+m) → ℂ} {z : Point (n+m)} (hf : AnalyticAt ℂ F z) :
    AnalyticAt ℂ (clearedLeftOriginal i F) z := by
  have hd (k : Fin (n+m)) := analyticAt_coordDeriv hf k
  have hdd := analyticAt_coordDeriv (hd (Fin.castAdd m i)) (Fin.castAdd m i)
  apply AnalyticAt.sub
  · apply AnalyticAt.add
    · exact (analyticAt_rowClearing _ z).mul (hdd.add hf)
    · apply Finset.analyticAt_sum
      intro j _
      exact (analyticAt_rowClearingErase _ _ z).mul ((hd _).sub (hd _))
  · apply Finset.analyticAt_sum
    intro a _
    exact (analyticAt_rowClearingErase _ _ z).mul ((hd _).add (hd _))

theorem analyticAt_clearedRightOriginal {n m : ℕ} (a : Fin m)
    {F : Point (n+m) → ℂ} {z : Point (n+m)} (hf : AnalyticAt ℂ F z) :
    AnalyticAt ℂ (clearedRightOriginal a F) z := by
  have hd (k : Fin (n+m)) := analyticAt_coordDeriv hf k
  have hdd := analyticAt_coordDeriv (hd (Fin.natAdd n a)) (Fin.natAdd n a)
  apply AnalyticAt.sub
  · apply AnalyticAt.add
    · exact (analyticAt_rowClearing _ z).mul (hdd.add hf)
    · apply Finset.analyticAt_sum
      intro b _
      exact (analyticAt_rowClearingErase _ _ z).mul ((hd _).sub (hd _))
  · apply Finset.analyticAt_sum
    intro i _
    exact (analyticAt_rowClearingErase _ _ z).mul ((hd _).add (hd _))

lemma castAdd_ne_natAdd' {n m : ℕ} (i : Fin n) (a : Fin m) :
    Fin.castAdd m i ≠ Fin.natAdd n a := by
  intro h
  have he := congrArg Fin.val h
  change i.val = n+a.val at he
  omega

theorem clearedLeftOriginal_eq {n m : ℕ} (i : Fin n)
    (G : Point n → Point m → ℂ) (u : Point n) (v : Point m)
    (hz : CollisionFree (Fin.append u v)) :
    clearedLeftOriginal i (blockFunction G) (Fin.append u v) =
      rowClearing (Fin.castAdd m i) (Fin.append u v)*leftOriginal i G u v := by
  unfold clearedLeftOriginal leftOriginal
  simp only [secondPartial_blockFunction_left,coordDeriv_blockFunction_left,
    coordDeriv_blockFunction_right,blockFunction_append]
  simp only [mul_sub,mul_add,Finset.mul_sum]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hne : Fin.castAdd m i ≠ Fin.castAdd m j :=
      (Fin.castAdd_injective n m).ne (Ne.symm (Finset.mem_erase.mp hj).1)
    simpa only [Fin.append_left,Fin.append_right,mul_sub] using
      (rowClearing_mul_div hz _ _ hne (leftPartial i G u v-leftPartial j G u v)).symm
  · apply Finset.sum_congr rfl
    intro a _
    simpa only [Fin.append_left,Fin.append_right,mul_add] using
      (rowClearing_mul_div hz _ _ (castAdd_ne_natAdd' i a) (leftPartial i G u v+rightPartial a G u v)).symm

theorem clearedRightOriginal_eq {n m : ℕ} (a : Fin m)
    (G : Point n → Point m → ℂ) (u : Point n) (v : Point m)
    (hz : CollisionFree (Fin.append u v)) :
    clearedRightOriginal a (blockFunction G) (Fin.append u v) =
      rowClearing (Fin.natAdd n a) (Fin.append u v)*rightOriginal a G u v := by
  unfold clearedRightOriginal rightOriginal
  simp only [secondPartial_blockFunction_right,coordDeriv_blockFunction_left,
    coordDeriv_blockFunction_right,blockFunction_append]
  simp only [mul_sub,mul_add,Finset.mul_sum]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro b hb
    have hne : Fin.natAdd n a ≠ Fin.natAdd n b := by
      intro he
      have hval := congrArg Fin.val he
      exact (Finset.mem_erase.mp hb).1 (Fin.ext (Nat.add_left_cancel hval)).symm
    simpa only [Fin.append_left,Fin.append_right,mul_sub] using
      (rowClearing_mul_div hz _ _ hne (rightPartial a G u v-rightPartial b G u v)).symm
  · apply Finset.sum_congr rfl
    intro i _
    simpa only [Fin.append_left,Fin.append_right,mul_add] using
      (rowClearing_mul_div hz _ _ (Ne.symm (castAdd_ne_natAdd' i a)) (rightPartial a G u v+leftPartial i G u v)).symm

theorem analyticAt_append_left {n m : ℕ} (v : Point m) (u : Point n) :
    AnalyticAt ℂ (fun t : Point n => Fin.append t v) u := by
  apply AnalyticAt.pi
  intro k
  refine Fin.addCases (fun j => ?_) (fun a => ?_) k
  · simpa only [Fin.append_left] using analyticAt_coord u j
  · simpa only [Fin.append_right] using
      (analyticAt_const : AnalyticAt ℂ (fun _ : Point n => v a) u)

/-- Original equations depend only on the combined function germ. -/
theorem solvesOriginalAt_congr_nhds {n m : ℕ}
    {F G : Point (n+m) → ℂ} (u : Point n) (v : Point m)
    (hz : CollisionFree (Fin.append u v))
    (hfg : F =ᶠ[nhds (Fin.append u v)] G)
    (hs : SolvesOriginalAt (n := n) (m := m) F (Fin.append u v)) :
    SolvesOriginalAt (n := n) (m := m) G (Fin.append u v) := by
  have h0 := hfg.eq_of_nhds
  have hd (k : Fin (n+m)) := coordDeriv_congr_nhds hfg k
  have hdd (k : Fin (n+m)) : secondPartial k F (Fin.append u v) =
      secondPartial k G (Fin.append u v) :=
    coordDeriv_congr_nhds (hfg.eventuallyEq_nhds.mono
      (fun _ hw => coordDeriv_congr_nhds hw k)) k
  have hl (i : Fin n) : clearedLeftOriginal i G (Fin.append u v) = 0 := by
    have he : clearedLeftOriginal i F (Fin.append u v) = clearedLeftOriginal i G (Fin.append u v) := by
      simp only [clearedLeftOriginal,h0,hd,hdd]
    rw [← he]
    have hh := clearedLeftOriginal_eq i (restrictBlocks F) u v hz
    have hsi : leftOriginal i (restrictBlocks F) u v = 0 := by
      simpa only [Fin.append_left,Fin.append_right] using hs.1 i
    simpa only [blockFunction_restrictBlocks,hsi,mul_zero] using hh
  have hr (a : Fin m) : clearedRightOriginal a G (Fin.append u v) = 0 := by
    have he : clearedRightOriginal a F (Fin.append u v) = clearedRightOriginal a G (Fin.append u v) := by
      simp only [clearedRightOriginal,h0,hd,hdd]
    rw [← he]
    have hh := clearedRightOriginal_eq a (restrictBlocks F) u v hz
    have hsa : rightOriginal a (restrictBlocks F) u v = 0 := by
      simpa only [Fin.append_left,Fin.append_right] using hs.2 a
    simpa only [blockFunction_restrictBlocks,hsa,mul_zero] using hh
  constructor
  · intro i
    have hc := clearedLeftOriginal_eq i (restrictBlocks G) u v hz
    simp only [blockFunction_restrictBlocks,hl i] at hc
    have hh := (mul_eq_zero.mp hc.symm).resolve_left (rowClearing_ne_zero hz _)
    simpa only [Fin.append_left,Fin.append_right] using hh
  · intro a
    have hc := clearedRightOriginal_eq a (restrictBlocks G) u v hz
    simp only [blockFunction_restrictBlocks,hr a] at hc
    have hh := (mul_eq_zero.mp hc.symm).resolve_left (rowClearing_ne_zero hz _)
    simpa only [Fin.append_left,Fin.append_right] using hh

/-- Original CMS equations on one nonempty numerator neighborhood extend to
all collision-free numerator tuples. Only genuine analyticity of F along the
full fixed-denominator slice is assumed. -/
theorem solvesOriginalAt_of_local_numerator {n m : ℕ}
    (F : Point (n+m) → ℂ) (v : Point m)
    (hf : ∀ u : Point n, AnalyticAt ℂ F (Fin.append u v))
    (u₀ : Point n)
    (hlocal : ∀ᶠ u in nhds u₀, CollisionFree (Fin.append u v) ∧
      SolvesOriginalAt (n := n) (m := m) F (Fin.append u v))
    (u : Point n) (hu : CollisionFree (Fin.append u v)) :
    SolvesOriginalAt (n := n) (m := m) F (Fin.append u v) := by
  have hl (i : Fin n) : clearedLeftOriginal i F (Fin.append u v) = 0 := by
    have ha : AnalyticOnNhd ℂ (fun t : Point n => clearedLeftOriginal i F (Fin.append t v)) Set.univ :=
      fun t _ => (analyticAt_clearedLeftOriginal i (hf t)).comp (f := fun w : Point n => Fin.append w v) (analyticAt_append_left v t)
    have he : (fun t : Point n => clearedLeftOriginal i F (Fin.append t v)) =ᶠ[nhds u₀]
        (fun _ => (0:ℂ)) := by
      filter_upwards [hlocal] with t ht
      have hs : leftOriginal i (restrictBlocks F) t v = 0 := by
        simpa only [SolvesOriginalAt,Fin.append_left,Fin.append_right] using ht.2.1 i
      have hc := clearedLeftOriginal_eq i (restrictBlocks F) t v ht.1
      simpa only [blockFunction_restrictBlocks,hs,mul_zero] using hc
    exact congrFun (ha.eq_of_eventuallyEq analyticOnNhd_const he) u
  have hr (a : Fin m) : clearedRightOriginal a F (Fin.append u v) = 0 := by
    have ha : AnalyticOnNhd ℂ (fun t : Point n => clearedRightOriginal a F (Fin.append t v)) Set.univ :=
      fun t _ => (analyticAt_clearedRightOriginal a (hf t)).comp (f := fun w : Point n => Fin.append w v) (analyticAt_append_left v t)
    have he : (fun t : Point n => clearedRightOriginal a F (Fin.append t v)) =ᶠ[nhds u₀]
        (fun _ => (0:ℂ)) := by
      filter_upwards [hlocal] with t ht
      have hs : rightOriginal a (restrictBlocks F) t v = 0 := by
        simpa only [SolvesOriginalAt,Fin.append_left,Fin.append_right] using ht.2.2 a
      have hc := clearedRightOriginal_eq a (restrictBlocks F) t v ht.1
      simpa only [blockFunction_restrictBlocks,hs,mul_zero] using hc
    exact congrFun (ha.eq_of_eventuallyEq analyticOnNhd_const he) u
  constructor
  · intro i
    have hc := clearedLeftOriginal_eq i (restrictBlocks F) u v hu
    simp only [blockFunction_restrictBlocks,hl i] at hc
    have hs := (mul_eq_zero.mp hc.symm).resolve_left (rowClearing_ne_zero hu _)
    simpa only [Fin.append_left,Fin.append_right] using hs
  · intro a
    have hc := clearedRightOriginal_eq a (restrictBlocks F) u v hu
    simp only [blockFunction_restrictBlocks,hr a] at hc
    have hs := (mul_eq_zero.mp hc.symm).resolve_left (rowClearing_ne_zero hu _)
    simpa only [Fin.append_left,Fin.append_right] using hs

end BourgadeHuang.CMS
