import BourgadeHuang.CMS.OrderedGapGeometry

/-! Large ordered chambers with prescribed half-planes on any selected
coordinates, as used by the actual fractional-denominator observables. -/
noncomputable section
open Set
namespace BourgadeHuang.CMS

/-- A real-gap chamber with selected independent half-plane constraints. -/
def OrderedGapMixedDomain (d : ℕ) (R : ℝ) (J : Finset (Fin d)) (σ : Fin d → Sign) :
    Set (Point d) :=
  OrderedGapDomain d R ∩ {z | ∀i∈J,if σ i then 0<(z i).im else (z i).im<0}

theorem orderedGapMixedDomain_convex (d : ℕ) (R : ℝ)
    (J : Finset (Fin d)) (σ : Fin d → Sign) : Convex ℝ (OrderedGapMixedDomain d R J σ) := by
  apply (orderedGapDomain_convex d R).inter
  intro x hx y hy a b ha hb hab i hi
  have hxi := hx i hi
  have hyi := hy i hi
  cases hσ : σ i <;> simp only [hσ,Bool.false_eq_true,↓reduceIte] at hxi hyi ⊢
  all_goals
    simp only [Pi.add_apply,Pi.smul_apply,Complex.add_im,Complex.smul_im,smul_eq_mul]
    rcases eq_or_lt_of_le ha with ha|ha
    · subst a
      have hb1 : b=1 := by linarith
      simpa [hb1] using hyi
    · nlinarith [mul_lt_mul_of_pos_left hxi ha,mul_le_mul_of_nonneg_left hyi.le hb]

theorem orderedGapMixedDomain_nonempty (d : ℕ) (R : ℝ)
    (J : Finset (Fin d)) (σ : Fin d → Sign) : (OrderedGapMixedDomain d R J σ).Nonempty := by
  obtain ⟨x,hx⟩ := orderedGapDomain_nonempty d R
  refine ⟨fun i=>(x i).re+(if σ i then Complex.I else -Complex.I),?_,?_⟩
  · intro i j hij
    simpa only [Complex.sub_re,Complex.add_re,Complex.ofReal_re,apply_ite Complex.re,
      Complex.I_re,Complex.neg_re,neg_zero,ite_self,add_zero] using hx i j hij
  · intro i hi
    cases hσ : σ i <;> simp [hσ]

theorem orderedGapMixedDomain_isOpen (d : ℕ) (R : ℝ)
    (J : Finset (Fin d)) (σ : Fin d → Sign) : IsOpen (OrderedGapMixedDomain d R J σ) := by
  apply (orderedGapDomain_isOpen d R).inter
  have he : {z : Point d | ∀i∈J,if σ i then 0<(z i).im else (z i).im<0}=
      ⋂i : Fin d,{z : Point d | i∈J → if σ i then 0<(z i).im else (z i).im<0} := by
    ext z
    simp
  rw [he]
  apply isOpen_iInter_of_finite
  intro i
  by_cases hi : i∈J
  · cases hs : σ i
    · simpa [hi,hs] using isOpen_lt (Complex.continuous_im.comp (continuous_apply i)) continuous_const
    · simpa [hi,hs] using isOpen_lt continuous_const (Complex.continuous_im.comp (continuous_apply i))
  · simpa only [hi,false_implies,setOf_true] using (isOpen_univ : IsOpen (univ : Set (Point d)))

theorem orderedGapMixedDomain_isConnected (d : ℕ) (R : ℝ)
    (J : Finset (Fin d)) (σ : Fin d → Sign) : IsConnected (OrderedGapMixedDomain d R J σ) :=
  (orderedGapMixedDomain_convex d R J σ).isConnected (orderedGapMixedDomain_nonempty d R J σ)

theorem orderedGapMixedDomain_collisionFree {d : ℕ} {R : ℝ} (hR : 0≤R)
    {J : Finset (Fin d)} {σ : Fin d → Sign} {z : Point d}
    (hz : z∈OrderedGapMixedDomain d R J σ) : CollisionFree z :=
  orderedDomain_collisionFree (orderedGapDomain_subset_orderedDomain hR hz.1)

end BourgadeHuang.CMS
