import GaussianWave.BS.Lower.CoverInjectivityEvent
import GaussianWave.BS.Lower.FiniteRecoloring

/-! Product recoloring of the actual finite cover sampler. Colliding cover
images are controlled by the genuine exceptional-root count. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
set_option maxHeartbeats 900000

namespace GaussianWave.BS.Lower
open GaussianWave.BS GaussianWave.BS.Reused.Graph
open GaussianWave.BS.Reused.Entropy GaussianWave.BS.Reused.Entropy.Finite

variable {N m q : ℕ}

theorem independentColoringLaw_restrict_mass_finite {S : Type*} [Fintype S]
    (p : Fin N → Fin q → ℝ) (hp : ∀ v b,0 ≤ p v b) (hs : ∀ v,∑ b,p v b=1)
    (site : S ↪ Fin N) (w : S → Fin q) :
    lawMass (independentColoringLaw p hp hs) (fun c i => c (site i)) w = ∏ i,p (site i) (w i) := by
  let P := independentColoringLaw p hp hs
  have hInd := (independentColoringLaw_iIndepFun p hp hs).precomp site.injective
  have hevent : (fun c : Fin N → Fin q => fun i => c (site i)) ⁻¹' {w} =
      ⋂ i : S,(fun c : Fin N → Fin q => c (site i)) ⁻¹' {w i} := by
    ext c
    simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_iInter]
    exact funext_iff
  have hmarg (i : S) : P ((fun c : Fin N → Fin q => c (site i)) ⁻¹' {w i}) =
      ENNReal.ofReal (p (site i) (w i)) := by
    rw [← Measure.map_apply (measurable_pi_apply (site i)) (measurableSet_singleton (w i))]
    change Measure.map _ (independentColoringLaw p hp hs) _ = _
    rw [independentColoringLaw_eval,finiteColorLaw_singleton]
  have heq : P ((fun c : Fin N → Fin q => fun i => c (site i)) ⁻¹' {w}) =
      ∏ i : S,P ((fun c : Fin N → Fin q => c (site i)) ⁻¹' {w i}) := by
    rw [hevent]
    simpa only [Finset.mem_univ,Set.iInter_true] using
      (hInd.measure_inter_preimage_eq_mul Finset.univ
        (sets := fun i : S => {w i}) (fun i _ => measurableSet_singleton (w i)))
  change (P ((fun c : Fin N → Fin q => fun i => c (site i)) ⁻¹' {w})).toReal = _
  rw [heq]
  simp_rw [hmarg]
  simp only [ENNReal.toReal_prod,ENNReal.toReal_ofReal (hp _ _)]

theorem uniformVertexCoverSeed_root_average (k : ℕ) (f : Fin N → ℝ) :
    (Fintype.card (VertexCoverSeed N m k) : ℝ)⁻¹*
      (∑ seed : VertexCoverSeed N m k,f seed.1) = (N : ℝ)⁻¹*∑ v,f v := by
  simp only [VertexCoverSeed,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,
    Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [← Finset.mul_sum]
  by_cases hN : N=0
  · subst N; simp
  have hP : (Fintype.card (Equiv.Perm (Fin (m+2))) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hB : (Fintype.card (Fin (m+2) → BranchCoverOrdering (m+1) k) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  field_simp
  ring

def actualCoverRecolorMass (G : RegularGraph N (m+2)) (k : ℕ)
    (p : Fin N → Fin q → ℝ) (hp : ∀ v b,0 ≤ p v b) (hs : ∀ v,∑ b,p v b=1)
    (w : VertexBallVertex (m+2) k → Fin q) : ℝ :=
  (Fintype.card (VertexCoverSeed N m k) : ℝ)⁻¹*∑ seed : VertexCoverSeed N m k,
    lawMass (independentColoringLaw p hp hs) (fun c v => c (vertexGraphCover G k seed v)) w

def productCoverRecolorMass (G : RegularGraph N (m+2)) (k : ℕ)
    (p : Fin N → Fin q → ℝ) (w : VertexBallVertex (m+2) k → Fin q) : ℝ :=
  (Fintype.card (VertexCoverSeed N m k) : ℝ)⁻¹*∑ seed : VertexCoverSeed N m k,
    ∏ v,p (vertexGraphCover G k seed v) (w v)

/-- The only error between actual independent recoloring on the graph and
independent recoloring on its sampled cover is the proportion of roots
admitting a colliding cover. The estimate holds for every atom. -/
theorem actual_product_cover_recolor_error (G : RegularGraph N (m+2)) (k : ℕ)
    (p : Fin N → Fin q → ℝ) (hp : ∀ v b,0 ≤ p v b) (hs : ∀ v,∑ b,p v b=1)
    (w : VertexBallVertex (m+2) k → Fin q) :
    |actualCoverRecolorMass G k p hp hs w-productCoverRecolorMass G k p w| ≤
      (N : ℝ)⁻¹*badVertexCoverRootCount G k := by
  let P := independentColoringLaw p hp hs
  have hp1 (v : Fin N) (b : Fin q) : p v b ≤ 1 :=
    (Finset.single_le_sum (fun i _ => hp v i) (Finset.mem_univ b)).trans_eq (hs v)
  have hpoint (seed : VertexCoverSeed N m k) :
      |lawMass P (fun c v => c (vertexGraphCover G k seed v)) w-
        ∏ v,p (vertexGraphCover G k seed v) (w v)| ≤
      if GoodVertexCoverRoot G k seed.1 then 0 else 1 := by
    by_cases hg : GoodVertexCoverRoot G k seed.1
    · have hi := hg seed rfl
      have he := independentColoringLaw_restrict_mass_finite p hp hs
        ⟨vertexGraphCover G k seed,hi⟩ w
      change lawMass (independentColoringLaw p hp hs) (fun c v => c (vertexGraphCover G k seed v)) w =
        ∏ v,p (vertexGraphCover G k seed v) (w v) at he
      simp only [P] at he ⊢
      rw [he]
      simp only [sub_self,abs_zero,if_pos hg,le_refl]
    · have ha0 := lawMass_nonneg P (fun c v => c (vertexGraphCover G k seed v)) w
      have ha1 : lawMass P (fun c v => c (vertexGraphCover G k seed v)) w ≤ 1 := by
        exact (measureReal_mono (Set.subset_univ _)).trans_eq (measureReal_univ_eq_one)
      have hb0 : 0 ≤ ∏ v,p (vertexGraphCover G k seed v) (w v) :=
        Finset.prod_nonneg (fun v _ => hp _ _)
      have hb1 : (∏ v,p (vertexGraphCover G k seed v) (w v)) ≤ 1 :=
        Finset.prod_le_one (fun v _ => hp _ _) (fun v _ => hp1 _ _)
      rw [if_neg hg]
      exact abs_le.mpr ⟨by linarith,by linarith⟩
  calc
    _ = (Fintype.card (VertexCoverSeed N m k) : ℝ)⁻¹*
        |∑ seed : VertexCoverSeed N m k,
          (lawMass P (fun c v => c (vertexGraphCover G k seed v)) w-
            ∏ v,p (vertexGraphCover G k seed v) (w v))| := by
      simp only [actualCoverRecolorMass,productCoverRecolorMass,← mul_sub,
        ← Finset.sum_sub_distrib,abs_mul,
        abs_of_nonneg (by positivity : 0 ≤ (Fintype.card (VertexCoverSeed N m k) : ℝ)⁻¹),P]
    _ ≤ (Fintype.card (VertexCoverSeed N m k) : ℝ)⁻¹*
        ∑ seed : VertexCoverSeed N m k,if GoodVertexCoverRoot G k seed.1 then 0 else 1 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun seed _ => hpoint seed))
    _ = _ := uniformVertexCoverSeed_root_average k (fun v => if GoodVertexCoverRoot G k v then 0 else 1)

end GaussianWave.BS.Lower
