import BourgadeHuang.RationalChargeGeometry
import BourgadeHuang.CMS.PhysicalSectorialBasis
import BourgadeHuang.CMS.OrderedGapMixedGeometry

/-! The general positive-coupling physical CMS basis on prescribed denominator
half-planes, together with collision-removing analytic continuation. -/
noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace BourgadeHuang.RationalBulk
variable {n m : ℕ}

def denominatorIndices (n m : ℕ) : Finset (Fin (n+m)) :=
  Finset.univ.image (Fin.natAdd n)

def chamberSigns (n : ℕ) (eta : Fin m → CMS.Sign) : Fin (n+m) → CMS.Sign :=
  Fin.append (fun _ => false) eta

def largeChamber (n : ℕ) (R : ℝ) (eta : Fin m → CMS.Sign) : Set (CMS.Point (n+m)) :=
  CMS.OrderedGapMixedDomain (n+m) R (denominatorIndices n m) (chamberSigns n eta)

def denominatorDomain (n : ℕ) (eta : Fin m → CMS.Sign) : Set (CMS.Point (n+m)) :=
  {z | ∀j, if eta j then 0<(z (Fin.natAdd n j)).im else (z (Fin.natAdd n j)).im<0}

def sectorialRadius {beta : ℝ} (hbeta : 0<beta) (n m : ℕ) : ℝ :=
  CMS.RadialConstructionData.physicalCommonRadius hbeta (charges beta n m)
    (charges_physical beta n m)

def sectorialBranch {beta : ℝ} (hbeta : 0<beta) (sigma : Fin (n+m) → CMS.Sign) :
    CMS.Point (n+m) → ℂ :=
  CMS.RadialConstructionData.physicalBranch hbeta (charges beta n m) sigma
    (charges_physical beta n m)

def sectorialChamber {beta : ℝ} (hbeta : 0<beta) (n : ℕ)
    (eta : Fin m → CMS.Sign) : Set (CMS.Point (n+m)) :=
  largeChamber n (sectorialRadius hbeta n m) eta

theorem sectorialRadius_pos {beta : ℝ} (hbeta : 0<beta) :
    0 < sectorialRadius hbeta n m :=
  CMS.RadialConstructionData.physicalCommonRadius_pos hbeta (charges beta n m)
    (charges_physical beta n m)

theorem existsUnique_sectorial_expansion {beta : ℝ} (hbeta : 0<beta)
    (F : CMS.Point (n+m) → ℂ) (eta : Fin m → CMS.Sign)
    (ha : AnalyticOnNhd ℂ F (sectorialChamber hbeta n eta))
    (hsol : ∀z∈sectorialChamber hbeta n eta,∀i,
      CMS.deformedOperator (beta:ℂ) (charges beta n m) i F z=0) :
    ∃!b : (Fin (n+m) → CMS.Sign) → ℂ,
      EqOn F (fun z=>∑sigma,b sigma*sectorialBranch hbeta sigma z)
        (sectorialChamber hbeta n eta) := by
  exact CMS.RadialConstructionData.existsUnique_physical_expansion hbeta
    (charges beta n m) (charges_physical beta n m) (sectorialChamber hbeta n eta)
    (CMS.orderedGapMixedDomain_isOpen _ _ _ _)
    (CMS.orderedGapMixedDomain_isConnected _ _ _ _).isPreconnected
    (CMS.orderedGapMixedDomain_nonempty _ _ _ _) (fun _ hz=>hz.1) ha hsol

theorem denominatorDomain_convex (eta : Fin m → CMS.Sign) :
    Convex ℝ (denominatorDomain n eta) := by
  intro x hx y hy a b ha hb hab j
  have hxi := hx j
  have hyi := hy j
  cases hη : eta j <;> simp only [hη,Bool.false_eq_true,↓reduceIte] at hxi hyi ⊢
  all_goals
    simp only [Pi.add_apply,Pi.smul_apply,Complex.add_im,Complex.smul_im,smul_eq_mul]
    rcases eq_or_lt_of_le ha with ha|ha
    · subst a
      have hb1 : b=1 := by linarith
      simpa [hb1] using hyi
    · nlinarith [mul_lt_mul_of_pos_left hxi ha,mul_le_mul_of_nonneg_left hyi.le hb]

theorem largeChamber_subset_denominatorDomain (R : ℝ) (eta : Fin m → CMS.Sign) :
    largeChamber n R eta ⊆ denominatorDomain n eta := by
  intro z hz j
  have hj : Fin.natAdd n j ∈ denominatorIndices n m :=
    Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
  simpa only [chamberSigns,Fin.append_right] using hz.2 _ hj

theorem eqOn_denominatorDomain_of_largeChamber
    (F G : CMS.Point (n+m) → ℂ) (R : ℝ) (eta : Fin m → CMS.Sign)
    (haF : AnalyticOnNhd ℂ F (denominatorDomain n eta))
    (haG : AnalyticOnNhd ℂ G (denominatorDomain n eta))
    (heq : EqOn F G (largeChamber n R eta)) :
    EqOn F G (denominatorDomain n eta) := by
  obtain ⟨z,hz⟩ := CMS.orderedGapMixedDomain_nonempty (n+m) R
    (denominatorIndices n m) (chamberSigns n eta)
  apply haF.eqOn_of_preconnected_of_eventuallyEq haG
    (denominatorDomain_convex eta).isPreconnected
    (largeChamber_subset_denominatorDomain R eta hz)
  exact Filter.mem_of_superset ((CMS.orderedGapMixedDomain_isOpen _ _ _ _).mem_nhds hz)
    (fun _ hw=>heq hw)

theorem twoScaleRay_eventually_sectorialChamber {beta : ℝ} (hbeta : 0<beta)
    (xi delta : Fin (n+m) → ℝ) (epsilon : Fin n → CMS.Sign) (eta : Fin m → CMS.Sign)
    (k : ℕ) (hxi : StrictMono xi) :
    ∀ᶠr : ℝ in atTop,CMS.twoScaleRay xi delta (Fin.append epsilon eta) k r ∈
      sectorialChamber hbeta n eta := by
  filter_upwards [CMS.twoScaleRay_eventually_orderedGapDomain xi delta (Fin.append epsilon eta) k hxi
    (sectorialRadius hbeta n m), CMS.twoScaleRay_eventually_halfPlane xi delta (Fin.append epsilon eta) k]
    with r hr hs
  refine ⟨hr,?_⟩
  intro i hi
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
  simpa only [chamberSigns,Fin.append_right] using hs (Fin.natAdd n j)

theorem twoScalePhase_neutral_zero (beta : ℝ)
    (hn : (n:ℝ) = (m:ℝ)*beta/2)
    (xi : Fin (n+m) → ℝ) (epsilon : Fin n → CMS.Sign) (eta : Fin m → CMS.Sign)
    (k : ℕ) (r : ℝ) :
    (CMS.generalRayPhase (charges beta n m) (Fin.append epsilon eta)
      (CMS.twoScaleRay xi (fun _=>0) (Fin.append epsilon eta) k r)).re=0 := by
  unfold charges
  rw [CMS.generalRayPhase_twoScale_target,sum_realCharges,hn]
  simp

end BourgadeHuang.RationalBulk
