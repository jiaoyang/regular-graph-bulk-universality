import GaussianWave.BS.ColoredStarFrame
import GaussianWave.BS.LogDensityRigidity

/-!
# Explicit multichannel root and transverse geometry

The ambient coordinates are channel × spatial white-star coordinate.
The actual whole-edge projection retains both endpoint directions in every
channel. Cross-channel tensor entries are treated explicitly; no rank-one
Cramér--Wold shortcut is used.
-/
noncomputable section
open scoped BigOperators Topology ContDiff

namespace GaussianWave.BS

abbrev ColoredSpace (d r : ℕ) := (Fin r × Fin d) → ℝ

def coloredStarRootForm (d r : ℕ) : ColoredSpace d r →ₗ[ℝ] (Fin r → ℝ) where
  toFun x a := starRootForm (fun j => x (a, j))
  map_add' x y := by
    ext a
    simp [starRootForm, Finset.sum_add_distrib, add_div]
  map_smul' c x := by
    ext a
    simp only [starRootForm, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
    ring

def coloredRootLift (d r : ℕ) : (Fin r → ℝ) →ₗ[ℝ] ColoredSpace d r where
  toFun a p := a p.1 * starRootDirection d p.2
  map_add' x y := by ext ⟨a, j⟩; simp [add_mul]
  map_smul' c x := by ext ⟨a, j⟩; simp [mul_assoc]

@[simp] theorem coloredStarRootForm_apply (d r : ℕ) (x : ColoredSpace d r) (a : Fin r) :
    coloredStarRootForm d r x a = starRootForm (fun j => x (a, j)) := rfl

@[simp] theorem coloredRootLift_apply (d r : ℕ) (a : Fin r → ℝ) (b : Fin r) (j : Fin d) :
    coloredRootLift d r a (b, j) = a b * starRootDirection d j := rfl

def coloredRootPart (d r : ℕ) : ColoredSpace d r →ₗ[ℝ] ColoredSpace d r where
  toFun x p := starRootPart d (fun j => x (p.1, j)) p.2
  map_add' x y := by ext ⟨a, j⟩; exact congrFun ((starRootPart d).map_add _ _) j
  map_smul' a x := by ext ⟨b, j⟩; exact congrFun ((starRootPart d).map_smul a _) j

def coloredTransversePart (d r : ℕ) : ColoredSpace d r →ₗ[ℝ] ColoredSpace d r :=
  LinearMap.id - coloredRootPart d r

def coloredPlaneProjection (d r : ℕ) (i : Fin d) :
    ColoredSpace d r →ₗ[ℝ] ColoredSpace d r where
  toFun x p := starPlaneProjection d i (fun j => x (p.1, j)) p.2
  map_add' x y := by ext ⟨a, j⟩; exact congrFun ((starPlaneProjection d i).map_add _ _) j
  map_smul' a x := by ext ⟨b, j⟩; exact congrFun ((starPlaneProjection d i).map_smul a _) j

/-- A literal single-channel embedding, used to retain every cross-channel
entry in the trilinear argument. -/
def coloredBlock (d r : ℕ) (a : Fin r) : (Fin d → ℝ) →ₗ[ℝ] ColoredSpace d r where
  toFun u p := if p.1 = a then u p.2 else 0
  map_add' u v := by ext ⟨b, j⟩; by_cases h : b = a <;> simp [h]
  map_smul' c u := by ext ⟨b, j⟩; by_cases h : b = a <;> simp [h]

@[simp] theorem coloredBlock_apply (d r : ℕ) (a : Fin r) (u : Fin d → ℝ)
    (b : Fin r) (j : Fin d) : coloredBlock d r a u (b, j) = if b = a then u j else 0 := rfl

@[simp] theorem coloredRootPart_apply (d r : ℕ) (x : ColoredSpace d r) (a : Fin r) (j : Fin d) :
    coloredRootPart d r x (a, j) = starRootPart d (fun k => x (a, k)) j := rfl

@[simp] theorem coloredTransversePart_apply (d r : ℕ) (x : ColoredSpace d r) (a : Fin r) (j : Fin d) :
    coloredTransversePart d r x (a, j) = starTransversePart d (fun k => x (a, k)) j := rfl

@[simp] theorem coloredPlaneProjection_apply (d r : ℕ) (i : Fin d) (x : ColoredSpace d r)
    (a : Fin r) (j : Fin d) :
    coloredPlaneProjection d r i x (a, j) = starPlaneProjection d i (fun k => x (a, k)) j := rfl

theorem coloredRootPart_add_transversePart (d r : ℕ) (x : ColoredSpace d r) :
    coloredRootPart d r x + coloredTransversePart d r x = x := by simp [coloredTransversePart]

theorem coloredPlaneProjection_block (d r : ℕ) (i : Fin d) (a : Fin r) (u : Fin d → ℝ) :
    coloredPlaneProjection d r i (coloredBlock d r a u) =
      coloredBlock d r a (starPlaneProjection d i u) := by
  ext ⟨b, j⟩
  by_cases h : b = a
  · subst b
    simp
  · simp [h]
    exact congrFun (map_zero (starPlaneProjection d i)) j

theorem coloredRootPart_block (d r : ℕ) (a : Fin r) (u : Fin d → ℝ) :
    coloredRootPart d r (coloredBlock d r a u) = coloredBlock d r a (starRootPart d u) := by
  ext ⟨b, j⟩
  by_cases h : b = a
  · subst b
    simp
  · simp [h]
    exact congrFun (map_zero (starRootPart d)) j

theorem coloredTransversePart_block (d r : ℕ) (a : Fin r) (u : Fin d → ℝ) :
    coloredTransversePart d r (coloredBlock d r a u) = coloredBlock d r a (starTransversePart d u) := by
  unfold coloredTransversePart starTransversePart
  rw [LinearMap.sub_apply, LinearMap.id_apply, coloredRootPart_block]
  exact ((coloredBlock d r a).map_sub u (starRootPart d u)).symm

theorem coloredPlaneProjection_sum_rootPart (d r : ℕ) (hd : 0 < d) (x : ColoredSpace d r) :
    (∑ i, coloredPlaneProjection d r i (coloredRootPart d r x)) =
      (d : ℝ) • coloredRootPart d r x := by
  ext ⟨a, j⟩
  simpa only [Finset.sum_apply, Pi.smul_apply, coloredPlaneProjection_apply,
    coloredRootPart_apply, smul_eq_mul] using
    congrFun (starPlaneProjection_sum_rootPart d hd (fun k => x (a, k))) j

theorem coloredPlaneProjection_sum_transversePart (d r : ℕ) (hd : 2 ≤ d) (x : ColoredSpace d r) :
    (∑ i, coloredPlaneProjection d r i (coloredTransversePart d r x)) =
      ((d : ℝ) / ((d : ℝ) - 1)) • coloredTransversePart d r x := by
  ext ⟨a, j⟩
  simpa only [Finset.sum_apply, Pi.smul_apply, coloredPlaneProjection_apply,
    coloredTransversePart_apply, smul_eq_mul] using
    congrFun (starPlaneProjection_sum_transversePart d hd (fun k => x (a, k))) j

theorem coloredTransversePart_eq_sum_blocks (d r : ℕ) (x : ColoredSpace d r) :
    coloredTransversePart d r x =
      ∑ a, coloredBlock d r a (fun j => coloredTransversePart d r x (a, j)) := by
  ext ⟨b, j⟩
  simp only [Finset.sum_apply, coloredBlock_apply]
  simp

theorem sum_coloredTransversePart (d r : ℕ) (hd : 0 < d) (x : ColoredSpace d r) (a : Fin r) :
    (∑ j, coloredTransversePart d r x (a, j)) = 0 :=
  sum_starTransversePart hd (fun j => x (a, j))

theorem coloredRootPart_of_centered (d r : ℕ) (x : ColoredSpace d r)
    (hx : ∀ a, ∑ j, x (a, j) = 0) : coloredRootPart d r x = 0 := by
  ext ⟨a, j⟩
  simp only [coloredRootPart_apply, starRootPart_apply, hx, zero_div, Pi.zero_apply]

theorem coloredPlaneProjection_eq_transpose_mulVec (d r : ℕ) (hd : 2 ≤ d)
    (c : ℝ) (hc : |c| < 1) (i : Fin d) (x : ColoredSpace d r) :
    coloredPlaneProjection d r i x =
      (coloredStarEdgeProjection d r c i).transpose.mulVec
        ((coloredStarEdgeProjection d r c i).mulVec x) := by
  ext ⟨a, j⟩
  have h := congrFun (starPlaneProjection_eq_transpose_mulVec d hd c hc i (fun k => x (a, k))) j
  change starPlaneProjection d i (fun k => x (a, k)) j =
    ∑ p : Bool × Fin r, coloredStarEdgeProjection d r c i p (a, j) *
      (coloredStarEdgeProjection d r c i).mulVec x p
  simp only [Fintype.sum_prod_type, coloredStarEdgeProjection_mulVec,
    coloredStarEdgeProjection, ite_mul, zero_mul]
  simpa [Matrix.mulVec, dotProduct, Matrix.transpose_apply] using h

end GaussianWave.BS
