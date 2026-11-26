import BourgadeHuang.EdgeCMS.RadialCoefficients
import BourgadeHuang.CMS.SectorialRadialSystem

/-! The actual finite scaled-jet radial equation for analytic homogeneous
systems, including the strict triangularity of its principal part. -/
noncomputable section
open scoped BigOperators Topology
open Set
namespace BourgadeHuang.EdgeCMS
open CMS

namespace SectorialData

/-- Constant diagonal of the principal radial system. -/
def principalDiagonal {d : ℕ} {C : OpenCone d} (D : SectorialData C) (ω : Point d) (S : Finset (Fin d)) : ℂ :=
  ∑i : Fin d,if i∈S then -(ω i*D.phase i) else 0

/-- One coordinate's strictly triangular contribution. -/
def lowCoordinate {d : ℕ} {C : OpenCone d} (D : SectorialData C) (ω z : Point d) (t : ℂ)
    (S T : Finset (Fin d)) (i : Fin d) : ℂ :=
  if i∈S then -(ω i)*SquareFreeTerm.homogeneousEntry (D.correctionRow S i) S.card T z t else 0

/-- One coordinate's bounded coefficient of the reciprocal radial term. -/
def highCoordinate {d : ℕ} {C : OpenCone d} (D : SectorialData C) (ω z : Point d) (t : ℂ)
    (S T : Finset (Fin d)) (i : Fin d) : ℂ :=
  if i∈S then -(ω i)*SquareFreeTerm.homogeneousEntry (D.correctionRow S i) (S.card+1) T z t
  else if T=insert i S then ω i else 0

/-- The bounded strictly degree-lowering matrix. -/
def principalRemainder {d : ℕ} {C : OpenCone d} (D : SectorialData C) (ω z : Point d) (t : ℂ)
    (S T : Finset (Fin d)) : ℂ := ∑i,D.lowCoordinate ω z t S T i

/-- The bounded matrix carrying the explicit factor 1/t. -/
def radialRemainder {d : ℕ} {C : OpenCone d} (D : SectorialData C) (ω z : Point d) (t : ℂ)
    (S T : Finset (Fin d)) : ℂ :=
  (if T=S then (S.card:ℂ) else 0)+∑i,D.highCoordinate ω z t S T i

theorem principalRemainder_strict_degree {d : ℕ} {C : OpenCone d} (D : SectorialData C) (ω z : Point d)
    (t : ℂ) (S T : Finset (Fin d)) (hT : ¬T.card<S.card) :
    D.principalRemainder ω z t S T=0 := by
  apply Finset.sum_eq_zero
  intro i _
  unfold lowCoordinate
  split
  · rw [SquareFreeTerm.homogeneousEntry_low_eq_zero _ (D.correctionRow_spec S i) _ _ _ hT,mul_zero]
  · rfl

theorem principalRemainder_empty_column {d : ℕ} {C : OpenCone d} (D : SectorialData C) (ω z : Point d)
    (t : ℂ) (S : Finset (Fin d)) : D.principalRemainder ω z t S ∅=0 := by
  apply Finset.sum_eq_zero
  intro i _
  unfold lowCoordinate
  split
  · rw [SquareFreeTerm.homogeneousEntry_low_empty _ (D.correctionRow_spec S i),mul_zero]
  · rfl

theorem scaled_coordDeriv_eq {d : ℕ} {C : OpenCone d} (D : SectorialData C) (ω : Point d)
    (S : Finset (Fin d)) (i : Fin d) {f : Point d → ℂ} (hf : D.IsSolution f)
    {z : Point d} (hz : z∈C.carrier) {t : ℂ} (ht : t≠0) :
    t^S.card*ω i*coordDeriv i (squareFreeDerivative S f) z=
      (if i∈S then -(ω i*D.phase i) else 0)*scaledSquareFree S f z t+
      (∑T : Finset (Fin d),D.lowCoordinate ω z t S T i*scaledSquareFree T f z t)+
      t⁻¹*(∑T : Finset (Fin d),D.highCoordinate ω z t S T i*scaledSquareFree T f z t) := by
  classical
  by_cases hi : i∈S
  · have hh := D.coordDeriv_squareFreeDerivative_of_mem S hi hf hz
    dsimp only at hh
    rw [hh]
    have hs := SquareFreeTerm.scaled_evalSum_split (D.correctionRow S i)
      (D.correctionRow_spec S i) f z ht
    change t^S.card*SquareFreeTerm.evalSum (D.correctionRow S i) f z=
      (∑T : Finset (Fin d),SquareFreeTerm.homogeneousEntry (D.correctionRow S i) S.card T z t*
        scaledSquareFree T f z t)+
      t⁻¹*(∑T : Finset (Fin d),SquareFreeTerm.homogeneousEntry (D.correctionRow S i) (S.card+1) T z t*
        scaledSquareFree T f z t) at hs
    simp only [lowCoordinate,highCoordinate,if_pos hi]
    simp_rw [mul_assoc,← Finset.mul_sum]
    unfold scaledSquareFree at hs ⊢
    linear_combination -(ω i)*hs
  · rw [coordDeriv_squareFreeDerivative_of_not_mem_cone S hi hf.1 hz]
    simp only [lowCoordinate,highCoordinate,if_neg hi,zero_mul,Finset.sum_const_zero,add_zero,zero_add]
    simp only [ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    unfold scaledSquareFree
    rw [Finset.card_insert_of_not_mem hi,pow_succ]
    field_simp
    ring

/-- Exact radial ODE for the actual square-free derivatives of every solution. -/
theorem hasDerivAt_scaled_squareFree_system {d : ℕ} {C : OpenCone d} (D : SectorialData C)
    (z ω : Point d) (S : Finset (Fin d)) {f : Point d → ℂ} (hf : D.IsSolution f)
    {t : ℂ} (ht : t≠0) (hz : complexAffineRay z ω t∈C.carrier) :
    HasDerivAt (fun r => scaledSquareFree S f (complexAffineRay z ω r) r)
      (D.principalDiagonal ω S*scaledSquareFree S f (complexAffineRay z ω t) t+
        (∑T : Finset (Fin d),D.principalRemainder ω (complexAffineRay z ω t) t S T*
          scaledSquareFree T f (complexAffineRay z ω t) t)+
        t⁻¹*(∑T : Finset (Fin d),D.radialRemainder ω (complexAffineRay z ω t) t S T*
          scaledSquareFree T f (complexAffineRay z ω t) t)) t := by
  have hd := hasDerivAt_scaledSquareFree_ray S z ω ht (hf.1 _ hz)
  convert hd using 1
  let p := complexAffineRay z ω t
  let Y := fun T => scaledSquareFree T f p t
  change D.principalDiagonal ω S*Y S+
    (∑T : Finset (Fin d),D.principalRemainder ω p t S T*Y T)+
    t⁻¹*(∑T : Finset (Fin d),D.radialRemainder ω p t S T*Y T)=
      (S.card:ℂ)/t*Y S+t^S.card*∑i,ω i*coordDeriv i (squareFreeDerivative S f) p
  conv_rhs => rw [Finset.mul_sum]
  have hh : ∀i,t^S.card*(ω i*coordDeriv i (squareFreeDerivative S f) p)=
      (if i∈S then -(ω i*D.phase i) else 0)*Y S+
      (∑T : Finset (Fin d),D.lowCoordinate ω p t S T i*Y T)+
      t⁻¹*(∑T : Finset (Fin d),D.highCoordinate ω p t S T i*Y T) := by
    intro i
    simpa only [mul_assoc] using D.scaled_coordDeriv_eq ω S i hf hz ht
  simp_rw [hh]
  simp only [principalDiagonal,principalRemainder,radialRemainder,Finset.sum_add_distrib,
    Finset.sum_mul,add_mul,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rw [Finset.sum_comm (f := fun T i => D.lowCoordinate ω p t S T i*Y T),
    Finset.sum_comm (f := fun T i => D.highCoordinate ω p t S T i*Y T)]
  rw [← Finset.mul_sum]
  ring

theorem principalRemainder_dilation {d : ℕ} {C : OpenCone d}
    (D : SectorialData C) (ω : Point d) {z : Point d} (hz : z ∈ C.carrier)
    {t : ℝ} (ht : 0 < t) (S T : Finset (Fin d)) :
    D.principalRemainder ω ((t : ℂ) • z) t S T = D.principalRemainder ω z 1 S T := by
  unfold principalRemainder
  apply Finset.sum_congr rfl
  intro i hi
  unfold lowCoordinate
  split_ifs
  · rw [SquareFreeTerm.homogeneousEntry_dilation _ _ _ hz ht]
  · rfl

theorem radialRemainder_dilation {d : ℕ} {C : OpenCone d}
    (D : SectorialData C) (ω : Point d) {z : Point d} (hz : z ∈ C.carrier)
    {t : ℝ} (ht : 0 < t) (S T : Finset (Fin d)) :
    D.radialRemainder ω ((t : ℂ) • z) t S T = D.radialRemainder ω z 1 S T := by
  unfold radialRemainder
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  unfold highCoordinate
  split_ifs
  · rw [SquareFreeTerm.homogeneousEntry_dilation _ _ _ hz ht]
  · rfl
  · rfl

/-- Along a pure positive dilation the actual analytic square-free jet
satisfies a constant triangular principal system plus a constant matrix
divided by the radial parameter.  No asymptotic coefficients are assumed. -/
theorem hasDerivAt_scaled_dilation {d : ℕ} {C : OpenCone d}
    (D : SectorialData C) {z : Point d} (hz : z ∈ C.carrier)
    (S : Finset (Fin d)) {f : Point d → ℂ} (hf : D.IsSolution f)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun r : ℝ => scaledSquareFree S f ((r : ℂ) • z) r)
      (D.principalDiagonal z S * scaledSquareFree S f ((t : ℂ) • z) t +
        (∑ T : Finset (Fin d), D.principalRemainder z z 1 S T *
          scaledSquareFree T f ((t : ℂ) • z) t) +
        (t : ℂ)⁻¹ * (∑ T : Finset (Fin d), D.radialRemainder z z 1 S T *
          scaledSquareFree T f ((t : ℂ) • z) t)) t := by
  have hpoint (s : ℂ) : complexAffineRay (0 : Point d) z s = s • z := by
    ext i
    simp [complexAffineRay, Pi.smul_apply, smul_eq_mul]
  have hd := (D.hasDerivAt_scaled_squareFree_system (0 : Point d) z S hf
    (Complex.ofReal_ne_zero.mpr ht.ne')
    (by simpa only [hpoint] using C.scale_mem ht hz)).comp_ofReal
  simp only [hpoint] at hd
  simpa only [principalRemainder_dilation D z hz ht, radialRemainder_dilation D z hz ht] using hd

end SectorialData
end BourgadeHuang.EdgeCMS
