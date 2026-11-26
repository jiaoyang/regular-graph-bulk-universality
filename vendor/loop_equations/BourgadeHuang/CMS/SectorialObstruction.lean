import BourgadeHuang.CMS.ConnectionCurvature
import BourgadeHuang.CMS.CommutatorSums
import BourgadeHuang.CMS.RadialJets

/-! A flat analytic connection transports every coordinate obstruction by
its homogeneous radial system. This implication uses the actual matrix
curvature identity, independently of any fundamental solution. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace BourgadeHuang.CMS
set_option maxHeartbeats 1600000

section General
variable {d : ℕ} {ι : Type*} [Fintype ι]

def coordinateObstruction (A : Fin d → Point d → Matrix ι ι ℂ)
    (G : Point d → ι → ℂ) (i : Fin d) (S : ι) (z : Point d) : ℂ :=
  coordDeriv i (fun w=>G w S) z-∑T,A i z S T*G z T

theorem analyticAt_coordinateObstruction
    (A : Fin d → Point d → Matrix ι ι ℂ) (G : Point d → ι → ℂ)
    {z : Point d} (hA : ∀i S T,AnalyticAt ℂ (fun w=>A i w S T) z)
    (hG : ∀S,AnalyticAt ℂ (fun w=>G w S) z) (i : Fin d) (S : ι) :
    AnalyticAt ℂ (coordinateObstruction A G i S) z :=
  (analyticAt_coordDeriv (hG S) i).sub
    (Finset.analyticAt_sum Finset.univ (fun T _=>(hA i S T).mul (hG T)))

private theorem obstruction_matrix_product (A B : Matrix ι ι ℂ) (G : ι → ℂ) (S : ι) :
    (∑T,A S T*(∑U,B T U*G U))=(∑T,(∑U,A S U*B U T)*G T) := by
  simp only [Finset.mul_sum,Finset.sum_mul,mul_assoc]
  exact Finset.sum_comm

/-- The difference of two covariant mixed derivatives is the actual matrix
curvature applied to G. -/
theorem coordinateObstruction_commutator
    (A : Fin d → Point d → Matrix ι ι ℂ) (G : Point d → ι → ℂ)
    {z : Point d} (hA : ∀i S T,AnalyticAt ℂ (fun w=>A i w S T) z)
    (hG : ∀S,AnalyticAt ℂ (fun w=>G w S) z) (i j : Fin d) (S : ι) :
    coordDeriv j (coordinateObstruction A G i S) z-
      (∑T,A j z S T*coordinateObstruction A G i T z)-
      coordDeriv i (coordinateObstruction A G j S) z+
      (∑T,A i z S T*coordinateObstruction A G j T z)=
    ∑T,(coordDeriv i (fun w=>A j w S T) z-coordDeriv j (fun w=>A i w S T) z+
      (∑U,A j z S U*A i z U T)-(∑U,A i z S U*A j z U T))*G z T := by
  have hd (i j : Fin d) : coordDeriv j (coordinateObstruction A G i S) z=
      coordDeriv j (coordDeriv i (fun w=>G w S)) z-
        ∑T,(coordDeriv j (fun w=>A i w S T) z*G z T+A i z S T*coordDeriv j (fun w=>G w T) z) := by
    change coordDeriv j (fun w=>coordDeriv i (fun x=>G x S) w-∑T,A i w S T*G w T) z=_
    rw [coordDeriv_sub_analytic (f:=coordDeriv i (fun w=>G w S))
      (g:=fun w=>∑T,A i w S T*G w T) (analyticAt_coordDeriv (hG S) i)
      (Finset.analyticAt_sum Finset.univ (fun T _=>(hA i S T).mul (hG T))) j]
    rw [coordDeriv_finset_sum_analytic Finset.univ (fun T w=>A i w S T*G w T) (fun T _=>(hA i S T).mul (hG T))]
    simp only [coordDeriv_mul_analytic (hA i S _) (hG _)]
  rw [hd,hd,coordDeriv_comm_analytic (hG S) j i]
  simp only [coordinateObstruction,mul_sub,Finset.sum_sub_distrib,Finset.sum_add_distrib]
  rw [obstruction_matrix_product (A j z) (A i z),obstruction_matrix_product (A i z) (A j z)]
  simp only [sub_mul,add_mul,Finset.sum_sub_distrib,Finset.sum_add_distrib]
  ring

/-- Flatness gives equality of the two genuine covariant derivatives. -/
theorem coordinateObstruction_cross
    (A : Fin d → Point d → Matrix ι ι ℂ) (G : Point d → ι → ℂ)
    {z : Point d} (hA : ∀i S T,AnalyticAt ℂ (fun w=>A i w S T) z)
    (hG : ∀S,AnalyticAt ℂ (fun w=>G w S) z)
    (hflat : ∀i j S T,coordDeriv i (fun w=>A j w S T) z-coordDeriv j (fun w=>A i w S T) z+
      (∑U,A j z S U*A i z U T)-(∑U,A i z S U*A j z U T)=0)
    (i j : Fin d) (S : ι) :
    coordDeriv j (coordinateObstruction A G i S) z=
      (∑T,A j z S T*coordinateObstruction A G i T z)+
      coordDeriv i (coordinateObstruction A G j S) z-
      (∑T,A i z S T*coordinateObstruction A G j T z) := by
  have h := coordinateObstruction_commutator A G hA hG i j S
  simp only [hflat,zero_mul,Finset.sum_const_zero] at h
  linear_combination h

/-- If an analytic vector solves the radial equation for one constant
complex direction, every coordinate obstruction solves its homogeneous
radial equation. -/
theorem coordinateObstruction_radial
    (A : Fin d → Point d → Matrix ι ι ℂ) (G : Point d → ι → ℂ)
    (ω : Fin d → ℂ) {U : Set (Point d)} (hU : IsOpen U)
    (hA : ∀i S T,AnalyticOnNhd ℂ (fun w=>A i w S T) U)
    (hG : ∀S,AnalyticOnNhd ℂ (fun w=>G w S) U)
    (hflat : ∀z∈U,∀i j S T,
      coordDeriv i (fun w=>A j w S T) z-coordDeriv j (fun w=>A i w S T) z+
      (∑V,A j z S V*A i z V T)-(∑V,A i z S V*A j z V T)=0)
    (hradial : ∀z∈U,∀S,(∑j,ω j*coordDeriv j (fun w=>G w S) z)=
      ∑j,ω j*(∑T,A j z S T*G z T))
    (i : Fin d) (S : ι) {z : Point d} (hz : z∈U) :
    (∑j,ω j*coordDeriv j (coordinateObstruction A G i S) z)=
      ∑j,ω j*(∑T,A j z S T*coordinateObstruction A G i T z) := by
  have hH (j : Fin d) (T : ι) : AnalyticOnNhd ℂ (coordinateObstruction A G j T) U :=
    fun z hz=>analyticAt_coordinateObstruction A G (fun i S T=>hA i S T z hz) (fun S=>hG S z hz) j T
  have hzero (z : Point d) (hz : z∈U) (T : ι) :
      (∑j,ω j*coordinateObstruction A G j T z)=0 := by
    simp only [coordinateObstruction,mul_sub,Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (hradial z hz T)
  have hd : (∑j,ω j*coordDeriv i (coordinateObstruction A G j S) z)=0 := by
    have he : (fun w=>∑j,ω j*coordinateObstruction A G j S w)=ᶠ[𝓝 z] (fun _=>0) :=
      Filter.eventuallyEq_of_mem (hU.mem_nhds hz) (fun w hw=>hzero w hw S)
    have hh := coordDeriv_congr_nhds he i
    rw [coordDeriv_finset_sum_analytic Finset.univ (fun j w=>ω j*coordinateObstruction A G j S w)
      (fun j _=>analyticAt_const.mul (hH j S z hz))] at hh
    have hc (j : Fin d) := coordDeriv_const_mul_analytic (hH j S z hz) (ω j) i
    simp only [hc] at hh
    simpa only [coordDeriv,deriv_const] using hh
  have hm : (∑j,ω j*(∑T,A i z S T*coordinateObstruction A G j T z))=0 := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have he (T : ι) : (∑j,ω j*(A i z S T*coordinateObstruction A G j T z))=
        A i z S T*(∑j,ω j*coordinateObstruction A G j T z) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    simp only [he,hzero z hz,mul_zero,Finset.sum_const_zero]
  have hx := Finset.sum_congr (s₁:=Finset.univ) (s₂:=Finset.univ) rfl
    (fun j _=>congrArg (fun x : ℂ=>ω j*x)
      (coordinateObstruction_cross A G (fun i S T=>hA i S T z hz)
        (fun S=>hG S z hz) (hflat z hz) i j S))
  rw [hx]
  simp only [mul_sub,mul_add]
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,hd,hm]
  ring

end General

namespace SectorialData
variable {d : ℕ}

def obstruction (D : SectorialData d) (G : Point d → Finset (Fin d) → ℂ)
    (i : Fin d) (S : Finset (Fin d)) : Point d → ℂ :=
  coordinateObstruction (fun i z=>D.connection i z) G i S

/-- Analyticity of the actual finite-jet obstruction on the ordered chamber. -/
theorem analyticOnNhd_obstruction (D : SectorialData d)
    (G : Point d → Finset (Fin d) → ℂ) {U : Set (Point d)}
    (hsub : U⊆OrderedDomain d) (hG : ∀S,AnalyticOnNhd ℂ (fun z=>G z S) U)
    (i : Fin d) (S : Finset (Fin d)) : AnalyticOnNhd ℂ (D.obstruction G i S) U := by
  intro z hz
  exact analyticAt_coordinateObstruction _ G
    (fun j T V=>D.analyticAt_connection j T V (orderedDomain_collisionFree (hsub hz))) (fun T=>hG T z hz) i S

/-- The actual physical CMS connection, with its curvature proved internally,
propagates coordinate compatibility along every fixed radial direction. -/
theorem general_obstruction_radial (β : ℂ) (c : Fin d → ℂ) (σ : Fin d → Sign)
    (hβ : β≠0) (hc : ∀i,c i= -1 ∨ c i=β/2)
    (G : Point d → Finset (Fin d) → ℂ) (ω : Fin d → ℂ)
    {U : Set (Point d)} (hU : IsOpen U) (hsub : U⊆OrderedDomain d)
    (hG : ∀S,AnalyticOnNhd ℂ (fun z=>G z S) U)
    (hradial : ∀z∈U,∀S,(∑j,ω j*coordDeriv j (fun w=>G w S) z)=
      ∑j,ω j*(∑T,(general β c σ).connection j z S T*G z T))
    (i : Fin d) (S : Finset (Fin d)) {z : Point d} (hz : z∈U) :
    (∑j,ω j*coordDeriv j ((general β c σ).obstruction G i S) z)=
      ∑j,ω j*(∑T,(general β c σ).connection j z S T*
        (general β c σ).obstruction G i T z) := by
  exact coordinateObstruction_radial (fun i z=>(general β c σ).connection i z) G ω hU
    (fun j S T z hz=>(general β c σ).analyticAt_connection j S T (orderedDomain_collisionFree (hsub hz))) hG
    (fun z hz i j S T=>general_connection_flat β c σ hβ hc i j S T (hsub hz))
    hradial i S hz

/-- The homogeneous obstruction system is an actual ODE on each complex
ray, not only a formal directional-derivative identity. -/
theorem general_obstruction_hasDerivAt_ray (β : ℂ) (c : Fin d → ℂ) (σ : Fin d → Sign)
    (hβ : β≠0) (hc : ∀i,c i= -1 ∨ c i=β/2)
    (G : Point d → Finset (Fin d) → ℂ) (ω : Fin d → ℂ)
    {U : Set (Point d)} (hU : IsOpen U) (hsub : U⊆OrderedDomain d)
    (hG : ∀S,AnalyticOnNhd ℂ (fun z=>G z S) U)
    (hradial : ∀z∈U,∀S,(∑j,ω j*coordDeriv j (fun w=>G w S) z)=
      ∑j,ω j*(∑T,(general β c σ).connection j z S T*G z T))
    (i : Fin d) (S : Finset (Fin d)) (z : Point d) (t : ℂ)
    (ht : complexAffineRay z ω t∈U) :
    HasDerivAt (fun r=>(general β c σ).obstruction G i S (complexAffineRay z ω r))
      (∑j,ω j*(∑T,(general β c σ).connection j (complexAffineRay z ω t) S T*
        (general β c σ).obstruction G i T (complexAffineRay z ω t))) t := by
  rw [←general_obstruction_radial β c σ hβ hc G ω hU hsub hG hradial i S ht]
  exact hasDerivAt_comp_complexAffineRay z ω t
    ((general β c σ).analyticOnNhd_obstruction G hsub hG i S _ ht)

/-- The same derivative for the real radial parameter used by the Volterra
uniqueness argument. -/
theorem general_obstruction_hasDerivAt_real_ray (β : ℂ) (c : Fin d → ℂ) (σ : Fin d → Sign)
    (hβ : β≠0) (hc : ∀i,c i= -1 ∨ c i=β/2)
    (G : Point d → Finset (Fin d) → ℂ) (ω : Fin d → ℂ)
    {U : Set (Point d)} (hU : IsOpen U) (hsub : U⊆OrderedDomain d)
    (hG : ∀S,AnalyticOnNhd ℂ (fun z=>G z S) U)
    (hradial : ∀z∈U,∀S,(∑j,ω j*coordDeriv j (fun w=>G w S) z)=
      ∑j,ω j*(∑T,(general β c σ).connection j z S T*G z T))
    (i : Fin d) (S : Finset (Fin d)) (z : Point d) (t : ℝ)
    (ht : complexAffineRay z ω (t:ℂ)∈U) :
    HasDerivAt (fun r : ℝ=>(general β c σ).obstruction G i S (complexAffineRay z ω r))
      (∑j,ω j*(∑T,(general β c σ).connection j (complexAffineRay z ω t) S T*
        (general β c σ).obstruction G i T (complexAffineRay z ω t))) t :=
  (general_obstruction_hasDerivAt_ray β c σ hβ hc G ω hU hsub hG hradial i S z t ht).comp_ofReal

end SectorialData
end BourgadeHuang.CMS
