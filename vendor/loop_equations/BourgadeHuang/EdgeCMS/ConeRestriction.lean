import BourgadeHuang.EdgeCMS.SectorialReduction

/-! Restriction of actual homogeneous differential systems to a smaller cone. -/
noncomputable section
namespace BourgadeHuang.EdgeCMS
open CMS

namespace Coefficient

def restrict {d : ℕ} {C C' : OpenCone d} (e : Coefficient C)
    (h : C'.carrier ⊆ C.carrier) : Coefficient C' where
  eval := e.eval
  analytic := fun z hz => e.analytic z (h hz)

@[simp] theorem restrict_eval {d : ℕ} {C C' : OpenCone d} (e : Coefficient C)
    (h : C'.carrier ⊆ C.carrier) : (e.restrict h).eval = e.eval := rfl

theorem homogeneous_restrict {d n : ℕ} {C C' : OpenCone d} {e : Coefficient C}
    (he : e.Homogeneous n) (h : C'.carrier ⊆ C.carrier) : (e.restrict h).Homogeneous n := by
  intro t ht z hz
  exact he ht (h hz)

end Coefficient
namespace SectorialData

def restrict {d : ℕ} {C C' : OpenCone d} (D : SectorialData C)
    (h : C'.carrier ⊆ C.carrier) : SectorialData C' where
  phase := D.phase
  first i j := (D.first i j).restrict h
  scalar i := (D.scalar i).restrict h
  first_homogeneous i j := Coefficient.homogeneous_restrict (D.first_homogeneous i j) h
  scalar_homogeneous i := Coefficient.homogeneous_restrict (D.scalar_homogeneous i) h

@[simp] theorem restrict_phase {d : ℕ} {C C' : OpenCone d} (D : SectorialData C)
    (h : C'.carrier ⊆ C.carrier) : (D.restrict h).phase = D.phase := rfl

@[simp] theorem restrict_operator {d : ℕ} {C C' : OpenCone d} (D : SectorialData C)
    (h : C'.carrier ⊆ C.carrier) (i : Fin d) (f : Point d → ℂ) (z : Point d) :
    (D.restrict h).operator i f z = D.operator i f z := rfl

theorem IsSolution.restrict {d : ℕ} {C C' : OpenCone d} {D : SectorialData C}
    {f : Point d → ℂ} (hf : D.IsSolution f) (h : C'.carrier ⊆ C.carrier) :
    (D.restrict h).IsSolution f :=
  ⟨fun z hz => hf.1 z (h hz), fun z hz i => hf.2 z (h hz) i⟩

end SectorialData
end BourgadeHuang.EdgeCMS
