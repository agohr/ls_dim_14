import QuaternionicSymmetry.TorusLaurentRepresentation
import QuaternionicSymmetry.ComplexIdentityComponentLie
import Mathlib.Analysis.Complex.Convex

/-! The actual complex torus is path connected. Every continuous group
homomorphism from it therefore factors through the target's genuine
identity component, with unchanged underlying map and no new source. -/

namespace QuaternionicSymmetry.ComplexTorusIdentityComponentLift

open TorusLaurentRepresentation IdentityComponentLie
noncomputable section

theorem complexTorus_pathConnected (r : ℕ) :
    PathConnectedSpace (ComplexTorus r) := by
  refine ⟨inferInstance, ?_⟩
  intro x y
  exact ⟨Path.pi (fun i => PathConnectedSpace.somePath (x i) (y i))⟩

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {r : ℕ} (f : ComplexTorus r →* G) (hf : Continuous f)

include hf in
theorem range_le_component : f.range ≤ Component G := by
  letI : PathConnectedSpace (ComplexTorus r) := complexTorus_pathConnected r
  have hc : IsConnected (Set.range f) := isConnected_range hf
  exact hc.subset_connectedComponent ⟨1, f.map_one⟩

def lift : ComplexTorus r →* Component G where
  toFun t := ⟨f t, range_le_component f hf ⟨t,rfl⟩⟩
  map_one' := by apply Subtype.ext; exact f.map_one
  map_mul' t u := by apply Subtype.ext; exact f.map_mul t u

@[simp] theorem lift_coe (t : ComplexTorus r) : (lift f hf t : G) = f t := rfl

theorem inclusion_comp_lift : (Component G).subtype.comp (lift f hf) = f := by
  ext t
  rfl

theorem lift_continuous : Continuous (lift f hf) := hf.subtype_mk _

theorem lift_injective (hInj : Function.Injective f) : Function.Injective (lift f hf) := by
  intro t u h
  exact hInj (congrArg Subtype.val h)

end
end QuaternionicSymmetry.ComplexTorusIdentityComponentLift
