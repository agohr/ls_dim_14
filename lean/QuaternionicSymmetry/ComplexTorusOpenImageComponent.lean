import QuaternionicSymmetry.ComplexTorusIdentityComponentLift
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Connected.Clopen

/-! An open image of a continuous complex-torus homomorphism is exactly the
target's identity component. This upgrades the differential open-image
conclusion without requiring the whole centralizer to be connected. -/

namespace QuaternionicSymmetry.ComplexTorusOpenImageComponent

open QuaternionicSymmetry.ComplexTorusIdentityComponentLift
open IdentityComponentLie
open TorusLaurentRepresentation

theorem range_eq_component {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {r : ℕ} (f : ComplexTorus r →* G)
    (hf : Continuous f) (hOpen : IsOpen (f.range : Set G)) :
    f.range = Component G := by
  apply le_antisymm
  · exact range_le_component f hf
  · have hClosed : IsClosed (f.range : Set G) := f.range.isClosed_of_isOpen hOpen
    have hClopen : IsClopen (f.range : Set G) := ⟨hClosed, hOpen⟩
    intro x hx
    exact hClopen.connectedComponent_subset (f.range.one_mem) hx

end QuaternionicSymmetry.ComplexTorusOpenImageComponent
