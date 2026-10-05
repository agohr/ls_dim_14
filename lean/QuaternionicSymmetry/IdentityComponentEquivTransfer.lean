import QuaternionicSymmetry.IdentityComponentLie

/-! A homeomorphic group equivalence restricts to the actual identity
components. This is the topological comparison needed before transporting
any group-level complexification statement. -/

namespace QuaternionicSymmetry.IdentityComponentEquivTransfer

open IdentityComponentLie

variable {K H : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  (e : K ≃* H) (he : Continuous e) (he' : Continuous e.symm)

private theorem maps_component (he : Continuous e) (x : Component K) :
    e x.1 ∈ connectedComponent (1 : H) := by
  have h := Continuous.image_connectedComponent_subset he (1 : K)
  have hx := h (Set.mem_image_of_mem e x.2)
  simpa only [map_one] using hx

private theorem symm_maps_component (he' : Continuous e.symm) (x : Component H) :
    e.symm x.1 ∈ connectedComponent (1 : K) := by
  have h := Continuous.image_connectedComponent_subset he' (1 : H)
  have hx := h (Set.mem_image_of_mem e.symm x.2)
  simpa only [map_one] using hx

def componentEquiv (he : Continuous e) (he' : Continuous e.symm) :
    Component K ≃* Component H where
  toFun x := ⟨e x.1, maps_component e he x⟩
  invFun x := ⟨e.symm x.1, symm_maps_component e he' x⟩
  left_inv x := by apply Subtype.ext; exact e.symm_apply_apply x.1
  right_inv x := by apply Subtype.ext; exact e.apply_symm_apply x.1
  map_mul' x y := by apply Subtype.ext; exact e.map_mul x.1 y.1

theorem continuous_componentEquiv : Continuous (componentEquiv e he he') := by
  apply Continuous.subtype_mk
  exact he.comp continuous_subtype_val

theorem continuous_componentEquiv_symm :
    Continuous (componentEquiv e he he').symm := by
  apply Continuous.subtype_mk
  exact he'.comp continuous_subtype_val

end QuaternionicSymmetry.IdentityComponentEquivTransfer
