import QuaternionicSymmetry.EvenFormsMap

/-! Linear-equivalence functoriality for the even exterior subalgebra. -/

namespace QuaternionicSymmetry.EvenForms

noncomputable section

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

private theorem map_comp_apply (f : M →ₗ[R] N) (g : N →ₗ[R] M)
    (x : evenSubalgebra R M) :
    map g (map f x) = map (g.comp f) x := by
  apply Subtype.ext
  change ExteriorAlgebra.map g (ExteriorAlgebra.map f (x : ExteriorAlgebra R M)) = _
  change ((ExteriorAlgebra.map g).comp (ExteriorAlgebra.map f))
      (x : ExteriorAlgebra R M) = _
  rw [ExteriorAlgebra.map_comp_map]
  rfl

/-- The even-subalgebra map induced by a linear equivalence. -/
def equiv (f : M ≃ₗ[R] N) :
    evenSubalgebra R M ≃ₐ[R] evenSubalgebra R N := by
  let F : evenSubalgebra R M →ₐ[R] evenSubalgebra R N := map f.toLinearMap
  let G : evenSubalgebra R N →ₐ[R] evenSubalgebra R M := map f.symm.toLinearMap
  have hleft : Function.LeftInverse G F := by
    intro x
    change map f.symm.toLinearMap (map f.toLinearMap x) = x
    rw [map_comp_apply]
    simp [map]
  have hright : Function.RightInverse G F := by
    intro y
    change map f.toLinearMap (map f.symm.toLinearMap y) = y
    rw [map_comp_apply]
    simp [map]
  exact
    { F with
      invFun := G
      left_inv := hleft
      right_inv := hright }

@[simp] theorem equiv_apply_coe (f : M ≃ₗ[R] N) (x : evenSubalgebra R M) :
    ((equiv f x : evenSubalgebra R N) : ExteriorAlgebra R N) =
      ExteriorAlgebra.map f.toLinearMap (x : ExteriorAlgebra R M) := rfl

@[simp] theorem equiv_symm_apply (f : M ≃ₗ[R] N) (x : evenSubalgebra R N) :
    (equiv f).symm x = map f.symm.toLinearMap x := rfl

theorem map_injective (f : M ≃ₗ[R] N) :
    Function.Injective (map f.toLinearMap) :=
  (equiv f).injective

end
end QuaternionicSymmetry.EvenForms
