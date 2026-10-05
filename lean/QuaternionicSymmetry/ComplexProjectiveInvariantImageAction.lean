import QuaternionicSymmetry.ComplexProjectiveImageTorusAction

/-! Restrict a diagonal projective action using literal image invariance,
independently of the method used to prove that invariance. -/
namespace QuaternionicSymmetry.ComplexProjectiveInvariantImageAction
open ComplexProjectiveTopology ComplexProjectiveDiagonalAction
open TorusLaurentRepresentation ManifoldQuaternionicTorusAction
noncomputable section
variable {r d : ℕ} {X : Type*}

def subsetAction (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hPres : ∀ z : ComplexTorus r, Set.MapsTo (projectiveAction μ z) A A) :
    ComplexTorus r →* Equiv.Perm A where
  toFun z := {
    toFun x := ⟨projectiveAction μ z x, hPres z x.property⟩
    invFun x := ⟨projectiveAction μ z⁻¹ x, hPres z⁻¹ x.property⟩
    left_inv x := by apply Subtype.ext; exact projectiveAction_inv_apply μ z x
    right_inv x := by apply Subtype.ext; exact projectiveAction_apply_inv μ z x }
  map_one' := by ext x; exact projectiveAction_one μ x
  map_mul' z w := by ext x; exact projectiveAction_mul μ z w x

def imageAction (μ : Fin (d + 1) → Fin r → ℤ) (f : X → Space d)
    (hf : Function.Injective f)
    (hPres : ∀ z : ComplexTorus r,
      Set.MapsTo (projectiveAction μ z) (Set.range f) (Set.range f)) :
    ComplexTorus r →* Equiv.Perm X :=
  (Equiv.ofInjective f hf).symm.permCongrHom.toMonoidHom.comp
    (subsetAction μ (Set.range f) hPres)

theorem imageAction_equivariant (μ : Fin (d + 1) → Fin r → ℤ) (f : X → Space d)
    (hf : Function.Injective f)
    (hPres : ∀ z : ComplexTorus r,
      Set.MapsTo (projectiveAction μ z) (Set.range f) (Set.range f))
    (z : ComplexTorus r) (x : X) :
    f (imageAction μ f hf hPres z x) = projectiveAction μ z (f x) := by
  change f ((Equiv.ofInjective f hf).symm
    (subsetAction μ (Set.range f) hPres z ((Equiv.ofInjective f hf) x))) = _
  rw [Equiv.apply_ofInjective_symm hf]
  rfl

theorem imageAction_restrict (μ : Fin (d + 1) → Fin r → ℤ) (f : X → Space d)
    (hf : Function.Injective f)
    (hPres : ∀ z : ComplexTorus r,
      Set.MapsTo (projectiveAction μ z) (Set.range f) (Set.range f))
    (α : Torus r → X → X)
    (hα : ∀ t x, f (α t x) = projectiveAction μ (compactInclusion r t) (f x))
    (t : Torus r) (x : X) :
    imageAction μ f hf hPres (compactInclusion r t) x = α t x := by
  apply hf
  rw [imageAction_equivariant μ f hf hPres, hα]

end
end QuaternionicSymmetry.ComplexProjectiveInvariantImageAction
