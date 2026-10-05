import QuaternionicSymmetry.ComplexProjectiveTorusPreservation

/-! Transport the proved complex-torus action on a projective polynomial
image back through the actual injective map. Its restriction is the original
compact action by equivariance and injectivity. No regularity or scheme
structure is inferred merely from this action on points. -/
namespace QuaternionicSymmetry.ComplexProjectiveImageTorusAction

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ManifoldQuaternionicTorusAction TorusLaurentRepresentation
open ComplexProjectiveDiagonalAction ComplexProjectiveTorusPreservation
noncomputable section

variable {r d : ℕ} {X : Type*}

theorem compact_range_mapsTo
    (μ : Fin (d + 1) → Fin r → ℤ) (f : X → Space d)
    (α : Torus r → X → X)
    (hα : ∀ t x, f (α t x) = projectiveAction μ (compactInclusion r t) (f x)) :
    ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) (Set.range f) (Set.range f) := by
  rintro t y ⟨x,rfl⟩
  exact ⟨α t x,hα t x⟩

def imageAction
    (μ : Fin (d + 1) → Fin r → ℤ) (f : X → Space d)
    (hf : Function.Injective f) (hA : HasHomogeneousEquations (Set.range f))
    (α : Torus r → X → X)
    (hα : ∀ t x, f (α t x) = projectiveAction μ (compactInclusion r t) (f x)) :
    ComplexTorus r →* Equiv.Perm X :=
  (Equiv.ofInjective f hf).symm.permCongrHom.toMonoidHom.comp
    (cutoutAction μ (Set.range f) hA (compact_range_mapsTo μ f α hα))

theorem imageAction_equivariant
    (μ : Fin (d + 1) → Fin r → ℤ) (f : X → Space d)
    (hf : Function.Injective f) (hA : HasHomogeneousEquations (Set.range f))
    (α : Torus r → X → X)
    (hα : ∀ t x, f (α t x) = projectiveAction μ (compactInclusion r t) (f x))
    (z : ComplexTorus r) (x : X) :
    f (imageAction μ f hf hA α hα z x) = projectiveAction μ z (f x) := by
  change f ((Equiv.ofInjective f hf).symm
    (cutoutAction μ (Set.range f) hA (compact_range_mapsTo μ f α hα) z
      ((Equiv.ofInjective f hf) x))) = _
  rw [Equiv.apply_ofInjective_symm hf]
  rfl

theorem imageAction_restrict
    (μ : Fin (d + 1) → Fin r → ℤ) (f : X → Space d)
    (hf : Function.Injective f) (hA : HasHomogeneousEquations (Set.range f))
    (α : Torus r → X → X)
    (hα : ∀ t x, f (α t x) = projectiveAction μ (compactInclusion r t) (f x))
    (t : Torus r) (x : X) :
    imageAction μ f hf hA α hα (compactInclusion r t) x = α t x := by
  apply hf
  rw [imageAction_equivariant μ f hf hA α hα, hα]

end
end QuaternionicSymmetry.ComplexProjectiveImageTorusAction
