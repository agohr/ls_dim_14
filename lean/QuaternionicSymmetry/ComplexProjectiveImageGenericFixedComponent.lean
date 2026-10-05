import QuaternionicSymmetry.ComplexProjectiveCompactFullFixedSet
import QuaternionicSymmetry.ComplexProjectiveImageTorusAction

/-! The generic integral cocharacter keeps the *same literal fixed set*
and therefore the same connected fixed component after passing from the
finite projective coordinate action to an injectively embedded invariant
image. This is not yet a Białynicki–Birula source/attracting-cell claim. -/

namespace QuaternionicSymmetry.ComplexProjectiveImageGenericFixedComponent

open ComplexProjectiveTopology ComplexProjectiveDiagonalAction
open ComplexProjectiveImageTorusAction ComplexProjectivePolynomialLocus
open ComplexProjectiveCompactFullFixedSet
open TorusLaurentRepresentation TorusIntegralCocharacter
open ManifoldQuaternionicTorusAction
noncomputable section

variable {r d : ℕ} {X : Type*}

/-- On an actual injectively embedded invariant projective image, the
same fixed-set equality holds for the constructed Laurent action and the
original compact action. -/
theorem exists_cocharacter_same_image_fixed_set
    (μ : Fin (d + 1) → Fin r → ℤ) (f : X → Space d)
    (hf : Function.Injective f) (hA : HasHomogeneousEquations (Set.range f))
    (α : Torus r → X → X)
    (hα : ∀ t x, f (α t x) = projectiveAction μ (compactInclusion r t) (f x)) :
    ∃ u : Fin r → ℤ,
      {x : X | ∀ z : ℂˣ,
        imageAction μ f hf hA α hα (cocharacter u z) x = x} =
      {x : X | ∀ t : Torus r, α t x = x} := by
  obtain ⟨u,hu⟩ := exists_cocharacter_same_compact_fixed_set μ
  refine ⟨u,?_⟩
  ext x
  have hproj := Set.ext_iff.mp hu (f x)
  constructor
  · intro hx t
    apply hf
    rw [hα]
    have hp : ∀ t : Torus r,
        projectiveAction μ (compactInclusion r t) (f x) = f x :=
      hproj.mp (by
        intro z
        rw [← imageAction_equivariant μ f hf hA α hα]
        exact congrArg f (hx z))
    exact hp t
  · intro hx z
    apply hf
    rw [imageAction_equivariant μ f hf hA α hα (cocharacter u z) x]
    have hp : ∀ z : ℂˣ,
        projectiveAction μ (cocharacter u z) (f x) = f x :=
      hproj.mpr (by
        intro t
        rw [← hα, hx t])
    exact hp z

/-- Consequently a connected component at an actual compact fixed point
is literally the cocharacter-fixed component, rather than merely a
homeomorphic copy. -/
theorem exists_cocharacter_same_image_fixed_component
    [TopologicalSpace X]
    (μ : Fin (d + 1) → Fin r → ℤ) (f : X → Space d)
    (hf : Function.Injective f) (hA : HasHomogeneousEquations (Set.range f))
    (α : Torus r → X → X)
    (hα : ∀ t x, f (α t x) = projectiveAction μ (compactInclusion r t) (f x))
    (x : X) :
    ∃ u : Fin r → ℤ,
      connectedComponentIn
        {y : X | ∀ z : ℂˣ,
          imageAction μ f hf hA α hα (cocharacter u z) y = y} x =
      connectedComponentIn {y : X | ∀ t : Torus r, α t y = y} x := by
  obtain ⟨u,hu⟩ :=
    exists_cocharacter_same_image_fixed_set μ f hf hA α hα
  exact ⟨u,congrArg (fun S : Set X => connectedComponentIn S x) hu⟩

end
end QuaternionicSymmetry.ComplexProjectiveImageGenericFixedComponent
