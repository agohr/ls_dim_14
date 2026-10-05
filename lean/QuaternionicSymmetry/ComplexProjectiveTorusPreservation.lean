import QuaternionicSymmetry.ComplexProjectiveDiagonalAction
import QuaternionicSymmetry.CompactTorusPolynomialOrbitLaurent

/-! A finite homogeneous cutout preserved by the compact diagonal torus is
preserved by its full complex-torus extension. This is proved from the literal
polynomial equations and internal Laurent density, not a new source premise.
The resulting action below is an action on points, not yet a scheme action. -/
namespace QuaternionicSymmetry.ComplexProjectiveTorusPreservation

open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ManifoldQuaternionicTorusAction TorusLaurentRepresentation
open ComplexProjectiveDiagonalAction CompactTorusPolynomialOrbitLaurent
open scoped LinearAlgebra.Projectivization
noncomputable section

variable {r d : ℕ}

theorem mapsTo_of_compact
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A) :
    ∀ z : ComplexTorus r, Set.MapsTo (projectiveAction μ z) A A := by
  obtain ⟨N,P,rfl⟩ := hA
  intro z x
  induction x using Projectivization.ind with
  | h v hv =>
    intro hx
    rw [projectiveAction_mk, mem_zeroLocus_mk_iff]
    intro j
    apply eval_diagonal_zero_of_compact (P j).polynomial μ v
    intro t
    have ht := hCompact t hx
    rw [projectiveAction_mk, mem_zeroLocus_mk_iff] at ht
    exact ht j

theorem image_eq_of_compact
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (z : ComplexTorus r) :
    projectiveAction μ z '' A = A := by
  apply Set.Subset.antisymm
  · rintro x ⟨y,hy,rfl⟩
    exact mapsTo_of_compact μ A hA hCompact z hy
  · intro x hx
    refine ⟨projectiveAction μ z⁻¹ x,
      mapsTo_of_compact μ A hA hCompact z⁻¹ hx, ?_⟩
    exact projectiveAction_apply_inv μ z x

/-- Restrict the actual projective action to the polynomial cutout. Its
inverse and group laws follow from the ambient maps, not chosen witnesses. -/
def cutoutAction
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A) :
    ComplexTorus r →* Equiv.Perm A where
  toFun z :=
    { toFun x := ⟨projectiveAction μ z x,
        mapsTo_of_compact μ A hA hCompact z x.property⟩
      invFun x := ⟨projectiveAction μ z⁻¹ x,
        mapsTo_of_compact μ A hA hCompact z⁻¹ x.property⟩
      left_inv x := by apply Subtype.ext; exact projectiveAction_inv_apply μ z x
      right_inv x := by apply Subtype.ext; exact projectiveAction_apply_inv μ z x }
  map_one' := by ext x; exact projectiveAction_one μ x
  map_mul' z w := by ext x; exact projectiveAction_mul μ z w x

@[simp] theorem cutoutAction_coe
    (μ : Fin (d + 1) → Fin r → ℤ) (A : Set (Space d))
    (hA : HasHomogeneousEquations A)
    (hCompact : ∀ t : Torus r,
      Set.MapsTo (projectiveAction μ (compactInclusion r t)) A A)
    (z : ComplexTorus r) (x : A) :
    ((cutoutAction μ A hA hCompact z x : A) : Space d) =
      projectiveAction μ z x := rfl

end
end QuaternionicSymmetry.ComplexProjectiveTorusPreservation
