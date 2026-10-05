import QuaternionicSymmetry.ManifoldTwistorVerticalComplex
/-! Identifies the tangent space of Mathlib’s geometric two-sphere with
the dot-orthogonal quaternionic coefficient plane and transports the
vertical complex rotation onto that actual tangent space. -/

namespace QuaternionicSymmetry.ManifoldTwistorVerticalComplex
open QuaternionicSymmetry.ManifoldTwistorCoefficientSphere
open QuaternionicSymmetry.ManifoldTwistorSphereBundle
open scoped Manifold ContDiff RealInnerProductSpace Matrix
noncomputable section
local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

def sphereOrthogonal (a : geometricSphere) : Submodule ℝ EuclideanThree :=
 (ℝ ∙ (a : EuclideanThree))ᗮ

def sphereTangentMap (a : geometricSphere) :
 TangentSpace (𝓡 2) a →L[ℝ] EuclideanThree :=
 mfderiv (𝓡 2) 𝓘(ℝ,EuclideanThree) ((↑) : geometricSphere → EuclideanThree) a

def tangentToOrthogonal (a : geometricSphere) :
 TangentSpace (𝓡 2) a →L[ℝ] sphereOrthogonal a :=
 (sphereTangentMap a).codRestrict (sphereOrthogonal a) (by
   intro v
   change (sphereTangentMap a) v ∈ (ℝ ∙ (a : EuclideanThree))ᗮ
   rw [← range_mfderiv_coe_sphere (n := 2) a]
   exact ⟨v,rfl⟩)

theorem tangentToOrthogonal_injective (a : geometricSphere) :
 Function.Injective (tangentToOrthogonal a) := by
  intro u v h
  exact mfderiv_coe_sphere_injective a (congrArg Subtype.val h)

theorem tangentToOrthogonal_surjective (a : geometricSphere) :
 Function.Surjective (tangentToOrthogonal a) := by
  intro v
  have hv : v.1 ∈ (sphereTangentMap a).range := by
    change v.1 ∈ (mfderiv (𝓡 2) 𝓘(ℝ,EuclideanThree)
      ((↑) : geometricSphere → EuclideanThree) a).range
    rw [range_mfderiv_coe_sphere (n := 2) a]
    exact v.2
  obtain ⟨u,hu⟩ := hv
  refine ⟨u, ?_⟩
  apply Subtype.ext
  exact hu

def tangentOrthogonalEquiv (a : geometricSphere) :
 TangentSpace (𝓡 2) a ≃ₗ[ℝ] sphereOrthogonal a :=
 LinearEquiv.ofBijective (tangentToOrthogonal a).toLinearMap
   ⟨tangentToOrthogonal_injective a, tangentToOrthogonal_surjective a⟩
theorem dot_eq_inner (a : coefficientSphere) (v : EuclideanThree) :
    a.1 ⬝ᵥ (EuclideanSpace.equiv (Fin 3) ℝ v) =
      inner ℝ (coefficientSphereHomeomorph a : EuclideanThree) v := by
  simp [EuclideanSpace.inner_eq_star_dotProduct,
    coefficientSphereHomeomorph, toEuclidean, EuclideanSpace.equiv,
    dotProduct_comm]
  rfl

def orthogonalToVertical (a : coefficientSphere) :
    sphereOrthogonal (coefficientSphereHomeomorph a) →ₗ[ℝ] verticalSubmodule a where
  toFun v := ⟨EuclideanSpace.equiv (Fin 3) ℝ v.1, by
    change a.1 ⬝ᵥ (EuclideanSpace.equiv (Fin 3) ℝ v.1) = 0
    rw [dot_eq_inner]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp v.2⟩
  map_add' u v := by
    apply Subtype.ext
    exact (EuclideanSpace.equiv (Fin 3) ℝ).map_add u.1 v.1
  map_smul' r v := by
    apply Subtype.ext
    exact (EuclideanSpace.equiv (Fin 3) ℝ).map_smul r v.1

theorem orthogonalToVertical_bijective (a : coefficientSphere) :
    Function.Bijective (orthogonalToVertical a) := by
  constructor
  · intro u v huv
    apply Subtype.ext
    exact (EuclideanSpace.equiv (Fin 3) ℝ).injective
      (congrArg Subtype.val huv)
  · intro v
    let w := (EuclideanSpace.equiv (Fin 3) ℝ).symm v.1
    have hw : w ∈ sphereOrthogonal (coefficientSphereHomeomorph a) := by
      change w ∈ (ℝ ∙ (coefficientSphereHomeomorph a : EuclideanThree))ᗮ
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
      rw [← dot_eq_inner]
      have hv : a.1 ⬝ᵥ v.1 = 0 := v.2
      simpa [w] using hv
    refine ⟨⟨w, hw⟩, ?_⟩
    apply Subtype.ext
    exact (EuclideanSpace.equiv (Fin 3) ℝ).apply_symm_apply v.1

def orthogonalVerticalEquiv (a : coefficientSphere) :
    sphereOrthogonal (coefficientSphereHomeomorph a) ≃ₗ[ℝ] verticalSubmodule a :=
  LinearEquiv.ofBijective (orthogonalToVertical a)
    (orthogonalToVertical_bijective a)

/-- The vertical tangent of the genuine smooth two-sphere is the algebraic
plane perpendicular to its unit quaternionic coefficient. -/
def sphereTangentVerticalEquiv (a : coefficientSphere) :
    TangentSpace (𝓡 2) (coefficientSphereHomeomorph a) ≃ₗ[ℝ]
      verticalSubmodule a :=
  (tangentOrthogonalEquiv (coefficientSphereHomeomorph a)).trans
    (orthogonalVerticalEquiv a)

/-- The actual sphere-fiber tangent rotation, transported from the cross
product through the verified tangent identification. -/
def sphereVerticalComplex (a : coefficientSphere) :
    TangentSpace (𝓡 2) (coefficientSphereHomeomorph a) →ₗ[ℝ]
      TangentSpace (𝓡 2) (coefficientSphereHomeomorph a) :=
  (sphereTangentVerticalEquiv a).symm.toLinearMap.comp
    ((verticalComplex a).comp (sphereTangentVerticalEquiv a).toLinearMap)

theorem sphereVerticalComplex_sq (a : coefficientSphere)
    (v : TangentSpace (𝓡 2) (coefficientSphereHomeomorph a)) :
    sphereVerticalComplex a (sphereVerticalComplex a v) = -v := by
  simp [sphereVerticalComplex, verticalComplex_sq]

end
end QuaternionicSymmetry.ManifoldTwistorVerticalComplex
