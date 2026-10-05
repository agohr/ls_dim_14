import QuaternionicSymmetry.ManifoldQuaternionicTwistorAntipodalCharacter
import QuaternionicSymmetry.ManifoldQuaternionicIsometryContactIsotropy
import QuaternionicSymmetry.ManifoldQuaternionicHolomorphicContactFiberAction

/-! The contact-quotient derivative at the antipodal fixed point has the
conjugate of the original vertical character. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicTwistorAntipodalContactWeight

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicIsometryContactQuotient
open ManifoldQuaternionicIsometryContactIsotropy
open ManifoldQuaternionicIsometryVerticalComplex
open ManifoldQuaternionicHolomorphicContactFiberAction
open ManifoldQuaternionicTwistorIsotropyWeight
open ManifoldQuaternionicVerticalComplexCharacter
open ManifoldQuaternionicTwistorAntipodalWeight
open ManifoldQuaternionicTwistorAntipodalCharacter
open ManifoldTwistorSphereCore
open ManifoldTwistorVerticalComplex
open ManifoldTwistorGlobalAlmostComplex
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorCoefficientSphere
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

private abbrev J := (𝓘(ℝ,E)).prod (𝓡 2)

local instance : Fact (Module.finrank ℝ
    ManifoldTwistorCoefficientSphere.EuclideanThree = 2 + 1) := ⟨by simp⟩
local instance (x : M) : ChartedSpace (EuclideanSpace ℝ (Fin 2))
    ((sphereCore Q).Fiber x) := by
  change ChartedSpace (EuclideanSpace ℝ (Fin 2))
    ManifoldTwistorCoefficientSphere.geometricSphere
  infer_instance

/-- The genuine contact-quotient derivative at the antipode acts by the
conjugate vertical scalar in the antipode's preferred complex coordinate. -/
theorem antipodal_contact_scalar
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    (z : SphereBundleTotal Q) (f : QuaternionicIsometries Q)
    (hz : f • z = z)
    (x : TangentSpace (J (E := E)) (sphereAntipodal Q z) ⧸
      horizontalTangentSubmodule Q D (sphereAntipodal Q z)) :
    ((verticalTangentEquiv Q (sphereTotalMap Q f (sphereAntipodal Q z)))
      ((contactQuotientEquiv Q D (sphereTotalMap Q f (sphereAntipodal Q z)))
        (actualContactQuotientDerivative Q D f (sphereAntipodal Q z) x))).1 =
      (coefficientVerticalComplexSmul
        (coefficientSphereHomeomorph.symm (sphereAntipodal Q z).2)
        (star (verticalScalar Q z ⟨f, hz⟩))
        ((verticalTangentEquiv Q (sphereAntipodal Q z))
          (contactQuotientEquiv Q D (sphereAntipodal Q z) x))).1 := by
  have h := isotropy_contact_weight Q D (sphereAntipodal Q z)
    ⟨f, antipodal_fixed Q z f hz⟩ x
  rw [isotropyVerticalRepresentation_eq_verticalScalar,
    verticalScalar_antipodal] at h
  exact h

/-- The same conjugate scalar acts on the actual holomorphic contact-line
fiber after its canonical quotient and vertical-coordinate identifications. -/
theorem antipodal_holomorphic_contact_fiber_scalar
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} {C : CompatibleComplexAtlas Q D n}
    (L : HolomorphicContactLine Q D n C)
    (z : SphereBundleTotal Q) (f : QuaternionicIsometries Q)
    (hz : f • z = z) (v : L.core.Fiber (sphereAntipodal Q z)) :
    letI := contactQuotientComplexModule Q D (sphereAntipodal Q z)
    letI := contactQuotientComplexModule Q D
      (sphereTotalMap Q f (sphereAntipodal Q z))
    ((verticalTangentEquiv Q (sphereTotalMap Q f (sphereAntipodal Q z)))
      ((contactQuotientEquiv Q D (sphereTotalMap Q f (sphereAntipodal Q z)))
        (L.quotientEquiv (sphereTotalMap Q f (sphereAntipodal Q z))
          (contactLineFiberMap Q D L f (sphereAntipodal Q z) v)))).1 =
      (coefficientVerticalComplexSmul
        (coefficientSphereHomeomorph.symm (sphereAntipodal Q z).2)
        (star (verticalScalar Q z ⟨f, hz⟩))
        ((verticalTangentEquiv Q (sphereAntipodal Q z))
          (contactQuotientEquiv Q D (sphereAntipodal Q z)
            (L.quotientEquiv (sphereAntipodal Q z) v)))).1 := by
  letI := contactQuotientComplexModule Q D (sphereAntipodal Q z)
  letI := contactQuotientComplexModule Q D
    (sphereTotalMap Q f (sphereAntipodal Q z))
  rw [quotientEquiv_contactLineFiberMap,
    actualContactQuotientDerivativeComplex_apply]
  exact antipodal_contact_scalar Q D z f hz (L.quotientEquiv (sphereAntipodal Q z) v)

end
end QuaternionicSymmetry.ManifoldQuaternionicTwistorAntipodalContactWeight
