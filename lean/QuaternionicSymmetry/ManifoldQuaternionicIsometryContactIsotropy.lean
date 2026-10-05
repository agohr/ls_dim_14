import QuaternionicSymmetry.ManifoldQuaternionicIsometryVerticalComplex
import QuaternionicSymmetry.ManifoldQuaternionicTwistorIsotropyWeight

/-! Identification of the derivative-induced contact quotient action at an
actual fixed twistor point with the quaternionic coefficient isotropy weight. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicIsometryContactIsotropy

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicIsometryContactQuotient
open ManifoldQuaternionicIsometryVerticalComplex
open ManifoldQuaternionicTwistorIsotropyWeight
open ManifoldQuaternionicTwistorContactWeight
open ManifoldQuaternionicTwistorVerticalDerivative
open ManifoldTwistorGlobalAlmostComplex
open ManifoldTwistorSphereCore
open ManifoldTwistorVerticalComplex
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

private abbrev J := (𝓘(ℝ,E)).prod (𝓡 2)
private abbrev Isotropy (z : SphereBundleTotal Q) :=
  MulAction.stabilizer (QuaternionicIsometries Q) z

local instance : Fact (Module.finrank ℝ
    ManifoldTwistorCoefficientSphere.EuclideanThree = 2 + 1) := ⟨by simp⟩
local instance (x : M) : ChartedSpace (EuclideanSpace ℝ (Fin 2))
    ((sphereCore Q).Fiber x) := by
  change ChartedSpace (EuclideanSpace ℝ (Fin 2))
    ManifoldTwistorCoefficientSphere.geometricSphere
  infer_instance

/-- In the actual quotient/contact-line fiber at a fixed twistor point,
the derivative action has precisely the coefficient-space isotropy weight. -/
theorem isotropy_contact_weight
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    (z : SphereBundleTotal Q) (f : Isotropy Q z)
    (x : TangentSpace (J (E := E)) z ⧸
      horizontalTangentSubmodule Q D z) :
    ((verticalTangentEquiv Q (sphereTotalMap Q f.1 z))
      ((contactQuotientEquiv Q D (sphereTotalMap Q f.1 z))
        (actualContactQuotientDerivative Q D f.1 z x))).1 =
      ((isotropyVerticalRepresentation Q z f)
        ((verticalTangentEquiv Q z)
          (contactQuotientEquiv Q D z x))).1 := by
  rw [actualContactQuotientDerivative_eq_transported]
  simp only [transportedContactLineDerivative, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply]
  change ((verticalTangentEquiv Q (sphereTotalMap Q f.1 z))
      (actualVerticalDerivative Q f.1 z
        (contactQuotientEquiv Q D z x))).1 = _
  have h := vertical_mfderiv_coefficient Q f.1 z
    (contactQuotientEquiv Q D z x)
  change ((verticalTangentEquiv Q (sphereTotalMap Q f.1 z))
    (actualVerticalDerivative Q f.1 z
      (contactQuotientEquiv Q D z x))).1 = _ at h
  exact h

/-- The same identification uses the complex-linear derivative on the
actual contact quotient, so the isotropy weight is a complex character of
the genuine holomorphic action, not merely a real SO(2) rotation. -/
theorem isotropy_contact_weight_complex
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    (z : SphereBundleTotal Q) (f : Isotropy Q z)
    (x : TangentSpace (J (E := E)) z ⧸
      horizontalTangentSubmodule Q D z) :
    letI := contactQuotientComplexModule Q D z
    letI := contactQuotientComplexModule Q D (sphereTotalMap Q f.1 z)
    ((verticalTangentEquiv Q (sphereTotalMap Q f.1 z))
      ((contactQuotientEquiv Q D (sphereTotalMap Q f.1 z))
        (actualContactQuotientDerivativeComplex Q D f.1 z x))).1 =
      ((isotropyVerticalRepresentation Q z f)
        ((verticalTangentEquiv Q z)
          (contactQuotientEquiv Q D z x))).1 := by
  letI := contactQuotientComplexModule Q D z
  letI := contactQuotientComplexModule Q D (sphereTotalMap Q f.1 z)
  rw [actualContactQuotientDerivativeComplex_apply]
  exact isotropy_contact_weight Q D z f x

end
end QuaternionicSymmetry.ManifoldQuaternionicIsometryContactIsotropy
