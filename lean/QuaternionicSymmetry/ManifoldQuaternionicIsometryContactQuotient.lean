import QuaternionicSymmetry.ManifoldQuaternionicIsometryTotalHorizontal
import QuaternionicSymmetry.ManifoldQuaternionicTwistorContactWeight

/-! The contact quotient action is genuinely induced by the derivative
of the smooth isometry lift, and is the vertical isotropy character. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicIsometryContactQuotient

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometryTotalHorizontal
open ManifoldQuaternionicTwistorContactWeight
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldTwistorGlobalAlmostComplex
open ManifoldTwistorSphereCore
open ManifoldQuaternionicConnection
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

private abbrev J := (𝓘(ℝ,E)).prod (𝓡 2)
local instance : Fact (Module.finrank ℝ (ManifoldTwistorCoefficientSphere.EuclideanThree) = 2 + 1) :=
  ⟨by simp⟩
local instance (x : M) : ChartedSpace (EuclideanSpace ℝ (Fin 2))
    ((sphereCore Q).Fiber x) := by
  change ChartedSpace (EuclideanSpace ℝ (Fin 2))
    ManifoldTwistorCoefficientSphere.geometricSphere
  infer_instance

/-- The actual manifold derivative descends to the contact quotient
because it preserves the genuine horizontal subspace. -/
def actualContactQuotientDerivative
    (D : CompatibleTangentConnection Q)
    (f : QuaternionicIsometries Q) (z : SphereBundleTotal Q) :
    (TangentSpace (J (E := E)) z ⧸ horizontalTangentSubmodule Q D z) →ₗ[ℝ]
      (TangentSpace (J (E := E)) (sphereTotalMap Q f z) ⧸
        horizontalTangentSubmodule Q D (sphereTotalMap Q f z)) :=
  (horizontalTangentSubmodule Q D z).mapQ
    (horizontalTangentSubmodule Q D (sphereTotalMap Q f z))
    (mfderiv (J (E := E)) (J (E := E)) (sphereTotalMap Q f) z)
    (by intro t ht; exact sphereTotalMap_maps_horizontal Q D f z t ht)

/-- The quotient of the full differential equals the previously constructed
vertical-line transport. Thus the vertical isotropy character is the
actual contact-quotient character, with no separate preservation premise. -/
theorem actualContactQuotientDerivative_eq_transported
    (D : CompatibleTangentConnection Q)
    (f : QuaternionicIsometries Q) (z : SphereBundleTotal Q) :
    actualContactQuotientDerivative Q D f z =
      transportedContactLineDerivative Q D f z := by
  apply LinearMap.ext
  intro x
  let v := contactQuotientEquiv Q D z x
  have hx : (Submodule.Quotient.mk v.1 : TangentSpace (J (E := E)) z ⧸
      horizontalTangentSubmodule Q D z) = x := by
    exact (contactQuotientEquiv Q D z).symm_apply_apply x
  rw [← hx]
  simp only [actualContactQuotientDerivative, Submodule.mapQ_apply,
    transportedContactLineDerivative, LinearMap.comp_apply]
  have hv : contactQuotientEquiv Q D z (Submodule.Quotient.mk v.1) = v :=
    (contactQuotientEquiv Q D z).apply_symm_apply v
  change Submodule.Quotient.mk
      (mfderiv (J (E := E)) (J (E := E)) (sphereTotalMap Q f) z v.1) =
    (contactQuotientEquiv Q D (sphereTotalMap Q f z)).symm
      (actualVerticalDerivative Q f z
        (contactQuotientEquiv Q D z (Submodule.Quotient.mk v.1)))
  rw [hv]
  rfl

end
end QuaternionicSymmetry.ManifoldQuaternionicIsometryContactQuotient
