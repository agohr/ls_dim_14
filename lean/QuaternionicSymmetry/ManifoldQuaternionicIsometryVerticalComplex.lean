import QuaternionicSymmetry.ManifoldQuaternionicIsometryContactQuotient

/-! Complex linearity of the genuine isometry derivative on the vertical
twistor line and hence on the actual contact quotient. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicIsometryVerticalComplex

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicTwistorContactWeight
open ManifoldQuaternionicTwistorVerticalDerivative
open ManifoldQuaternionicTwistorVerticalAction
open ManifoldQuaternionicIsometryOrientation
open ManifoldQuaternionicIsometryCoefficients
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldTwistorSphereCore
open ManifoldTwistorCoefficientSphere
open ManifoldTwistorVerticalComplex
open ManifoldTwistorGlobalAlmostComplex
open ManifoldQuaternionicConnection
open ManifoldQuaternionicIsometryContactQuotient
open scoped Manifold ContDiff Matrix
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

private abbrev J := (𝓘(ℝ,E)).prod (𝓡 2)
local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩
local instance (x : M) : ChartedSpace (EuclideanSpace ℝ (Fin 2))
    ((sphereCore Q).Fiber x) := by
  change ChartedSpace (EuclideanSpace ℝ (Fin 2)) geometricSphere
  infer_instance

theorem actualVerticalDerivative_complex
    (D : CompatibleTangentConnection Q)
    (f : QuaternionicIsometries Q) (z : SphereBundleTotal Q)
    (v : verticalTangentSubmodule Q z) :
    actualVerticalDerivative Q f z (verticalTangentComplex Q D z v) =
      verticalTangentComplex Q D (sphereTotalMap Q f z)
        (actualVerticalDerivative Q f z v) := by
  apply (verticalTangentEquiv Q (sphereTotalMap Q f z)).injective
  apply Subtype.ext
  have hL := vertical_mfderiv_coefficient Q f z
    (verticalTangentComplex Q D z v)
  change ((verticalTangentEquiv Q (sphereTotalMap Q f z))
      (actualVerticalDerivative Q f z
        (verticalTangentComplex Q D z v))).1 = _ at hL
  have hV := vertical_mfderiv_coefficient Q f z v
  change ((verticalTangentEquiv Q (sphereTotalMap Q f z))
      (actualVerticalDerivative Q f z v)).1 = _ at hV
  rw [hL,
    verticalTangentEquiv_complex Q D z v,
    verticalTangentEquiv_complex Q D (sphereTotalMap Q f z)
      (actualVerticalDerivative Q f z v)]
  change coefficientAction Q f z.1
      ((coefficientSphereHomeomorph.symm z.2).1 ⨯₃
        (verticalTangentEquiv Q z v).1) =
    (coefficientSphereHomeomorph.symm (sphereTotalMap Q f z).2).1 ⨯₃
      (verticalTangentEquiv Q (sphereTotalMap Q f z)
        (actualVerticalDerivative Q f z v)).1
  rw [hV, sphereTotalMap_coefficient]
  exact coefficientAction_cross Q f z.1 _ _

/-- The actual vertical manifold derivative is complex linear for the
geometric complex structures, not merely real-linear with an SO(3) label. -/
def actualVerticalDerivativeComplex
    (D : CompatibleTangentConnection Q)
    (f : QuaternionicIsometries Q) (z : SphereBundleTotal Q) :
    letI := verticalComplexModule Q D z
    letI := verticalComplexModule Q D (sphereTotalMap Q f z)
    verticalTangentSubmodule Q z →ₗ[ℂ]
      verticalTangentSubmodule Q (sphereTotalMap Q f z) := by
  letI := verticalComplexModule Q D z
  letI := verticalComplexModule Q D (sphereTotalMap Q f z)
  exact {
    actualVerticalDerivative Q f z with
    map_smul' := by
      intro c v
      change actualVerticalDerivative Q f z
          (verticalComplexSmul Q D z c v) =
        verticalComplexSmul Q D (sphereTotalMap Q f z) c
          (actualVerticalDerivative Q f z v)
      simp only [verticalComplexSmul, map_add, map_smul,
        actualVerticalDerivative_complex Q D f z v]
  }

/-- The genuine quotient of the full twistor differential is a complex
linear map of the two contact-line fibers. -/
def actualContactQuotientDerivativeComplex
    (D : CompatibleTangentConnection Q)
    (f : QuaternionicIsometries Q) (z : SphereBundleTotal Q) :
    letI := contactQuotientComplexModule Q D z
    letI := contactQuotientComplexModule Q D (sphereTotalMap Q f z)
    (TangentSpace (J (E := E)) z ⧸ horizontalTangentSubmodule Q D z) →ₗ[ℂ]
      (TangentSpace (J (E := E)) (sphereTotalMap Q f z) ⧸
        horizontalTangentSubmodule Q D (sphereTotalMap Q f z)) := by
  letI := contactQuotientComplexModule Q D z
  letI := contactQuotientComplexModule Q D (sphereTotalMap Q f z)
  letI := verticalComplexModule Q D z
  letI := verticalComplexModule Q D (sphereTotalMap Q f z)
  exact (contactQuotientComplexEquiv Q D (sphereTotalMap Q f z)).symm.toLinearMap.comp
    ((actualVerticalDerivativeComplex Q D f z).comp
      (contactQuotientComplexEquiv Q D z).toLinearMap)

theorem actualContactQuotientDerivativeComplex_apply
    (D : CompatibleTangentConnection Q)
    (f : QuaternionicIsometries Q) (z : SphereBundleTotal Q)
    (x : TangentSpace (J (E := E)) z ⧸ horizontalTangentSubmodule Q D z) :
    letI := contactQuotientComplexModule Q D z
    letI := contactQuotientComplexModule Q D (sphereTotalMap Q f z)
    actualContactQuotientDerivativeComplex Q D f z x =
      actualContactQuotientDerivative Q D f z x := by
  dsimp [actualContactQuotientDerivativeComplex,
    actualVerticalDerivativeComplex]
  exact congrArg (fun T => T x)
    (actualContactQuotientDerivative_eq_transported Q D f z).symm

end
end QuaternionicSymmetry.ManifoldQuaternionicIsometryVerticalComplex
