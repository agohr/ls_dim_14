import QuaternionicSymmetry.ManifoldQuaternionicTwistorVerticalDerivative
import QuaternionicSymmetry.ManifoldTwistorContactQuotientComplex

/-! The actual smooth lifted derivative on the vertical line, and its
transport to the fiberwise contact quotient line. The latter is defined via
the verified quotient–vertical equivalence; identifying it with the quotient
of the full derivative requires horizontal-connection naturality. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicTwistorContactWeight

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicTwistorVerticalDerivative
open ManifoldTwistorSphereCore
open ManifoldTwistorGlobalAlmostComplex
open ManifoldQuaternionicConnection
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

private abbrev J := (𝓘(ℝ,E)).prod (𝓡 2)

/-- The restricted *actual manifold derivative* between true vertical
tangent planes of the twistor sphere bundle. -/
def actualVerticalDerivative (f : QuaternionicIsometries Q)
    (z : SphereBundleTotal Q) :
    verticalTangentSubmodule Q z →ₗ[ℝ]
      verticalTangentSubmodule Q (sphereTotalMap Q f z) where
  toFun v := ⟨mfderiv (J (E := E)) (J (E := E))
    (sphereTotalMap Q f) z v.1,
    mfderiv_sphereTotalMap_mem_vertical Q f z v.1 v.2⟩
  map_add' u v := by
    apply Subtype.ext
    exact map_add (mfderiv (J (E := E)) (J (E := E))
      (sphereTotalMap Q f) z) u.1 v.1
  map_smul' c v := by
    apply Subtype.ext
    exact map_smul (mfderiv (J (E := E)) (J (E := E))
      (sphereTotalMap Q f) z) c v.1

/-- The line map on the contact quotient transported from the genuine
vertical derivative through the actual contact quotient/vertical splitting.
Once connection naturality is proved, this equals the quotient of the full
twistor derivative. -/
def transportedContactLineDerivative
    (D : CompatibleTangentConnection Q)
    (f : QuaternionicIsometries Q) (z : SphereBundleTotal Q) :
    (TangentSpace (J (E := E)) z ⧸ horizontalTangentSubmodule Q D z) →ₗ[ℝ]
      (TangentSpace (J (E := E)) (sphereTotalMap Q f z) ⧸
        horizontalTangentSubmodule Q D (sphereTotalMap Q f z)) :=
  (contactQuotientEquiv Q D (sphereTotalMap Q f z)).symm.toLinearMap.comp
    ((actualVerticalDerivative Q f z).comp
      (contactQuotientEquiv Q D z).toLinearMap)

end
end QuaternionicSymmetry.ManifoldQuaternionicTwistorContactWeight
