import QuaternionicSymmetry.ManifoldTwistorRawCoordinatesInverse
import Mathlib.Geometry.Manifold.VectorBundle.Pullback

/-! The connection-horizontal contact distribution has a canonical smooth
bundle model: the pullback of the genuine tangent bundle of the base along
the smooth twistor projection. Fiberwise horizontal lift identifies this
bundle with the image of the checked smooth tangent projector. The smooth
bundle instance here is Mathlib's actual pullback `ContMDiffVectorBundle`. -/

namespace QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex

open QuaternionicSymmetry.ManifoldTwistorSphereCore
open QuaternionicSymmetry.ManifoldTwistorSphereManifold
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open QuaternionicSymmetry.ManifoldQuaternionicConnection
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : CompatibleTangentConnection Q)

private abbrev I := (𝓘(ℝ,E)).prod (𝓡 2)

/-- The actual smooth twistor projection, bundled for pulling back the
smooth tangent vector bundle of the base. -/
def twistorProjectionMap :
    C^∞⟮I (E := E), SphereBundleTotal Q; 𝓘(ℝ,E), M⟯ :=
  ⟨fun z => z.1, sphereProjection_smooth Q⟩

/-- The genuine smooth pullback of the base tangent bundle. -/
abbrev contactPullbackFiber (z : SphereBundleTotal Q) : Type _ :=
  ((twistorProjectionMap Q) *ᵖ (TangentSpace 𝓘(ℝ,E) : M → Type _)) z

instance contactPullbackSmoothBundle :
    ContMDiffVectorBundle ∞ E (contactPullbackFiber Q) (I (E := E)) := by
  change ContMDiffVectorBundle ∞ E
    ((twistorProjectionMap Q) *ᵖ (TangentSpace 𝓘(ℝ,E) : M → Type _))
    (I (E := E))
  infer_instance

/-- The connection identifies each pullback tangent fiber with the actual
horizontal subspace of the twistor tangent bundle. -/
def contactPullbackHorizontalEquiv (z : SphereBundleTotal Q) :
    contactPullbackFiber Q z ≃ₗ[ℝ] horizontalTangentSubmodule Q D z :=
  (horizontalFiberEquiv Q D z).symm

theorem contactPullbackHorizontalEquiv_apply (z : SphereBundleTotal Q)
    (u : contactPullbackFiber Q z) :
    ((contactPullbackHorizontalEquiv Q D z u :
      horizontalTangentSubmodule Q D z) : TangentSpace (I (E := E)) z) =
      (connectionTangentEquiv Q D z).symm (u,0) :=
  horizontalFiberEquiv_symm_apply Q D z u

end
end QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
