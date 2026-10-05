import QuaternionicSymmetry.ManifoldTwistorContactBaseDirection

/-! Fixed-chart coordinates on the actual smooth pullback tangent bundle.
The fiber coordinate is the ordinary tangent-bundle transition derivative,
which equals the base direction in the genuine twistor tangent chart. -/

namespace QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex

open Bundle
open QuaternionicSymmetry.ManifoldTwistorSphereBundle
open QuaternionicSymmetry.ManifoldTwistorSphereCore
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
private abbrev J := I (E := E) |>.prod 𝓘(ℝ,E)

def contactBaseTrivialization (p : M) :
    Trivialization E (fun t : TangentBundle 𝓘(ℝ,E) M => t.1) :=
  FiberBundle.trivializationAt E (TangentSpace 𝓘(ℝ,E) : M → Type _) p

def contactPullbackTrivialization (p : M) :=
  (contactBaseTrivialization (E := E) p).pullback (twistorProjectionMap Q)

def contactPullbackCoordinates (p : M)
    (t : Bundle.TotalSpace E (contactPullbackFiber Q)) :
    (E × ManifoldTwistorCoefficientSphere.geometricSphere) × E :=
  (fixedRawChart Q p t.1,
    ((contactPullbackTrivialization Q p) t).2)

theorem contactPullbackCoordinates_baseDirection (p : M)
    (t : Bundle.TotalSpace E (contactPullbackFiber Q))
    (ht : t.1 ∈ ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.source) :
    (contactPullbackCoordinates Q p t).2 =
      (rawTangentCoordinates Q p (contactHorizontalLift Q D t)).1.2 := by
  change (contactPullbackCoordinates Q p t).2 =
    (rawTangentCoordinates Q p
      ⟨t.1,(contactPullbackHorizontalEquiv Q D t.1 t.2).1⟩).1.2
  rw [rawTangentCoordinates_baseDirection Q D p t.1 ht]
  have hu := sphereProjection_mfderiv_horizontalLift Q D t.1 t.2
  rw [sphereProjection_mfderiv Q t.1] at hu
  change ((contactPullbackHorizontalEquiv Q D t.1 t.2 :
    horizontalTangentSubmodule Q D t.1) :
      TangentSpace (I (E := E)) t.1).1 = t.2 at hu
  rw [hu]
  rfl

end
end QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
