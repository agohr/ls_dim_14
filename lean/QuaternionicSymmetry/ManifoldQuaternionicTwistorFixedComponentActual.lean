import QuaternionicSymmetry.ManifoldQuaternionicTwistorFixedFromCompactAction
import QuaternionicSymmetry.ManifoldQuaternionicTwistorMetricSection
import QuaternionicSymmetry.ManifoldQuaternionicTwistorFixedComponentBridge
import QuaternionicSymmetry.ManifoldQuaternionicTwistorComplexFixedAtlas

/-! Use the proved fixed components of the compact lifted action, then
apply the general complex-tangent criterion to their actual inclusions. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicTwistorFixedComponentActual

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicTwistorMetricSection
open ManifoldQuaternionicTwistorMetricBilinear
open ManifoldQuaternionicTwistorFixedComponentBridge
open ManifoldQuaternionicTwistorComplexFixedAtlas
open ManifoldQuaternionicTwistorLiftedFixedSet
open ManifoldRiemannianFixedComponentGenericInput
open ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

private abbrev J := (𝓘(ℝ,E)).prod (𝓡 2)
private abbrev F := E × EuclideanSpace ℝ (Fin 2)

/-- The proved compact-action conclusion supplies the genuine lifted
fixed-component atlas. The connection argument preserves the existing API. -/
theorem exists_liftedFixedComponentAtlas
    [T2Space M] [CompactSpace M]
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    (hBG : ManifoldQuaternionicTwistorFixedFromCompactAction.LiftedFixedComponents Q)
    (S : Subgroup (QuaternionicIsometries Q))
    (z : SphereBundleTotal Q) (hz : z ∈ fixedSpherePoints Q S) :
    ∃ k : ℕ, Nonempty (FixedComponentAtlas (J (E := E))
      (liftedSet Q S) z k) := by
  exact hBG S z hz

/-- The actual lifted fixed component admits a compatible complex atlas,
and its real dimension is twice its complex dimension. Both the compact-action
conclusion and the complex-submanifold criterion have internal proofs used
by the final source assembly. -/
theorem exists_complexFixedAtlas
    [T2Space M] [CompactSpace M]
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (C : ManifoldTwistorLeBrunComplexAtlas.CompatibleComplexAtlas Q D n)
    (hFixed : ManifoldQuaternionicTwistorFixedFromCompactAction.LiftedFixedComponents Q)
    (hComplex : ComplexSubmanifoldInput.ClosedComplexTangentSubmanifoldTheorem)
    (S : Subgroup (QuaternionicIsometries Q))
    (z : SphereBundleTotal Q) (hz : z ∈ fixedSpherePoints Q S) :
    letI := C.charts
    ∃ k : ℕ, ∃ A : FixedComponentAtlas (J (E := E)) (liftedSet Q S) z k,
      ∃ m : ℕ, ∃ B : ComplexSubmanifoldInput.CompatibleComplexAtlas
        (realEmbeddedAtlas Q D C S A) m, k = 2 * m := by
  letI := C.charts
  obtain ⟨k,⟨A⟩⟩ := hFixed S z hz
  obtain ⟨m,B,hdim⟩ := exists_compatibleComplexAtlas_dimension Q D C S A hComplex hz
  exact ⟨k,A,m,B,hdim⟩

end
end QuaternionicSymmetry.ManifoldQuaternionicTwistorFixedComponentActual
