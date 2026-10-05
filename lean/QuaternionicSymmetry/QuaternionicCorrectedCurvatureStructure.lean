import QuaternionicSymmetry.QuaternionicManifoldCorrectedConnectionStructure
import QuaternionicSymmetry.LocalConnectionSkewCurvature

/-! The actual corrected curvature is a metric quaternionic operator. -/
namespace QuaternionicSymmetry.QuaternionicCorrectedCurvatureStructure
open QuaternionicManifoldCorrectedConnection QuaternionicProjectiveStandardL2
open QuaternionicProjectiveStandardHilbertStructure
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
local instance : NormedSpace ℝ E := inferInstance
local instance : NormedSpace ℝ (StandardSpace (E := E)) := inferInstance
local instance : NormedSpace ℝ
    (StandardSpace (E := E) →L[ℝ] StandardSpace (E := E)) := inferInstance
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem correctedConnection_differentiable (t : ℝ) (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    DifferentiableAt ℝ (correctedConnection S Q D t p) y :=
  ((correctedConnection_smooth S Q D t p).differentiableOn (by norm_num)).differentiableAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy)

theorem curvature_I (t : ℝ) (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (z : StandardSpace (E := E)) :
    LocalConnection.curvature (correctedConnection S Q D t p) y u v ((standardStructure S).I z) =
      (standardStructure S).I (LocalConnection.curvature (correctedConnection S Q D t p) y u v z) := by
  have h := LocalConnectionCommutantCurvature.curvature_commutes
    (correctedConnection S Q D t p) (standardStructure S).I.toContinuousLinearMap y u v
    (correctedConnection_differentiable S Q D t p y hy) (by
      filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy] with x hx w
      apply ContinuousLinearMap.ext
      intro a
      exact correctedConnection_I S Q D t p x w hx a)
  exact congrArg (fun A : StandardSpace (E := E) →L[ℝ] StandardSpace (E := E) => A z) h

theorem curvature_J (t : ℝ) (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (z : StandardSpace (E := E)) :
    LocalConnection.curvature (correctedConnection S Q D t p) y u v ((standardStructure S).J z) =
      (standardStructure S).J (LocalConnection.curvature (correctedConnection S Q D t p) y u v z) := by
  have h := LocalConnectionCommutantCurvature.curvature_commutes
    (correctedConnection S Q D t p) (standardStructure S).J.toContinuousLinearMap y u v
    (correctedConnection_differentiable S Q D t p y hy) (by
      filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy] with x hx w
      apply ContinuousLinearMap.ext
      intro a
      exact correctedConnection_J S Q D t p x w hx a)
  exact congrArg (fun A : StandardSpace (E := E) →L[ℝ] StandardSpace (E := E) => A z) h

theorem curvature_skew (t : ℝ) (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (z w : StandardSpace (E := E)) :
    inner ℝ (LocalConnection.curvature (correctedConnection S Q D t p) y u v z) w +
      inner ℝ z (LocalConnection.curvature (correctedConnection S Q D t p) y u v w) = 0 := by
  apply LocalConnection.curvature_skew _ y u v
    (correctedConnection_differentiable S Q D t p y hy)
  filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p).mem_nhds hy]
    with x hx a b c
  exact correctedConnection_skew S Q D t p x a hx b c

end
end QuaternionicSymmetry.QuaternionicCorrectedCurvatureStructure
