import QuaternionicSymmetry.ManifoldTwistorFixedRawChart

/-!
# Transition between fixed raw twistor charts

On a genuine base-chart overlap, composing one raw twistor chart inverse with
another raw twistor chart gives the base chart transition and the associated
rotating sphere transition. The proof uses the sphere-bundle cocycle.
-/

namespace QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
open QuaternionicSymmetry.ManifoldTwistorSphereBundle
open QuaternionicSymmetry.ManifoldTwistorSphereCore
open QuaternionicSymmetry.ManifoldTwistorCoefficientSphere
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open QuaternionicSymmetry.ManifoldQuaternionicConnection
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
 [Nontrivial E] [FiniteDimensional ℝ E]
 [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

def rawSphereTransition (p q : M) (ys : E × geometricSphere) :
    E × geometricSphere :=
  (chartTransition (I := 𝓘(ℝ,E)) p q ys.1,
    (sphereCore Q).coordChange (achart E p) (achart E q)
      ((extChartAt 𝓘(ℝ,E) p).symm ys.1) ys.2)

theorem fixedRawChart_transition (p q : M) (y : E) (s : geometricSphere)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) p q) :
    fixedRawChart Q q (fixedRawChartInv Q p (y,s)) =
      rawSphereTransition Q p q (y,s) := by
  let x := (extChartAt 𝓘(ℝ,E) p).symm y
  let Z := sphereCore Q
  have hp : x ∈ Z.baseSet (achart E p) := by
    have h := (extChartAt 𝓘(ℝ,E) p).map_target hy.1
    simpa only [x, Z, sphereCore,
      ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ,E)] using h
  have hq : x ∈ Z.baseSet (achart E q) := by
    have h := hy.2
    simpa only [x, Z, sphereCore,
      ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ,E)] using h
  have hbase : (extChartAt 𝓘(ℝ,E) q) x =
      chartTransition (I := 𝓘(ℝ,E)) p q y := rfl
  apply Prod.ext
  · change (extChartAt 𝓘(ℝ,E) q) x =
      chartTransition (I := 𝓘(ℝ,E)) p q y
    exact hbase
  · change Z.coordChange (Z.indexAt x) (achart E q) x
      (Z.coordChange (achart E p) (Z.indexAt x) x s) =
      Z.coordChange (achart E p) (achart E q) x s
    exact Z.coordChange_comp (achart E p) (Z.indexAt x) (achart E q)
      x ⟨⟨hp,Z.mem_baseSet_at x⟩,hq⟩ s
end
end QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
