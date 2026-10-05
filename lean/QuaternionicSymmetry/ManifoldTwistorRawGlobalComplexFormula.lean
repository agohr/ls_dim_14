import QuaternionicSymmetry.ManifoldTwistorPreferredRawInverse
import QuaternionicSymmetry.ManifoldTwistorLocalAlmostComplex

/-! A coordinate-only formula for the genuine global twistor almost-complex
operator. The metric enters solely through its local operator; the outer
preferred sphere-tangent conjugation is independent of that metric. -/

namespace QuaternionicSymmetry.ManifoldTwistorRawGlobalComplexFormula
open ManifoldTwistorPreferredRawCoordinates
open ManifoldTwistorGlobalAlmostComplex
open ManifoldTwistorSphereCore
open ManifoldTwistorCoefficientSphere
open ManifoldTwistorLocalAlmostComplex
open ManifoldTwistorVerticalComplex
open ManifoldQuaternionicConnection
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

def rawTwistorComplex (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (a : geometricSphere) :
    (E × EuclideanSpace ℝ (Fin 2)) →ₗ[ℝ]
      (E × EuclideanSpace ℝ (Fin 2)) :=
  (rawPreferredEquiv (E := E) a).symm.toLinearMap.comp
    ((localTwistorComplex Q D p y hy (coefficientSphereHomeomorph.symm a)).comp
      (rawPreferredEquiv (E := E) a).toLinearMap)

theorem tangentComplex_apply_raw (z : SphereBundleTotal Q)
    (v : E × EuclideanSpace ℝ (Fin 2)) :
    tangentComplex Q D z v =
      rawTwistorComplex Q D z.1 (extChartAt 𝓘(ℝ,E) z.1 z.1)
        ((extChartAt 𝓘(ℝ,E) z.1).map_source (mem_extChartAt_source z.1))
        z.2 v := by
  rfl

end
end QuaternionicSymmetry.ManifoldTwistorRawGlobalComplexFormula
