import QuaternionicSymmetry.ManifoldTwistorLocalAlmostComplexOverlap
import QuaternionicSymmetry.ManifoldTwistorVerticalTangent
import QuaternionicSymmetry.ManifoldTwistorSphereManifold

/-! A pointwise almost complex operator on the tangent spaces of the genuine
smooth twistor sphere total space. The preferred bundle trivialization uses
the base chart at the point; the coefficient of its sphere coordinate is
identified with the actual sphere tangent through the inclusion derivative.
Smooth dependence and integrability require separate proofs. -/

namespace QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex

open QuaternionicSymmetry.ManifoldTwistorSphereBundle
open QuaternionicSymmetry.ManifoldTwistorSphereCore
open QuaternionicSymmetry.ManifoldTwistorSphereManifold
open QuaternionicSymmetry.ManifoldTwistorCoefficientSphere
open QuaternionicSymmetry.ManifoldTwistorVerticalComplex
open QuaternionicSymmetry.ManifoldTwistorLocalAlmostComplex
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open QuaternionicSymmetry.ManifoldQuaternionicConnection
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : CompatibleTangentConnection Q)

private abbrev productModel := (𝓘(ℝ,E)).prod (𝓡 2)


private def preferredCoefficient (z : SphereBundleTotal Q) : coefficientSphere :=
  coefficientSphereHomeomorph.symm z.2

private theorem preferred_localTriv (z : SphereBundleTotal Q) :
    ((sphereCore Q).localTriv (achart E z.1) z).2 = z.2 := by
  rw [(sphereCore Q).localTriv_apply]
  change euclideanSphereCoordChange Q (achart E z.1) (achart E z.1) z.1 z.2 = z.2
  exact euclideanSphereCoordChange_self Q (achart E z.1) z.1
    (mem_chart_source E z.1) z.2

/-- The actual total-space tangent model, in the preferred bundle chart at
the base point, converted from the sphere tangent to the dot-orthogonal
coefficient plane. -/
def preferredTangentEquiv (z : SphereBundleTotal Q) :
    TangentSpace (productModel (E := E)) z ≃ₗ[ℝ]
      E × verticalSubmodule (preferredCoefficient Q z) :=
  LinearEquiv.prodCongr (LinearEquiv.refl ℝ E)
    (sphereTangentVerticalEquiv (preferredCoefficient Q z))

private theorem preferredTarget (z : SphereBundleTotal Q) :
    (extChartAt 𝓘(ℝ,E) z.1 z.1) ∈
      (extChartAt 𝓘(ℝ,E) z.1).target :=
  (extChartAt 𝓘(ℝ,E) z.1).map_source (mem_extChartAt_source z.1)

/-- The pointwise twistor operator on the genuine tangent fiber of the
associated smooth sphere-bundle total space. -/
def tangentComplex (z : SphereBundleTotal Q) :
    TangentSpace (productModel (E := E)) z →ₗ[ℝ]
      TangentSpace (productModel (E := E)) z :=
  (preferredTangentEquiv Q z).symm.toLinearMap.comp
    ((localTwistorComplex Q D z.1
      (extChartAt 𝓘(ℝ,E) z.1 z.1)
      (preferredTarget Q z) (preferredCoefficient Q z)).comp
      (preferredTangentEquiv Q z).toLinearMap)

theorem tangentComplex_sq (z : SphereBundleTotal Q)
    (v : TangentSpace (productModel (E := E)) z) :
    tangentComplex Q D z (tangentComplex Q D z v) = -v := by
  simp [tangentComplex, localTwistorComplex_sq]

end
end QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
