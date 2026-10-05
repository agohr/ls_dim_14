import QuaternionicSymmetry.ManifoldQuaternionicHomothetyTwistorHomeomorph
import QuaternionicSymmetry.ManifoldTwistorSphereManifold
import Mathlib.Geometry.Manifold.Diffeomorph

/-! Smooth identity transport for twistor bundle cores. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicHomothetyTwistorSmooth
open ManifoldQuaternionicHomothetyReduction ManifoldQuaternionicHomothetyTwistorCore
open ManifoldTwistorSphereCore ManifoldTwistorCoefficientSphere
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

private def coreChartedSpace (Z : FiberBundleCore (atlas E M) M geometricSphere) :
    ChartedSpace (ModelProd E (EuclideanSpace ℝ (Fin 2))) Z.TotalSpace := by
  letI : TopologicalSpace Z.TotalSpace := Z.toTopologicalSpace
  letI : FiberBundle geometricSphere Z.Fiber := Z.fiberBundle
  letI : ChartedSpace (M × geometricSphere) Z.TotalSpace := FiberBundle.chartedSpace'
  letI : ChartedSpace (ModelProd E geometricSphere) Z.TotalSpace := inferInstance
  letI : ChartedSpace (ModelProd E (EuclideanSpace ℝ (Fin 2)))
      (M × geometricSphere) := inferInstance
  exact ChartedSpace.comp _ (M × geometricSphere) _

variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

private theorem coreChartedSpace_sphere :
    coreChartedSpace (sphereCore Q) =
      (inferInstance : ChartedSpace (ModelProd E (EuclideanSpace ℝ (Fin 2)))
        (SphereBundleTotal Q)) := rfl

omit [InnerProductSpace ℝ E] [Nontrivial E] [FiniteDimensional ℝ E]
  [IsManifold 𝓘(ℝ,E) ∞ M] in
private theorem coreChartedSpace_transport
    (Z W : FiberBundleCore (atlas E M) M geometricSphere) (h : Z = W) :
    h ▸ coreChartedSpace Z = coreChartedSpace W := by
  cases h
  rfl

private def coreDiffeomorph
    (Z W : FiberBundleCore (atlas E M) M geometricSphere) (h : Z = W) :
    @Diffeomorph ℝ _
      (E × EuclideanSpace ℝ (Fin 2)) _ _
      (E × EuclideanSpace ℝ (Fin 2)) _ _
      (ModelProd E (EuclideanSpace ℝ (Fin 2))) _
      (ModelProd E (EuclideanSpace ℝ (Fin 2))) _
      ((𝓘(ℝ,E)).prod (𝓡 2)) ((𝓘(ℝ,E)).prod (𝓡 2))
      W.TotalSpace W.toTopologicalSpace (coreChartedSpace W)
      Z.TotalSpace Z.toTopologicalSpace (coreChartedSpace Z) ∞ := by
  letI : TopologicalSpace W.TotalSpace := W.toTopologicalSpace
  letI : ChartedSpace (ModelProd E (EuclideanSpace ℝ (Fin 2)))
      W.TotalSpace := coreChartedSpace W
  letI : TopologicalSpace Z.TotalSpace := Z.toTopologicalSpace
  letI : ChartedSpace (ModelProd E (EuclideanSpace ℝ (Fin 2)))
      Z.TotalSpace := coreChartedSpace Z
  refine { toEquiv := Equiv.refl _, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · cases h
    letI : TopologicalSpace Z.TotalSpace := Z.toTopologicalSpace
    letI : ChartedSpace (ModelProd E (EuclideanSpace ℝ (Fin 2)))
      Z.TotalSpace := coreChartedSpace Z
    exact contMDiff_id
  · cases h
    letI : TopologicalSpace Z.TotalSpace := Z.toTopologicalSpace
    letI : ChartedSpace (ModelProd E (EuclideanSpace ℝ (Fin 2)))
      Z.TotalSpace := coreChartedSpace Z
    exact contMDiff_id

omit [Nontrivial E] [FiniteDimensional ℝ E]
  [IsManifold 𝓘(ℝ,E) ∞ M] in
private theorem coreDiffeomorph_apply
    (Z W : FiberBundleCore (atlas E M) M geometricSphere) (h : Z = W)
    (z : W.TotalSpace) : coreDiffeomorph Z W h z = z := rfl


omit [InnerProductSpace ℝ E] [Nontrivial E] [FiniteDimensional ℝ E]
  [IsManifold 𝓘(ℝ,E) ∞ M] in
private theorem coreTopology_transport
    (Z W : FiberBundleCore (atlas E M) M geometricSphere) (h : Z = W) :
    Z.toTopologicalSpace = W.toTopologicalSpace := by
  cases h
  rfl

/-- The identity on the common base and sphere coordinates is a smooth
diffeomorphism between the actual twistor total spaces. -/
def sphereTotalDiffeomorph (s : ℝ) (hs : s ≠ 0) :
    Diffeomorph ((𝓘(ℝ,E)).prod (𝓡 2)) ((𝓘(ℝ,E)).prod (𝓡 2))
      (SphereBundleTotal (rescaleMetric Q s hs)) (SphereBundleTotal Q) ∞ := by
  exact coreDiffeomorph (sphereCore Q) (sphereCore (rescaleMetric Q s hs))
    (sphereCore_rescale Q s hs).symm

theorem sphereTotalDiffeomorph_apply (s : ℝ) (hs : s ≠ 0)
    (z : SphereBundleTotal (rescaleMetric Q s hs)) :
    sphereTotalDiffeomorph Q s hs z = z :=
  coreDiffeomorph_apply (sphereCore Q) (sphereCore (rescaleMetric Q s hs))
    (sphereCore_rescale Q s hs).symm z

theorem sphereTotalDiffeomorph_proj (s : ℝ) (hs : s ≠ 0)
    (z : SphereBundleTotal (rescaleMetric Q s hs)) :
    (sphereTotalDiffeomorph Q s hs z).1 = z.1 := by
  rw [sphereTotalDiffeomorph_apply]


end
end QuaternionicSymmetry.ManifoldQuaternionicHomothetyTwistorSmooth
