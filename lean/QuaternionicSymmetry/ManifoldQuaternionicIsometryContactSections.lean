import QuaternionicSymmetry.ManifoldQuaternionicIsometryContactGauge
import QuaternionicSymmetry.HolomorphicLineCorePullbackEquivSections
import QuaternionicSymmetry.HolomorphicLineGaugeSectionEquiv
import QuaternionicSymmetry.ManifoldQuaternionicTwistorIsometryDiffeomorph

/-! Each actual quaternionic isometry acts complex-linearly and invertibly
on all global holomorphic sections of its genuine contact line. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicIsometryContactSections

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicIsometryContactFiberEquiv
open ManifoldQuaternionicIsometryContactGauge
open ManifoldQuaternionicTwistorIsometryDiffeomorph
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorLineCoreClasses
open ManifoldTwistorSphereCore
open HolomorphicLineCorePullback
open HolomorphicLineGaugeSectionEquiv
open HolomorphicLineCorePullbackEquivSections
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

local instance : Fact (Module.finrank ℝ
    ManifoldTwistorCoefficientSphere.EuclideanThree = 2 + 1) := ⟨by simp⟩
local instance (x : M) : ChartedSpace (EuclideanSpace ℝ (Fin 2))
    ((sphereCore Q).Fiber x) := by
  change ChartedSpace (EuclideanSpace ℝ (Fin 2))
    ManifoldTwistorCoefficientSphere.geometricSphere
  infer_instance

/-- The holomorphic contact gauge and the biholomorphic pullback give an
actual complex-linear equivalence on the full global section space. -/
def contactSectionEquiv
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B)
    (f : QuaternionicIsometries Q) :
    letI := B.charts
    GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
      (contactLineCore Q D C.line) ≃ₗ[ℂ]
    GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
      (contactLineCore Q D C.line) := by
  letI := B.charts
  letI := B.complexManifold
  letI := C.line.holomorphic
  letI := (pulledContactLine Q D B C.line f).holomorphic
  let IB := 𝓘(ℂ,ComplexTwistorModel n)
  let L := contactLineCore Q D C.line
  let P := pulledContactLine Q D B C.line f
  have hΦ : ContMDiff IB IB ∞ (sphereTotalMap Q f) :=
    ManifoldQuaternionicIsometryComplexInfinity.sphereTotalMap_contMDiff_complex_infty
      Q D B f
  have hΨ : ContMDiff IB IB ∞ (sphereTotalMap Q f⁻¹) :=
    ManifoldQuaternionicIsometryComplexInfinity.sphereTotalMap_contMDiff_complex_infty
      Q D B f⁻¹
  let Φ : SphereBundleTotal Q ≃ SphereBundleTotal Q := MulAction.toPerm f
  let gauge : GlobalSections IB L ≃ₗ[ℂ] GlobalSections IB P :=
    sectionLinearEquivOfLocalWitness IB L P
      (contactLineFiberEquiv Q D C.line f)
      (hasLocalHolomorphicWitness Q D B C f)
  let pullback : GlobalSections IB L ≃ₗ[ℂ] GlobalSections IB P :=
    sectionLinearEquiv IB L Φ hΦ hΨ
  exact gauge.trans pullback.symm

/-- At the image of a point, the global section action is exactly the
derivative-defined map on the actual contact-line fiber. -/
theorem contactSectionEquiv_apply_at_image
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B)
    (f : QuaternionicIsometries Q)
    (s : letI := B.charts
      GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore Q D C.line)) (z : SphereBundleTotal Q) :
    letI := B.charts
    (contactSectionEquiv Q D B C f s) (sphereTotalMap Q f z) =
      contactLineFiberEquiv Q D C.line f z (s z) := by
  letI := B.charts
  letI := B.complexManifold
  letI := C.line.holomorphic
  letI := (pulledContactLine Q D B C.line f).holomorphic
  let IB := 𝓘(ℂ,ComplexTwistorModel n)
  let L := contactLineCore Q D C.line
  let P := pulledContactLine Q D B C.line f
  have hΦ : ContMDiff IB IB ∞ (sphereTotalMap Q f) :=
    ManifoldQuaternionicIsometryComplexInfinity.sphereTotalMap_contMDiff_complex_infty
      Q D B f
  have hΨ : ContMDiff IB IB ∞ (sphereTotalMap Q f⁻¹) :=
    ManifoldQuaternionicIsometryComplexInfinity.sphereTotalMap_contMDiff_complex_infty
      Q D B f⁻¹
  let Φ : SphereBundleTotal Q ≃ SphereBundleTotal Q := MulAction.toPerm f
  let gauge : GlobalSections IB L ≃ₗ[ℂ] GlobalSections IB P :=
    sectionLinearEquivOfLocalWitness IB L P
      (contactLineFiberEquiv Q D C.line f)
      (hasLocalHolomorphicWitness Q D B C f)
  have h := sectionLinearEquiv_symm_apply_at_image IB L Φ hΦ hΨ (gauge s) z
  change (contactSectionEquiv Q D B C f s) (sphereTotalMap Q f z) =
    contactLineFiberEquiv Q D C.line f z (s z) at h
  exact h

end
end QuaternionicSymmetry.ManifoldQuaternionicIsometryContactSections
