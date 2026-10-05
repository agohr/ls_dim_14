import QuaternionicSymmetry.ManifoldQuaternionicIsometryContactPowerGauge
import QuaternionicSymmetry.HolomorphicLineGaugeSections
import QuaternionicSymmetry.HolomorphicLineCorePullbackEquivSections

/-! Actual isometries act by complex-linear equivalences on all sections
of each contact-line tensor power. This uses the entire section space, not
the possibly smaller span of products of degree-one sections.
-/

namespace QuaternionicSymmetry.ManifoldQuaternionicIsometryContactPowerSections

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicIsometryContactFiberEquiv
open ManifoldQuaternionicIsometryContactGauge
open ManifoldQuaternionicIsometryContactPowerGauge
open ManifoldQuaternionicIsometryComplexInfinity
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorLineCoreClasses
open ManifoldTwistorSphereCore
open HolomorphicLineCorePullback
open HolomorphicLineTensorPowerClasses
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

/-- In the actual preferred source and target fibers, the constructed
gauge scalar is precisely the genuine contact differential evaluated at one. -/
theorem contactGauge_preferred
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B)
    (f : QuaternionicIsometries Q) (z : SphereBundleTotal Q) :
    letI := B.charts
    letI := B.complexManifold
    letI := C.line.holomorphic
    letI := (pulledContactLine Q D B C.line f).holomorphic
    (contactGauge Q D B C f).forward (C.line.core.indexAt z)
      (C.line.core.indexAt (sphereTotalMap Q f z)) z =
        (show ℂ from contactLineFiberEquiv Q D C.line f z (1 : ℂ)) := by
  letI := B.charts
  letI := B.complexManifold
  letI := C.line.holomorphic
  let P := pulledContactLine Q D B C.line f
  letI := P.holomorphic
  change P.core.coordChange (P.core.indexAt z) (P.core.indexAt z) z
      (contactLineFiberEquiv Q D C.line f z
        (C.line.core.coordChange (C.line.core.indexAt z) (C.line.core.indexAt z) z 1)) = _
  rw [C.line.core.coordChange_self _ z (C.line.core.mem_baseSet_at z),
    P.core.coordChange_self _ z (P.core.mem_baseSet_at z)]

/-- Tensor-power gauge transport followed by inverse biholomorphic
pullback gives an equivalence of complete global section spaces. -/
def contactPowerSectionEquiv
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B)
    (f : QuaternionicIsometries Q) (k : ℕ) :
    letI := B.charts
    GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
      (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line) k) ≃ₗ[ℂ]
    GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
      (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line) k) := by
  letI := B.charts
  letI := B.complexManifold
  let IB := 𝓘(ℂ,ComplexTwistorModel n)
  let L := powerCoreRep IB (contactLineCore Q D C.line) k
  let P := pulledContactPower Q D B C.line f k
  letI := L.holomorphic
  letI := P.holomorphic
  let Φ : SphereBundleTotal Q ≃ SphereBundleTotal Q := MulAction.toPerm f
  have hΦ : ContMDiff IB IB ∞ Φ := sphereTotalMap_contMDiff_complex_infty Q D B f
  have hΨ : ContMDiff IB IB ∞ Φ.symm := sphereTotalMap_contMDiff_complex_infty Q D B f⁻¹
  let gauge := HolomorphicLineGaugeSections.sectionLinearEquiv IB L P
    (contactPowerGauge Q D B C f k)
  exact gauge.trans
    (HolomorphicLineCorePullbackEquivSections.sectionLinearEquiv IB L Φ hΦ hΨ).symm

/-- The action on every section of the tensor power has the expected
pointwise formula with the actual contact differential's scalar to power k. -/
theorem contactPowerSectionEquiv_apply_at_image
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B)
    (f : QuaternionicIsometries Q) (k : ℕ)
    (s : letI := B.charts
      GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line) k))
    (z : SphereBundleTotal Q) :
    letI := B.charts
    (contactPowerSectionEquiv Q D B C f k s) (sphereTotalMap Q f z) =
      (show ℂ from contactLineFiberEquiv Q D C.line f z (1 : ℂ)) ^ k *
        (show ℂ from s z) := by
  letI := B.charts
  letI := B.complexManifold
  letI := C.line.holomorphic
  letI := (pulledContactLine Q D B C.line f).holomorphic
  let IB := 𝓘(ℂ,ComplexTwistorModel n)
  let L := powerCoreRep IB (contactLineCore Q D C.line) k
  let P := pulledContactPower Q D B C.line f k
  letI := L.holomorphic
  letI := P.holomorphic
  let Φ : SphereBundleTotal Q ≃ SphereBundleTotal Q := MulAction.toPerm f
  have hΦ : ContMDiff IB IB ∞ Φ := sphereTotalMap_contMDiff_complex_infty Q D B f
  have hΨ : ContMDiff IB IB ∞ Φ.symm := sphereTotalMap_contMDiff_complex_infty Q D B f⁻¹
  let gauge := HolomorphicLineGaugeSections.sectionLinearEquiv IB L P
    (contactPowerGauge Q D B C f k)
  have h := HolomorphicLineCorePullbackEquivSections.sectionLinearEquiv_symm_apply_at_image
    IB L Φ hΦ hΨ (gauge s) z
  change (contactPowerSectionEquiv Q D B C f k s) (sphereTotalMap Q f z) =
    (contactGauge Q D B C f).forward (C.line.core.indexAt z)
      (C.line.core.indexAt (sphereTotalMap Q f z)) z ^ k * (show ℂ from s z) at h
  rw [contactGauge_preferred Q D B C f z] at h
  exact h

end
end QuaternionicSymmetry.ManifoldQuaternionicIsometryContactPowerSections
