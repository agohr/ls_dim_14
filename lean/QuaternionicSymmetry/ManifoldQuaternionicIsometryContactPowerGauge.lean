import QuaternionicSymmetry.HolomorphicLineGaugePowers
import QuaternionicSymmetry.ManifoldQuaternionicIsometryContactGauge
import QuaternionicSymmetry.HolomorphicLineTensorPowerClasses

/-! Actual quaternionic isometries give holomorphic gauges for every
contact-line tensor power, over the actual holomorphic twistor lift.
-/

namespace QuaternionicSymmetry.ManifoldQuaternionicIsometryContactPowerGauge

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicIsometryContactGauge
open ManifoldQuaternionicIsometryComplexInfinity
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorLineCoreClasses
open ManifoldTwistorSphereCore
open HolomorphicLineCorePullback
open HolomorphicLineTensorPowerClasses
open HolomorphicLinePowers
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

/-- The literal pullback of the contact power by the actual isometry lift. -/
def pulledContactPower
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (L : HolomorphicContactLine Q D n B)
    (f : QuaternionicIsometries Q) (k : ℕ) :
    letI := B.charts
    HolomorphicLineCoreClasses.LineCore.{0}
      (B := SphereBundleTotal Q) 𝓘(ℂ,ComplexTwistorModel n) := by
  letI := B.charts
  exact pullbackLineCore 𝓘(ℂ,ComplexTwistorModel n) 𝓘(ℂ,ComplexTwistorModel n)
    (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D L) k)
    (sphereTotalMap Q f) (sphereTotalMap_contMDiff_complex_infty Q D B f)

/-- Powering the genuine contact gauge gives an all-overlap holomorphic
gauge to the literal pulled-back power. This is not an assumption of
linearization or a claim about a symmetric power of the section space. -/
def contactPowerGauge
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B)
    (f : QuaternionicIsometries Q) (k : ℕ) :
    letI := B.charts
    letI := B.complexManifold
    letI := C.line.powerCore_holomorphic Q D k
    letI := (pulledContactPower Q D B C.line f k).holomorphic
    HolomorphicLineGauge.GaugeIso (IB := 𝓘(ℂ,ComplexTwistorModel n))
      (C.line.powerCore Q D k) (pulledContactPower Q D B C.line f k).core := by
  letI := B.charts
  letI := B.complexManifold
  letI := C.line.holomorphic
  letI := (pulledContactLine Q D B C.line f).holomorphic
  exact (contactGauge Q D B C f).power k

end
end QuaternionicSymmetry.ManifoldQuaternionicIsometryContactPowerGauge
