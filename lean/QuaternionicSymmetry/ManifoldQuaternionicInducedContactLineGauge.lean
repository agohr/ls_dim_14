import QuaternionicSymmetry.ManifoldQuaternionicInducedContactGaugeWitness

/-! The actual induced twistor immersion identifies its intrinsic
holomorphic contact line with the ambient holomorphic contact line pulled
back to the source, as an all-overlap holomorphic line-core gauge. This is
proved from contact-form holomorphicity, quotient naturality, and local
nonzero contact sections; it is not an extra source premise. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicInducedContactLineGauge
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicInducedContactLinePullback
open ManifoldQuaternionicInducedContactGaugeWitness
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section

variable {E F M N : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [FiniteDimensional ℝ F] [Nontrivial F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
variable (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
  (R : PositiveQuaternionicKahlerGeometry (E := F) (M := N))
  (ι : N → M)
  (hSmooth : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ ι)
  (hι : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x))
  (hR : IsInducedQuaternionicGeometry P R ι)
  (DP : ManifoldQuaternionicConnection.CompatibleTangentConnection P.tangent)
  (DR : ManifoldQuaternionicConnection.CompatibleTangentConnection R.tangent)
  (hTot : ManifoldQuaternionicInducedTotalGeodesy.IsTotallyGeodesic P R ι DP DR)

local instance : Fact (Module.finrank ℝ ManifoldTwistorCoefficientSphere.EuclideanThree = 2 + 1) :=
  ⟨by simp⟩
local instance (x : N) : ChartedSpace (EuclideanSpace ℝ (Fin 2))
    ((sphereCore R.tangent).Fiber x) := by
  change ChartedSpace (EuclideanSpace ℝ (Fin 2))
    ManifoldTwistorCoefficientSphere.geometricSphere
  infer_instance

include hSmooth hTot in
/-- Genuine holomorphic contact-line identification over the actual
induced twistor map, valid on every overlap of the two line-core covers. -/
def actualInducedContactLineGauge {m n : ℕ}
    (A : CompatibleComplexAtlas R.tangent DR m)
    (B : CompatibleComplexAtlas P.tangent DP n)
    (CR : HolomorphicContactData R.tangent DR m A)
    (CP : HolomorphicContactData P.tangent DP n B) :
    letI := A.charts
    letI := B.charts
    letI := A.complexManifold
    letI := B.complexManifold
    letI := CR.line.holomorphic
    letI := restrictedAmbientCore_holomorphic P R ι hSmooth hι hR DP DR hTot A B CP.line
    HolomorphicLineGauge.GaugeIso (IB := 𝓘(ℂ,ComplexTwistorModel m))
      CR.line.core
      (restrictedAmbientCore P R ι hSmooth hι hR DP DR hTot A B CP.line) := by
  letI := A.charts
  letI := B.charts
  letI := A.complexManifold
  letI := B.complexManifold
  letI := CR.line.holomorphic
  letI := restrictedAmbientCore_holomorphic P R ι hSmooth hι hR DP DR hTot A B CP.line
  exact HolomorphicLineLocalGaugeRatio.gaugeIsoOfLocalWitness
    𝓘(ℂ,ComplexTwistorModel m) CR.line.core
    (restrictedAmbientCore P R ι hSmooth hι hR DP DR hTot A B CP.line)
    (restrictedContactLineFiberEquiv P R ι hSmooth hι hR DP DR hTot
      A B CR.line CP.line)
    (actual_hasLocalHolomorphicWitness P R ι hSmooth hι hR DP DR hTot A B CR CP)

end
end QuaternionicSymmetry.ManifoldQuaternionicInducedContactLineGauge
