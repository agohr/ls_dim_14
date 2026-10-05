import QuaternionicSymmetry.ManifoldQuaternionicInducedContactLineGauge
import QuaternionicSymmetry.HolomorphicLineCoreClasses

/-! The induced contact-line gauge identifies genuine represented
holomorphic line classes. This is a consequence of the constructed gauge,
not an additional classification or Picard-group source premise. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicInducedContactLineClass
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicInducedContactLinePullback
open ManifoldQuaternionicInducedContactLineGauge
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorSphereCore
open HolomorphicLineCoreClasses
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
theorem intrinsic_contactLine_isomorphic_restricted_ambient {m n : ℕ}
    (A : CompatibleComplexAtlas R.tangent DR m)
    (B : CompatibleComplexAtlas P.tangent DP n)
    (CR : HolomorphicContactData R.tangent DR m A)
    (CP : HolomorphicContactData P.tangent DP n B) :
    letI := A.charts
    letI := B.charts
    letI := A.complexManifold
    letI := B.complexManifold
    Isomorphic 𝓘(ℂ,ComplexTwistorModel m)
      ({ Index := CR.line.Index, core := CR.line.core,
         holomorphic := CR.line.holomorphic } :
        LineCore.{0} 𝓘(ℂ,ComplexTwistorModel m))
      ({ Index := CP.line.Index,
         core := restrictedAmbientCore P R ι hSmooth hι hR DP DR hTot A B CP.line,
         holomorphic := restrictedAmbientCore_holomorphic
           P R ι hSmooth hι hR DP DR hTot A B CP.line } :
        LineCore.{0} 𝓘(ℂ,ComplexTwistorModel m)) := by
  letI := A.charts
  letI := B.charts
  letI := A.complexManifold
  letI := B.complexManifold
  exact ⟨actualInducedContactLineGauge
    P R ι hSmooth hι hR DP DR hTot A B CR CP⟩

end
end QuaternionicSymmetry.ManifoldQuaternionicInducedContactLineClass
