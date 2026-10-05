import QuaternionicSymmetry.ManifoldQuaternionicInducedContactGaugeWitness
import QuaternionicSymmetry.HolomorphicLineGaugeSectionEquiv

/-! The actual holomorphic contact-line comparison induces an explicit
complex-linear equivalence of global holomorphic section spaces. The
restricted target space contains *all* holomorphic sections of the
pullback line, not just restrictions of ambient global sections. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicInducedContactSections
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicInducedContactLinePullback
open ManifoldQuaternionicInducedContactGaugeWitness
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorSphereCore
open HolomorphicLineCoreClasses
open HolomorphicLineCorePullback
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
/-- Actual global holomorphic sections of the intrinsic contact line are
linearly equivalent to *all* sections of the genuinely pulled-back ambient
contact line. -/
def actualInducedContactSectionLinearEquiv {m n : ℕ}
    (A : CompatibleComplexAtlas R.tangent DR m)
    (B : CompatibleComplexAtlas P.tangent DP n)
    (CR : HolomorphicContactData R.tangent DR m A)
    (CP : HolomorphicContactData P.tangent DP n B) :
    letI := A.charts
    letI := B.charts
    letI := A.complexManifold
    letI := B.complexManifold
    GlobalSections 𝓘(ℂ,ComplexTwistorModel m)
      ({ Index := CR.line.Index, core := CR.line.core,
         holomorphic := CR.line.holomorphic } :
        LineCore.{0} 𝓘(ℂ,ComplexTwistorModel m)) ≃ₗ[ℂ]
    GlobalSections 𝓘(ℂ,ComplexTwistorModel m)
      ({ Index := CP.line.Index,
         core := restrictedAmbientCore P R ι hSmooth hι hR DP DR hTot A B CP.line,
         holomorphic := restrictedAmbientCore_holomorphic
           P R ι hSmooth hι hR DP DR hTot A B CP.line } :
        LineCore.{0} 𝓘(ℂ,ComplexTwistorModel m)) := by
  letI := A.charts
  letI := B.charts
  letI := A.complexManifold
  letI := B.complexManifold
  exact HolomorphicLineGaugeSectionEquiv.sectionLinearEquivOfLocalWitness
    𝓘(ℂ,ComplexTwistorModel m)
    ({ Index := CR.line.Index, core := CR.line.core,
       holomorphic := CR.line.holomorphic } :
      LineCore.{0} 𝓘(ℂ,ComplexTwistorModel m))
    ({ Index := CP.line.Index,
       core := restrictedAmbientCore P R ι hSmooth hι hR DP DR hTot A B CP.line,
       holomorphic := restrictedAmbientCore_holomorphic
         P R ι hSmooth hι hR DP DR hTot A B CP.line } :
      LineCore.{0} 𝓘(ℂ,ComplexTwistorModel m))
    (restrictedContactLineFiberEquiv P R ι hSmooth hι hR DP DR hTot
      A B CR.line CP.line)
    (actual_hasLocalHolomorphicWitness P R ι hSmooth hι hR DP DR hTot A B CR CP)

end
end QuaternionicSymmetry.ManifoldQuaternionicInducedContactSections
