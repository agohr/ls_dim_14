import QuaternionicSymmetry.ManifoldQuaternionicInducedContactLineFiber
import QuaternionicSymmetry.ManifoldQuaternionicInducedComplexAtlas
import QuaternionicSymmetry.HolomorphicLineCorePullback
import QuaternionicSymmetry.ManifoldTwistorLeBrunHolomorphicContact
import QuaternionicSymmetry.ManifoldQuaternionicInducedContactComplexNaturality

/-! The actual ambient contact line restricted to an induced twistor
submanifold, and the fiber map from the intrinsic contact line. The map is
fixed by the differential and the contact forms, without choosing a gauge. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicInducedContactLinePullback
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicInducedTwistorMap
open ManifoldQuaternionicInducedContactLineFiber
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
/-- Pull back the actual ambient holomorphic line core along the proved
holomorphic induced twistor map. -/
def restrictedAmbientCore {m n : ℕ}
    (A : CompatibleComplexAtlas R.tangent DR m)
    (B : CompatibleComplexAtlas P.tangent DP n)
    (LP : HolomorphicContactLine P.tangent DP n B) :
    VectorBundleCore ℂ (SphereBundleTotal R.tangent) ℂ LP.Index := by
  letI := A.charts
  letI := B.charts
  exact HolomorphicLineCorePullback.pullbackCore LP.core
    (sphereTotalMap P R ι hι hR)
    (ManifoldQuaternionicInducedComplexAtlas.sphereTotalMap_mdifferentiable_complex
      P R ι hSmooth hι hR DP DR hTot A B).continuous

include hSmooth hTot in
instance restrictedAmbientCore_holomorphic {m n : ℕ}
    (A : CompatibleComplexAtlas R.tangent DR m)
    (B : CompatibleComplexAtlas P.tangent DP n)
    (LP : HolomorphicContactLine P.tangent DP n B) :
    letI := A.charts
    (restrictedAmbientCore P R ι hSmooth hι hR DP DR hTot A B LP).IsContMDiff
      𝓘(ℂ, ComplexTwistorModel m) ∞ := by
  letI := A.charts
  letI := B.charts
  letI := LP.holomorphic
  exact HolomorphicLineCorePullback.pullbackCore_isContMDiff
    𝓘(ℂ, ComplexTwistorModel n) 𝓘(ℂ, ComplexTwistorModel m)
    LP.core (sphereTotalMap P R ι hι hR)
    (ManifoldQuaternionicInducedComplexInfinity.sphereTotalMap_contMDiff_complex_infty
      P R ι hSmooth hι hR DP DR hTot A B)

include hSmooth hTot in
/-- The differential-defined fiber equivalence, now over the *same* base
as the intrinsic contact line, into the actual restricted core. -/
def restrictedContactLineFiberEquiv {m n : ℕ}
    (A : CompatibleComplexAtlas R.tangent DR m)
    (B : CompatibleComplexAtlas P.tangent DP n)
    (LR : HolomorphicContactLine R.tangent DR m A)
    (LP : HolomorphicContactLine P.tangent DP n B)
    (z : SphereBundleTotal R.tangent) :
    LR.core.Fiber z ≃ₗ[ℂ]
      (restrictedAmbientCore P R ι hSmooth hι hR DP DR hTot A B LP).Fiber z :=
  contactLineFiberEquivInduced P R ι hSmooth hι hR DP DR A B LR LP z

include hSmooth hTot in
/-- The square of actual holomorphic contact-form total maps and the
induced twistor tangent map commutes pointwise. This is the equation used
to obtain the local holomorphic gauge by a nonzero local contact section. -/
theorem contactFormTotal_induced_naturality {m n : ℕ}
    (A : CompatibleComplexAtlas R.tangent DR m)
    (B : CompatibleComplexAtlas P.tangent DP n)
    (LR : HolomorphicContactLine R.tangent DR m A)
    (LP : HolomorphicContactLine P.tangent DP n B)
    (z : SphereBundleTotal R.tangent) (v : ComplexTwistorModel m) :
    letI := A.charts
    letI := B.charts
    LP.contactFormTotal P.tangent DP
      (tangentMap 𝓘(ℂ,ComplexTwistorModel m)
        𝓘(ℂ,ComplexTwistorModel n)
        (sphereTotalMap P R ι hι hR)
        (⟨z,v⟩ : TangentBundle 𝓘(ℂ,ComplexTwistorModel m)
          (SphereBundleTotal R.tangent))) =
      (⟨sphereTotalMap P R ι hι hR z,
        restrictedContactLineFiberEquiv P R ι hSmooth hι hR DP DR hTot
          A B LR LP z
          (LR.contactFormTotal R.tangent DR
            (⟨z,v⟩ : TangentBundle 𝓘(ℂ,ComplexTwistorModel m)
              (SphereBundleTotal R.tangent))).2⟩ :
        Bundle.TotalSpace ℂ LP.core.Fiber) := by
  letI := A.charts
  letI := B.charts
  apply Bundle.TotalSpace.ext
  · rfl
  apply heq_of_eq
  exact ManifoldQuaternionicInducedContactComplexNaturality.contactLineFiberEquiv_contactFormComplex
    P R ι hSmooth hι hR DP DR hTot A B LR LP z v

end
end QuaternionicSymmetry.ManifoldQuaternionicInducedContactLinePullback
