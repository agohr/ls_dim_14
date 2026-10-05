import QuaternionicSymmetry.ManifoldQuaternionicInducedComplexInfinity
import QuaternionicSymmetry.ManifoldTwistorLeBrunHolomorphicLine

/-! The actual holomorphic induced twistor immersion restricts the ambient
contact-horizontal distribution to the intrinsic one. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicInducedContactRestriction
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicInducedTwistorMap
open ManifoldQuaternionicInducedCoefficientMap
open ManifoldQuaternionicInducedSplitDerivative
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorSphereCore
open ManifoldTwistorGlobalAlmostComplex
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

private abbrev JF := 𝓘(ℝ,F).prod (𝓡 2)
private abbrev JE := 𝓘(ℝ,E).prod (𝓡 2)
local instance : Fact (Module.finrank ℝ ManifoldTwistorCoefficientSphere.EuclideanThree = 2 + 1) :=
  ⟨by simp⟩
local instance (x : N) : ChartedSpace (EuclideanSpace ℝ (Fin 2))
    ((sphereCore R.tangent).Fiber x) := by
  change ChartedSpace (EuclideanSpace ℝ (Fin 2))
    ManifoldTwistorCoefficientSphere.geometricSphere
  infer_instance

include hSmooth hTot in
theorem induced_contact_horizontal_restriction
    {m n : ℕ}
    (A : CompatibleComplexAtlas R.tangent DR m)
    (B : CompatibleComplexAtlas P.tangent DP n)
    (LR : HolomorphicContactLine R.tangent DR m A)
    (LP : HolomorphicContactLine P.tangent DP n B)
    (z : SphereBundleTotal R.tangent)
    (t : TangentSpace (JF (F := F)) z)
    (ht : LR.contactFormReal R.tangent DR z t = 0) :
    LP.contactFormReal P.tangent DP
      (sphereTotalMap P R ι hι hR z)
      (mfderiv (JF (F := F)) (JE (E := E))
        (sphereTotalMap P R ι hι hR) z t) = 0 := by
  have hh : t ∈ horizontalTangentSubmodule R.tangent DR z := by
    rw [← LR.contactFormReal_ker R.tangent DR z]
    exact ht
  have ht' := sphereTotalMap_mfderiv_preserves_horizontal
    P R ι hSmooth hι hR DP DR hTot z t hh
  rw [← LP.contactFormReal_ker P.tangent DP
    (sphereTotalMap P R ι hι hR z)] at ht'
  exact ht'

include hSmooth hTot in
/-- The ambient contact plane pulls back to exactly the intrinsic contact
plane; the reverse implication uses faithfulness of the actual induced
rank-three coefficient isometry. -/
theorem induced_contact_horizontal_iff
    (z : SphereBundleTotal R.tangent)
    (t : TangentSpace (JF (F := F)) z) :
    mfderiv (JF (F := F)) (JE (E := E))
      (sphereTotalMap P R ι hι hR) z t ∈
        horizontalTangentSubmodule P.tangent DP
          (sphereTotalMap P R ι hι hR z) ↔
      t ∈ horizontalTangentSubmodule R.tangent DR z := by
  constructor
  · intro hp
    have hp0 := (mem_horizontalTangentSubmodule_iff P.tangent DP
      (sphereTotalMap P R ι hι hR z) _).mp hp
    have hcoeff := connectionTangentEquiv_mfderiv_snd_coefficients
      P R ι hSmooth hι hR DP DR hTot z t
    rw [hp0] at hcoeff
    have hz : ((connectionTangentEquiv R.tangent DR z t).2).1 = 0 := by
      apply coefficientMap_injective P R ι hι hR z.1
      simpa using hcoeff.symm
    apply (mem_horizontalTangentSubmodule_iff R.tangent DR z t).mpr
    exact Subtype.ext hz
  · exact sphereTotalMap_mfderiv_preserves_horizontal
      P R ι hSmooth hι hR DP DR hTot z t

include hSmooth hTot in
theorem induced_contactForm_ker_iff
    {m n : ℕ}
    (A : CompatibleComplexAtlas R.tangent DR m)
    (B : CompatibleComplexAtlas P.tangent DP n)
    (LR : HolomorphicContactLine R.tangent DR m A)
    (LP : HolomorphicContactLine P.tangent DP n B)
    (z : SphereBundleTotal R.tangent)
    (t : TangentSpace (JF (F := F)) z) :
    LP.contactFormReal P.tangent DP
      (sphereTotalMap P R ι hι hR z)
      (mfderiv (JF (F := F)) (JE (E := E))
        (sphereTotalMap P R ι hι hR) z t) = 0 ↔
      LR.contactFormReal R.tangent DR z t = 0 := by
  rw [← LinearMap.mem_ker, LP.contactFormReal_ker,
    ← LinearMap.mem_ker, LR.contactFormReal_ker]
  exact induced_contact_horizontal_iff
    P R ι hSmooth hι hR DP DR hTot z t

end
end QuaternionicSymmetry.ManifoldQuaternionicInducedContactRestriction
