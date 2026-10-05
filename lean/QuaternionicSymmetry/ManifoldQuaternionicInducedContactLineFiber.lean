import QuaternionicSymmetry.ManifoldQuaternionicInducedContactRestriction
import QuaternionicSymmetry.ManifoldQuaternionicInducedVerticalComplex
import QuaternionicSymmetry.ManifoldTwistorContactQuotientComplex
import QuaternionicSymmetry.ManifoldTwistorVerticalComplexLine

/-! Fiberwise complex-linear contact-line comparison induced by the actual
holomorphic twistor immersion. Bundle-level holomorphic variation is a
separate issue, since LeBrun's quotientEquiv field is only pointwise. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicInducedContactLineFiber
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicInducedTwistorMap
open ManifoldQuaternionicInducedTwistorDerivative
open ManifoldQuaternionicInducedVerticalComplex
open ManifoldQuaternionicInducedSplitDerivative
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorGlobalAlmostComplex
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

local instance : Fact (Module.finrank ℝ ManifoldTwistorCoefficientSphere.EuclideanThree = 2 + 1) :=
  ⟨by simp⟩
local instance (x : N) : ChartedSpace (EuclideanSpace ℝ (Fin 2))
    ((sphereCore R.tangent).Fiber x) := by
  change ChartedSpace (EuclideanSpace ℝ (Fin 2))
    ManifoldTwistorCoefficientSphere.geometricSphere
  infer_instance

include hSmooth in
def actualVerticalDerivativeComplexEquiv
    (z : SphereBundleTotal R.tangent) :
    letI := verticalComplexModule R.tangent DR z
    letI := verticalComplexModule P.tangent DP
      (sphereTotalMap P R ι hι hR z)
    verticalTangentSubmodule R.tangent z ≃ₗ[ℂ]
      verticalTangentSubmodule P.tangent
        (sphereTotalMap P R ι hι hR z) := by
  letI := verticalComplexModule R.tangent DR z
  letI := verticalComplexModule P.tangent DP
    (sphereTotalMap P R ι hι hR z)
  letI : FiniteDimensional ℂ (verticalTangentSubmodule R.tangent z) :=
    FiniteDimensional.of_finrank_pos (by
      rw [verticalComplex_finrank R.tangent DR z]
      omega)
  letI : FiniteDimensional ℂ (verticalTangentSubmodule P.tangent
      (sphereTotalMap P R ι hι hR z)) :=
    FiniteDimensional.of_finrank_pos (by
      rw [verticalComplex_finrank P.tangent DP
        (sphereTotalMap P R ι hι hR z)]
      omega)
  let f := actualVerticalDerivativeComplex P R ι hSmooth hι hR DP DR z
  have hdim : Module.finrank ℂ (verticalTangentSubmodule R.tangent z) =
      Module.finrank ℂ (verticalTangentSubmodule P.tangent
        (sphereTotalMap P R ι hι hR z)) := by
    rw [verticalComplex_finrank R.tangent DR z,
      verticalComplex_finrank P.tangent DP
        (sphereTotalMap P R ι hι hR z)]
  have hinj : Function.Injective f :=
    actualVerticalDerivative_injective P R ι hSmooth hι hR z
  exact LinearEquiv.ofBijective f
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩

include hSmooth in
def contactQuotientComplexEquivInduced
    (z : SphereBundleTotal R.tangent) :
    letI := contactQuotientComplexModule R.tangent DR z
    letI := contactQuotientComplexModule P.tangent DP
      (sphereTotalMap P R ι hι hR z)
    (TangentSpace (𝓘(ℝ,F).prod (𝓡 2)) z ⧸
      horizontalTangentSubmodule R.tangent DR z) ≃ₗ[ℂ]
    (TangentSpace (𝓘(ℝ,E).prod (𝓡 2))
      (sphereTotalMap P R ι hι hR z) ⧸
      horizontalTangentSubmodule P.tangent DP
        (sphereTotalMap P R ι hι hR z)) := by
  letI := contactQuotientComplexModule R.tangent DR z
  letI := contactQuotientComplexModule P.tangent DP
    (sphereTotalMap P R ι hι hR z)
  letI := verticalComplexModule R.tangent DR z
  letI := verticalComplexModule P.tangent DP
    (sphereTotalMap P R ι hι hR z)
  exact (contactQuotientComplexEquiv R.tangent DR z).trans
    ((actualVerticalDerivativeComplexEquiv P R ι hSmooth hι hR DP DR z).trans
      (contactQuotientComplexEquiv P.tangent DP
        (sphereTotalMap P R ι hι hR z)).symm)

include hSmooth in
/-- The actual induced twistor immersion identifies source and restricted
ambient holomorphic-contact-line fibers as complex lines. Holomorphic
variation of this family is not implied by pointwise quotient equivalences
alone and is treated separately. -/
def contactLineFiberEquivInduced
    {m n : ℕ}
    (A : CompatibleComplexAtlas R.tangent DR m)
    (B : CompatibleComplexAtlas P.tangent DP n)
    (LR : HolomorphicContactLine R.tangent DR m A)
    (LP : HolomorphicContactLine P.tangent DP n B)
    (z : SphereBundleTotal R.tangent) :
    LR.core.Fiber z ≃ₗ[ℂ]
      LP.core.Fiber (sphereTotalMap P R ι hι hR z) := by
  letI := contactQuotientComplexModule R.tangent DR z
  letI := contactQuotientComplexModule P.tangent DP
    (sphereTotalMap P R ι hι hR z)
  exact (LR.quotientEquiv z).trans
    ((contactQuotientComplexEquivInduced P R ι hSmooth hι hR DP DR z).trans
      (LP.quotientEquiv (sphereTotalMap P R ι hι hR z)).symm)

include hSmooth in
/-- The actual differential descends to contact quotients, because the
horizontal preservation theorem has already been proved internally. -/
def actualContactQuotientDerivative
    (hTot : ManifoldQuaternionicInducedTotalGeodesy.IsTotallyGeodesic
      P R ι DP DR)
    (z : SphereBundleTotal R.tangent) :
    (TangentSpace (𝓘(ℝ,F).prod (𝓡 2)) z ⧸
      horizontalTangentSubmodule R.tangent DR z) →ₗ[ℝ]
    (TangentSpace (𝓘(ℝ,E).prod (𝓡 2))
      (sphereTotalMap P R ι hι hR z) ⧸
      horizontalTangentSubmodule P.tangent DP
        (sphereTotalMap P R ι hι hR z)) :=
  (horizontalTangentSubmodule R.tangent DR z).mapQ
    (horizontalTangentSubmodule P.tangent DP
      (sphereTotalMap P R ι hι hR z))
    (mfderiv (𝓘(ℝ,F).prod (𝓡 2)) (𝓘(ℝ,E).prod (𝓡 2))
      (sphereTotalMap P R ι hι hR) z)
    (by intro t ht
        exact sphereTotalMap_mfderiv_preserves_horizontal
          P R ι hSmooth hι hR DP DR hTot z t ht)

include hSmooth in
theorem actualContactQuotientDerivative_eq_complexEquiv
    (hTot : ManifoldQuaternionicInducedTotalGeodesy.IsTotallyGeodesic
      P R ι DP DR)
    (z : SphereBundleTotal R.tangent) :
    letI := contactQuotientComplexModule R.tangent DR z
    letI := contactQuotientComplexModule P.tangent DP
      (sphereTotalMap P R ι hι hR z)
    ∀ x, actualContactQuotientDerivative P R ι hSmooth hι hR DP DR hTot z x =
      contactQuotientComplexEquivInduced P R ι hSmooth hι hR DP DR z x := by
  letI := contactQuotientComplexModule R.tangent DR z
  letI := contactQuotientComplexModule P.tangent DP
    (sphereTotalMap P R ι hι hR z)
  letI := verticalComplexModule R.tangent DR z
  letI := verticalComplexModule P.tangent DP
    (sphereTotalMap P R ι hι hR z)
  intro x
  let v := contactQuotientEquiv R.tangent DR z x
  have hx : (Submodule.Quotient.mk v.1 :
      TangentSpace (𝓘(ℝ,F).prod (𝓡 2)) z ⧸
        horizontalTangentSubmodule R.tangent DR z) = x :=
    (contactQuotientEquiv R.tangent DR z).symm_apply_apply x
  rw [← hx]
  simp only [actualContactQuotientDerivative, Submodule.mapQ_apply,
    contactQuotientComplexEquivInduced, LinearEquiv.trans_apply]
  have hv : contactQuotientEquiv R.tangent DR z
      (Submodule.Quotient.mk v.1) = v :=
    (contactQuotientEquiv R.tangent DR z).apply_symm_apply v
  change contactQuotientComplexEquiv R.tangent DR z
    (Submodule.Quotient.mk v.1) = v at hv
  rw [hv]
  rfl

include hSmooth in
/-- Pointwise contact forms commute with the actual differential and the
constructed complex line-fiber equivalence. This is the precise algebraic
identity needed for holomorphic descent. -/
theorem contactLineFiberEquiv_contactFormReal
    {m n : ℕ}
    (A : CompatibleComplexAtlas R.tangent DR m)
    (B : CompatibleComplexAtlas P.tangent DP n)
    (LR : HolomorphicContactLine R.tangent DR m A)
    (LP : HolomorphicContactLine P.tangent DP n B)
    (hTot : ManifoldQuaternionicInducedTotalGeodesy.IsTotallyGeodesic
      P R ι DP DR)
    (z : SphereBundleTotal R.tangent)
    (t : TangentSpace (𝓘(ℝ,F).prod (𝓡 2)) z) :
    LP.contactFormReal P.tangent DP (sphereTotalMap P R ι hι hR z)
      (mfderiv (𝓘(ℝ,F).prod (𝓡 2)) (𝓘(ℝ,E).prod (𝓡 2))
        (sphereTotalMap P R ι hι hR) z t) =
    contactLineFiberEquivInduced P R ι hSmooth hι hR DP DR A B LR LP z
      (LR.contactFormReal R.tangent DR z t) := by
  let w := sphereTotalMap P R ι hι hR z
  letI := contactQuotientComplexModule R.tangent DR z
  letI := contactQuotientComplexModule P.tangent DP w
  have hnat := actualContactQuotientDerivative_eq_complexEquiv
    P R ι hSmooth hι hR DP DR hTot z
      (Submodule.Quotient.mk t)
  have hh := congrArg (LP.quotientEquiv w).symm hnat
  simpa [HolomorphicContactLine.contactFormReal,
    contactLineFiberEquivInduced, actualContactQuotientDerivative]
    using hh

end
end QuaternionicSymmetry.ManifoldQuaternionicInducedContactLineFiber
