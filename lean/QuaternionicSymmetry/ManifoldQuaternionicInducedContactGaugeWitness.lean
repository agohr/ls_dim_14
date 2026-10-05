import QuaternionicSymmetry.ManifoldTwistorLocalContactTangentSection
import QuaternionicSymmetry.ManifoldQuaternionicInducedContactLinePullback
import QuaternionicSymmetry.HolomorphicLineCorePullbackLocalSections
import QuaternionicSymmetry.HolomorphicLineLocalGaugeRatio
import QuaternionicSymmetry.ManifoldTwistorContactComplexExact
import QuaternionicSymmetry.ManifoldTwistorContactQuotientComplex

/-! Construct the local holomorphic source and restricted-target contact
sections needed for the induced contact-line gauge, directly from actual
holomorphic contact forms and the actual twistor differential. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicInducedContactGaugeWitness
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicInducedTwistorMap
open ManifoldQuaternionicInducedContactLineFiber
open ManifoldQuaternionicInducedContactLinePullback
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
/-- At every point, a source contact section is nonzero and its image under
the differential is a holomorphic section of the actual restricted ambient
contact line. No extension off the induced twistor image is assumed. -/
theorem exists_actual_local_gauge_witness {m n : ℕ}
    (A : CompatibleComplexAtlas R.tangent DR m)
    (B : CompatibleComplexAtlas P.tangent DP n)
    (CR : HolomorphicContactData R.tangent DR m A)
    (CP : HolomorphicContactData P.tangent DP n B)
    (z : SphereBundleTotal R.tangent) :
    letI := A.charts
    letI := B.charts
    letI := A.complexManifold
    letI := B.complexManifold
    letI := CR.line.holomorphic
    letI := restrictedAmbientCore_holomorphic P R ι hSmooth hι hR DP DR hTot
      A B CP.line
    ∃ U : Set (SphereBundleTotal R.tangent), IsOpen U ∧ z ∈ U ∧
      ∃ s : ∀ y : SphereBundleTotal R.tangent, CR.line.core.Fiber y,
      ∃ t : ∀ y : SphereBundleTotal R.tangent,
        (restrictedAmbientCore P R ι hSmooth hι hR DP DR hTot A B CP.line).Fiber y,
        ContMDiffOn 𝓘(ℂ,ComplexTwistorModel m)
          ((𝓘(ℂ,ComplexTwistorModel m)).prod 𝓘(ℂ,ℂ)) ∞
          (fun y => (⟨y,s y⟩ : Bundle.TotalSpace ℂ CR.line.core.Fiber)) U ∧
        ContMDiffOn 𝓘(ℂ,ComplexTwistorModel m)
          ((𝓘(ℂ,ComplexTwistorModel m)).prod 𝓘(ℂ,ℂ)) ∞
          (fun y => (⟨y,t y⟩ : Bundle.TotalSpace ℂ
            (restrictedAmbientCore P R ι hSmooth hι hR DP DR hTot A B CP.line).Fiber)) U ∧
        s z ≠ 0 ∧
        ∀ y ∈ U,
          restrictedContactLineFiberEquiv P R ι hSmooth hι hR DP DR hTot
            A B CR.line CP.line y (s y) = t y := by
  letI := A.charts
  letI := B.charts
  letI := A.complexManifold
  letI := B.complexManifold
  letI := CR.line.holomorphic
  letI := CP.line.holomorphic
  letI := restrictedAmbientCore_holomorphic P R ι hSmooth hι hR DP DR hTot A B CP.line
  letI := ManifoldTwistorGlobalAlmostComplex.contactQuotientComplexModule R.tangent DR z
  have hdim : Module.finrank ℂ (CR.line.core.Fiber z) = 1 :=
    (CR.line.quotientEquiv z).finrank_eq.trans
      (ManifoldTwistorGlobalAlmostComplex.contactQuotient_complex_finrank R.tangent DR z)
  letI : Nontrivial (CR.line.core.Fiber z) :=
    Module.nontrivial_of_finrank_pos (by rw [hdim]; omega)
  obtain ⟨w,hw⟩ := exists_ne (0 : CR.line.core.Fiber z)
  obtain ⟨v,hv⟩ := CR.line.contactFormComplex_surjective R.tangent DR z w
  obtain ⟨U,hU,hz,σ,hσz,hσ,hα⟩ :=
    ManifoldTwistorLocalContactTangentSection.exists_local_contact_section_with_tangent
      R.tangent DR A CR z v
  let Φ := sphereTotalMap P R ι hι hR
  let s : ∀ y : SphereBundleTotal R.tangent, CR.line.core.Fiber y :=
    fun y => CR.line.contactFormComplex R.tangent DR y (σ y)
  let t : ∀ y : SphereBundleTotal R.tangent,
      (restrictedAmbientCore P R ι hSmooth hι hR DP DR hTot A B CP.line).Fiber y :=
    fun y => CP.line.contactFormComplex P.tangent DP (Φ y)
      (mfderiv 𝓘(ℂ,ComplexTwistorModel m)
        𝓘(ℂ,ComplexTwistorModel n) Φ y (σ y))
  refine ⟨U,hU,hz,s,t,?_,?_,?_,?_⟩
  · exact hα
  · have hΦ : ContMDiff 𝓘(ℂ,ComplexTwistorModel m)
        𝓘(ℂ,ComplexTwistorModel n) ∞ Φ :=
      ManifoldQuaternionicInducedComplexInfinity.sphereTotalMap_contMDiff_complex_infty
        P R ι hSmooth hι hR DP DR hTot A B
    have hTM : ContMDiff (𝓘(ℂ,ComplexTwistorModel m)).tangent
        (𝓘(ℂ,ComplexTwistorModel n)).tangent ∞
        (tangentMap 𝓘(ℂ,ComplexTwistorModel m)
          𝓘(ℂ,ComplexTwistorModel n) Φ) :=
      hΦ.contMDiff_tangentMap (by simp)
    have hAlong : ContMDiffOn 𝓘(ℂ,ComplexTwistorModel m)
        ((𝓘(ℂ,ComplexTwistorModel n)).prod 𝓘(ℂ,ℂ)) ∞
        (fun y => (⟨Φ y,t y⟩ : Bundle.TotalSpace ℂ CP.line.core.Fiber)) U := by
      convert (CP.contactHolomorphic.comp hTM).comp_contMDiffOn hσ using 1
    exact HolomorphicLineCorePullbackLocalSections.alongMap_contMDiffOn_pullback
      𝓘(ℂ,ComplexTwistorModel n) 𝓘(ℂ,ComplexTwistorModel m)
      CP.line.core Φ hΦ U t hAlong
  · change CR.line.contactFormComplex R.tangent DR z (σ z) ≠ 0
    rw [hσz,hv]
    exact hw
  · intro y _
    exact (ManifoldQuaternionicInducedContactComplexNaturality.contactLineFiberEquiv_contactFormComplex
      P R ι hSmooth hι hR DP DR hTot A B CR.line CP.line y (σ y)).symm

include hSmooth hTot in
/-- The actual induced contact-line fiber equivalence satisfies the generic
holomorphic local-witness criterion, in both directions. -/
theorem actual_hasLocalHolomorphicWitness {m n : ℕ}
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
    HolomorphicLineLocalGaugeRatio.HasLocalHolomorphicWitness
      𝓘(ℂ,ComplexTwistorModel m) CR.line.core
      (restrictedAmbientCore P R ι hSmooth hι hR DP DR hTot A B CP.line)
      (restrictedContactLineFiberEquiv P R ι hSmooth hι hR DP DR hTot
        A B CR.line CP.line) := by
  letI := A.charts
  letI := B.charts
  letI := A.complexManifold
  letI := B.complexManifold
  letI := CR.line.holomorphic
  letI := restrictedAmbientCore_holomorphic P R ι hSmooth hι hR DP DR hTot A B CP.line
  exact exists_actual_local_gauge_witness P R ι hSmooth hι hR DP DR hTot A B CR CP

end
end QuaternionicSymmetry.ManifoldQuaternionicInducedContactGaugeWitness
