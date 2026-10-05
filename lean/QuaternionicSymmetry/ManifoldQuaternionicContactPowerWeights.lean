import QuaternionicSymmetry.ManifoldQuaternionicContactPowerContinuousFaithful
import QuaternionicSymmetry.TorusLaurentRepresentation

/-! Integral character vectors and an explicit complex-torus point action
on the actual complete holomorphic contact-power section space. Continuity
is derived from the real joint twistor tangent action; only general compact
representation decomposition and circle-character quantization are sourced.
Preservation/algebraization of the embedded twistor space remains separate. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicContactPowerWeights

open ManifoldQuaternionicSpanSymmetry ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicContactPowerFiniteSections
open ManifoldQuaternionicContactPowerContinuity
open ManifoldQuaternionicContactPowerContinuousFaithful
open ManifoldQuaternionicTorusAction
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorLineCoreClasses
open ManifoldTwistorSphereCore
open HolomorphicLineCorePullback HolomorphicLineTensorPowerClasses
open CompactTorusEigenbasisSource TorusCharacterInput TorusLaurentRepresentation
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

private abbrev J := (𝓘(ℝ,E)).prod (𝓡 2)
local instance : Fact (Module.finrank ℝ
    ManifoldTwistorCoefficientSphere.EuclideanThree = 2 + 1) := ⟨by simp⟩
local instance (x : M) : ChartedSpace (EuclideanSpace ℝ (Fin 2))
    ((sphereCore Q).Fiber x) := by
  change ChartedSpace (EuclideanSpace ℝ (Fin 2))
    ManifoldTwistorCoefficientSphere.geometricSphere
  infer_instance

abbrev PowerSections
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B) (k : ℕ) : Type :=
  letI := B.charts
  GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
    (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line) k)

theorem exists_integral_contactPower_eigenbasis
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (hEigen : KnappTorusEigenbasis) (hCircle : CircleCharacterSource)
    {r : ℕ} (T : ContinuousTorusAction Q r)
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B) (k : ℕ)
    (hExisting : Continuous (fun p : QuaternionicIsometries Q ×
      TangentBundle (J (E := E)) (SphereBundleTotal Q) =>
      tangentMap (J (E := E)) (J (E := E)) (sphereTotalMap Q p.1) p.2)) :
    letI := B.charts
    ∃ b : Module.Basis (Fin (Module.finrank ℂ (PowerSections Q D B C k)))
      ℂ (PowerSections Q D B C k),
      ∃ μ : Fin (Module.finrank ℂ (PowerSections Q D B C k)) → Fin r → ℤ,
        ∀ (t : Torus r) (i : Fin (Module.finrank ℂ (PowerSections Q D B C k))),
          contactPowerTorusRepresentation Q T D B C k t (b i) =
            (weightCharacter (μ i) t : ℂ) • b i := by
  letI := B.charts
  letI := finiteDimensional_contactPowerSections Q hFinite D B C k
  letI := contactPowerSectionsNormedAddCommGroup Q hFinite D B C k
  letI := contactPowerSectionsNormedSpace Q hFinite D B C k
  exact exists_integral_eigenbasis hEigen hCircle
    (contactPowerTorusRepresentation Q T D B C k)
    (continuous_contactPowerTorusAction_of_existing_tangent Q hFinite T D B C k hExisting)

theorem exists_contactPower_laurent_extension
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (hEigen : KnappTorusEigenbasis) (hCircle : CircleCharacterSource)
    {r : ℕ} (T : ContinuousTorusAction Q r)
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B) (k : ℕ)
    (hExisting : Continuous (fun p : QuaternionicIsometries Q ×
      TangentBundle (J (E := E)) (SphereBundleTotal Q) =>
      tangentMap (J (E := E)) (J (E := E)) (sphereTotalMap Q p.1) p.2)) :
    letI := B.charts
    ∃ b : Module.Basis (Fin (Module.finrank ℂ (PowerSections Q D B C k)))
      ℂ (PowerSections Q D B C k),
      ∃ μ : Fin (Module.finrank ℂ (PowerSections Q D B C k)) → Fin r → ℤ,
        ∀ t : Torus r, complexRepresentation b μ (compactInclusion r t) =
          contactPowerTorusRepresentation Q T D B C k t := by
  letI := B.charts
  obtain ⟨b,μ,hμ⟩ :=
    exists_integral_contactPower_eigenbasis Q hFinite hEigen hCircle T D B C k hExisting
  exact ⟨b,μ,complexRepresentation_restrict b μ
    (contactPowerTorusRepresentation Q T D B C k) hμ⟩

end
end QuaternionicSymmetry.ManifoldQuaternionicContactPowerWeights
