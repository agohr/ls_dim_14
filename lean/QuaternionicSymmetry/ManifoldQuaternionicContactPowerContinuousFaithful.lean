import QuaternionicSymmetry.ManifoldQuaternionicContactPowerContinuity
import QuaternionicSymmetry.ManifoldQuaternionicContactPowerFaithfulness
import QuaternionicSymmetry.ManifoldQuaternionicTwistorTangentContinuityTransfer

/-! A faithful compact torus of actual quaternionic isometries acts
continuously and projectively faithfully on the complete section space of
some genuinely very ample contact power. Only the real joint twistor
tangent-continuity obligation remains analytic here; algebraic torus
complexification is not inferred from this compact-torus statement. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicContactPowerContinuousFaithful

open ManifoldQuaternionicSpanSymmetry ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicContactPowerSectionAction
open ManifoldQuaternionicContactPowerFaithfulness
open ManifoldQuaternionicContactPowerFiniteSections
open ManifoldQuaternionicContactPowerContinuity
open ManifoldQuaternionicTwistorTangentContinuityTransfer
open ManifoldQuaternionicTorusAction
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorLineCoreClasses
open ManifoldTwistorSphereCore
open HolomorphicLineCorePullback HolomorphicLineTensorPowerClasses
open HolomorphicLineCoreAmpleFiniteMap
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
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

theorem contactPowerSectionRepresentation_injective
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B) (k : ℕ)
    (hVery : letI := B.charts; letI := B.complexManifold
      VeryAmpleCore 𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line) k)) :
    letI := B.charts
    Function.Injective (contactPowerSectionRepresentation Q D B C k) := by
  letI := B.charts
  apply (injective_iff_map_eq_one _).mpr
  intro f hf
  apply eq_one_of_scalar_contactPowerAction Q D B C k hVery f (1 : ℂˣ)
  intro s
  rw [hf]
  simp

theorem eq_one_of_scalar_contactPowerTorusAction
    {r : ℕ} (T : ContinuousTorusAction Q r) (hT : T.Faithful)
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B) (k : ℕ)
    (hVery : letI := B.charts; letI := B.complexManifold
      VeryAmpleCore 𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line) k))
    (t : Torus r) (c : ℂˣ)
    (hc : letI := B.charts
      ∀ s : GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line) k),
        contactPowerTorusRepresentation Q T D B C k t s = (c : ℂ) • s) :
    t = 1 := by
  have h := eq_one_of_scalar_contactPowerAction Q D B C k hVery
    (T.representation t) c hc
  apply hT
  simpa only [map_one] using h

theorem continuous_contactPowerTorusAction_of_existing_tangent
    [T2Space M] [CompactSpace M]
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    {r : ℕ} (T : ContinuousTorusAction Q r)
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B) (k : ℕ)
    (hExisting : Continuous (fun p : QuaternionicIsometries Q ×
      TangentBundle (J (E := E)) (SphereBundleTotal Q) =>
      tangentMap (J (E := E)) (J (E := E)) (sphereTotalMap Q p.1) p.2)) :
    letI := B.charts
    letI := contactPowerSectionsNormedAddCommGroup Q hFinite D B C k
    Continuous (fun p : Torus r ×
      GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line) k) =>
      contactPowerTorusRepresentation Q T D B C k p.1 p.2) :=
  continuous_contactPowerTorusAction_of_joint_tangent Q hFinite T D B C k
    (continuous_complex_tangentAction_of_existing Q D B hExisting)

/-- One and the same positive power supplies the geometric projective
embedding, finite complete section space, continuous compact-torus action
and trivial projective kernel. No weight decomposition or algebraization
is included as an assumption or asserted as a consequence here. -/
theorem exists_veryAmple_power_continuous_projectively_faithful
    [T2Space M] [CompactSpace M]
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    {r : ℕ} (T : ContinuousTorusAction Q r) (hT : T.Faithful)
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B)
    (hAmple : letI := B.charts; letI := B.complexManifold
      AmpleCore 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line))
    (hExisting : Continuous (fun p : QuaternionicIsometries Q ×
      TangentBundle (J (E := E)) (SphereBundleTotal Q) =>
      tangentMap (J (E := E)) (J (E := E)) (sphereTotalMap Q p.1) p.2)) :
    letI := B.charts
    letI := B.complexManifold
    ∃ k : ℕ, 0 < k ∧
      VeryAmpleCore 𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line) k) ∧
      FiniteDimensional ℂ (GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line) k)) ∧
      (letI := contactPowerSectionsNormedAddCommGroup Q hFinite D B C k;
        Continuous (fun p : Torus r ×
          GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
            (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
              (contactLineCore Q D C.line) k) =>
          contactPowerTorusRepresentation Q T D B C k p.1 p.2)) ∧
      ∀ (t : Torus r) (c : ℂˣ),
        (∀ s : GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
          (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line) k),
          contactPowerTorusRepresentation Q T D B C k t s = (c : ℂ) • s) → t = 1 := by
  letI := B.charts
  letI := B.complexManifold
  obtain ⟨k,hk,hVery⟩ := hAmple
  exact ⟨k,hk,hVery,finiteDimensional_contactPowerSections Q hFinite D B C k,
    continuous_contactPowerTorusAction_of_existing_tangent Q hFinite T D B C k hExisting,
    fun t c hc => eq_one_of_scalar_contactPowerTorusAction Q T hT D B C k hVery t c hc⟩

end
end QuaternionicSymmetry.ManifoldQuaternionicContactPowerContinuousFaithful
