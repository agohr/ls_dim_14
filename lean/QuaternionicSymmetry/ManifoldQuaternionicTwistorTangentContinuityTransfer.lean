import QuaternionicSymmetry.ComplexRealTangentAction
import QuaternionicSymmetry.ManifoldQuaternionicContactSectionContinuity

/-! Transfer the genuine joint twistor tangent action from the constructed
real sphere-bundle atlas into any compatible complex atlas. Only the joint
real tangent action remains to be established geometrically; no independent
complex-atlas or section-action continuity premise is added.
-/

namespace QuaternionicSymmetry.ManifoldQuaternionicTwistorTangentContinuityTransfer

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicIsometryContactSectionAction
open ManifoldQuaternionicContactSectionContinuity
open ManifoldQuaternionicContactFiniteSections
open ManifoldQuaternionicTorusContactSections
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorLineCoreClasses
open ManifoldTwistorSphereCore
open HolomorphicLineCorePullback
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

/-- The two real tangent actions are conjugate by the actual derivatives
of the two smooth identity maps between the compatible atlases. -/
theorem real_tangentMap_comparison
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (f : QuaternionicIsometries Q) :
    letI := B.charts
    ∀ v : TangentBundle 𝓘(ℝ,ComplexTwistorModel n) (SphereBundleTotal Q),
      tangentMap 𝓘(ℝ,ComplexTwistorModel n) 𝓘(ℝ,ComplexTwistorModel n)
          (sphereTotalMap Q f) v =
        tangentMap (J (E := E)) 𝓘(ℝ,ComplexTwistorModel n) id
          (tangentMap (J (E := E)) (J (E := E)) (sphereTotalMap Q f)
            (tangentMap 𝓘(ℝ,ComplexTwistorModel n) (J (E := E)) id v)) := by
  letI := B.charts
  intro v
  have hTo := B.smoothToExisting.mdifferentiable (by simp)
  have hFrom := B.smoothFromExisting.mdifferentiable (by simp)
  have hF :=
    (ManifoldQuaternionicTwistorLiftSmooth.sphereTotalMap_contMDiff Q f).mdifferentiable
      (by simp)
  calc
    _ = tangentMap (J (E := E)) 𝓘(ℝ,ComplexTwistorModel n) id
        (tangentMap 𝓘(ℝ,ComplexTwistorModel n) (J (E := E))
          (sphereTotalMap Q f ∘ id) v) :=
      tangentMap_comp_at v (hFrom _) ((hF.comp hTo) _)
    _ = _ := congrArg
      (tangentMap (J (E := E)) 𝓘(ℝ,ComplexTwistorModel n)
        (id : SphereBundleTotal Q → SphereBundleTotal Q))
      (tangentMap_comp_at v (hF _) (hTo _))

/-- Joint continuity in the actual constructed real sphere atlas implies
joint continuity in the complex tangent bundle of the sourced compatible
atlas. The topology comparison and all chain rules are proved internally. -/
theorem continuous_complex_tangentAction_of_existing
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (hExisting : Continuous (fun p : QuaternionicIsometries Q ×
      TangentBundle (J (E := E)) (SphereBundleTotal Q) =>
      tangentMap (J (E := E)) (J (E := E)) (sphereTotalMap Q p.1) p.2)) :
    letI := B.charts
    letI := B.complexManifold
    Continuous (fun p : QuaternionicIsometries Q ×
      TangentBundle 𝓘(ℂ,ComplexTwistorModel n) (SphereBundleTotal Q) =>
      tangentMap 𝓘(ℂ,ComplexTwistorModel n) 𝓘(ℂ,ComplexTwistorModel n)
        (sphereTotalMap Q p.1) p.2) := by
  letI := B.charts
  letI := B.complexManifold
  letI := B.realManifold
  have hReal : Continuous (fun p : QuaternionicIsometries Q ×
      TangentBundle 𝓘(ℝ,ComplexTwistorModel n) (SphereBundleTotal Q) =>
      tangentMap 𝓘(ℝ,ComplexTwistorModel n) 𝓘(ℝ,ComplexTwistorModel n)
        (sphereTotalMap Q p.1) p.2) := by
    have h := (B.smoothFromExisting.continuous_tangentMap (by simp)).comp
      (hExisting.comp (continuous_fst.prodMk
        ((B.smoothToExisting.continuous_tangentMap (by simp)).comp continuous_snd)))
    exact h.congr (fun p => (real_tangentMap_comparison Q D B p.1 p.2).symm)
  exact ComplexRealTangentAction.continuous_tangentAction_complex
    (sphereTotalMap Q)
    (fun f => (ManifoldQuaternionicIsometryComplexAtlas.sphereTotalMap_realSmooth_in_compatibleAtlas
      Q D B f).mdifferentiable (by simp))
    (fun f => (ManifoldQuaternionicIsometryComplexInfinity.sphereTotalMap_contMDiff_complex_infty
      Q D B f).mdifferentiable (by simp)) hReal

/-- No complex-atlas regularity premise is needed to pass from the actual
real joint tangent action to the complete contact-section representation. -/
theorem continuous_contactSectionAction_of_existing_tangent
    [T2Space M] [CompactSpace M]
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B)
    (hExisting : Continuous (fun p : QuaternionicIsometries Q ×
      TangentBundle (J (E := E)) (SphereBundleTotal Q) =>
      tangentMap (J (E := E)) (J (E := E)) (sphereTotalMap Q p.1) p.2)) :
    letI := B.charts
    letI := contactSectionsNormedAddCommGroup Q hFinite D B C
    Continuous (fun p : QuaternionicIsometries Q ×
      GlobalSections 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line) =>
      contactSectionRepresentation Q D B C p.1 p.2) :=
  continuous_contactSectionAction_of_joint_tangent Q hFinite D B C
    (continuous_complex_tangentAction_of_existing Q D B hExisting)

/-- The same real-atlas obligation supplies continuity after restricting
the genuine section representation to the compact torus. -/
theorem continuous_contactTorusAction_of_existing_tangent
    [T2Space M] [CompactSpace M]
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    {r : ℕ} (T : ManifoldQuaternionicTorusAction.ContinuousTorusAction Q r)
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B)
    (hExisting : Continuous (fun p : QuaternionicIsometries Q ×
      TangentBundle (J (E := E)) (SphereBundleTotal Q) =>
      tangentMap (J (E := E)) (J (E := E)) (sphereTotalMap Q p.1) p.2)) :
    letI := B.charts
    letI := contactSectionsNormedAddCommGroup Q hFinite D B C
    Continuous (fun p : ManifoldQuaternionicTorusAction.Torus r ×
      GlobalSections 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line) =>
      contactTorusRepresentation Q T D B C p.1 p.2) :=
  continuous_contactTorusAction_of_joint_tangent Q hFinite T D B C
    (continuous_complex_tangentAction_of_existing Q D B hExisting)

end
end QuaternionicSymmetry.ManifoldQuaternionicTwistorTangentContinuityTransfer
