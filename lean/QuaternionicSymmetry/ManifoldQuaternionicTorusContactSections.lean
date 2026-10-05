import QuaternionicSymmetry.ManifoldQuaternionicContactFiniteSections
import QuaternionicSymmetry.ManifoldQuaternionicTorusAction

/-! The actual compact-torus restriction of the holomorphic contact-section
representation. Continuity is inherited from the full isometry action once
its joint evaluation is established. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicTorusContactSections

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicTorusAction
open ManifoldQuaternionicIsometryTopology
open ManifoldQuaternionicIsometryContactSectionAction
open ManifoldQuaternionicContactFiniteSections
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorLineCoreClasses
open HolomorphicLineCorePullback
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

def contactTorusRepresentation
    {r : ℕ} (A : ContinuousTorusAction Q r)
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B) :
    letI := B.charts
    Torus r →* Module.End ℂ
      (GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore Q D C.line)) := by
  letI := B.charts
  exact (contactSectionRepresentation Q D B C).comp A.representation

theorem continuous_contactTorusAction_of_isometryAction
    [LocallyCompactSpace M]
    {r : ℕ} (A : ContinuousTorusAction Q r)
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B)
    [T2Space M] [CompactSpace M]
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (hFull :
      letI := B.charts
      letI := contactSectionsNormedAddCommGroup Q hFinite D B C
      Continuous (fun p : QuaternionicIsometries Q ×
        GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
          (contactLineCore Q D C.line) =>
        contactSectionRepresentation Q D B C p.1 p.2)) :
    letI := B.charts
    letI := contactSectionsNormedAddCommGroup Q hFinite D B C
    Continuous (fun p : Torus r ×
      GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore Q D C.line) =>
      contactTorusRepresentation Q A D B C p.1 p.2) := by
  letI := B.charts
  letI := contactSectionsNormedAddCommGroup Q hFinite D B C
  have hρ : Continuous A.representation :=
    continuous_representation_of_action Q A.representation A.continuous_action
  have hpair : Continuous (fun p : Torus r ×
      GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore Q D C.line) => (A.representation p.1, p.2)) :=
    (hρ.comp continuous_fst).prodMk continuous_snd
  simpa only [contactTorusRepresentation, MonoidHom.comp_apply] using hFull.comp hpair

end
end QuaternionicSymmetry.ManifoldQuaternionicTorusContactSections
