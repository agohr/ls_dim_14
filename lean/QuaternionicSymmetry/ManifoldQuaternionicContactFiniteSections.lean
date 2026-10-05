import QuaternionicSymmetry.ManifoldQuaternionicIsometryContactSectionAction
import QuaternionicSymmetry.HolomorphicLineFiniteSectionsSource
import QuaternionicSymmetry.ManifoldTwistorCompactHausdorff
import QuaternionicSymmetry.FiniteDimensionalComplexModuleNorm
import QuaternionicSymmetry.HolomorphicLineCoreFiniteSectionsContinuity
import QuaternionicSymmetry.HolomorphicLineCoreBasisOrbitContinuity
import QuaternionicSymmetry.ManifoldQuaternionicIsometryTopology

/-! Cartan–Serre finiteness specialized to the actual compact twistor
contact line, with a consistent basis-induced norm and exact continuity
criteria. Joint isometry-action continuity is not assumed or asserted. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicContactFiniteSections

open ManifoldTwistorLeBrunComplexAtlas
open ManifoldQuaternionicSpanSymmetry
open ManifoldTwistorLineCoreClasses
open ManifoldTwistorSphereCore
open HolomorphicLineCorePullback
open HolomorphicLineFiniteSectionsSource
open FiniteDimensionalComplexModuleNorm
open HolomorphicLineCoreFiniteSectionsContinuity
open HolomorphicLineCoreBasisOrbitContinuity
open ManifoldQuaternionicIsometryContactSectionAction
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem finiteDimensional_contactSections
    (hFinite : CompactHolomorphicLineSectionFiniteness)
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B) :
    letI := B.charts
    FiniteDimensional ℂ
      (GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore Q D C.line)) := by
  letI := B.charts
  letI := B.complexManifold
  exact hFinite (contactLineCore Q D C.line)

/-- A single finite basis induces the chosen norm on the genuine global
holomorphic contact-section space. -/
def contactSectionsNormedAddCommGroup
    (hFinite : CompactHolomorphicLineSectionFiniteness)
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B) :
    letI := B.charts
    NormedAddCommGroup
      (GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore Q D C.line)) := by
  letI := B.charts
  letI := finiteDimensional_contactSections Q hFinite D B C
  exact normedAddCommGroup _

/-- The scalar structure uses exactly the same basis-induced norm. -/
def contactSectionsNormedSpace
    (hFinite : CompactHolomorphicLineSectionFiniteness)
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B) :
    letI := B.charts
    letI := contactSectionsNormedAddCommGroup Q hFinite D B C
    NormedSpace ℂ
      (GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore Q D C.line)) := by
  letI := B.charts
  letI := finiteDimensional_contactSections Q hFinite D B C
  letI := contactSectionsNormedAddCommGroup Q hFinite D B C
  exact normedSpace _

/-- In the chosen finite-dimensional norm, continuity of the genuine
isometry action is reduced to its actual pointwise section evaluations.
The premise is not continuity of the representation itself. -/
theorem continuous_contactSectionAction_of_evaluation
    (hFinite : CompactHolomorphicLineSectionFiniteness)
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B)
    (hEval :
      letI := B.charts
      letI := contactSectionsNormedAddCommGroup Q hFinite D B C
      ∀ z : SphereBundleTotal Q,
        Continuous (fun p : QuaternionicIsometries Q ×
          GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
            (contactLineCore Q D C.line) =>
          (contactSectionRepresentation Q D B C p.1 p.2) z)) :
    letI := B.charts
    letI := contactSectionsNormedAddCommGroup Q hFinite D B C
    Continuous (fun p : QuaternionicIsometries Q ×
      GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore Q D C.line) =>
      contactSectionRepresentation Q D B C p.1 p.2) := by
  letI := B.charts
  letI := finiteDimensional_contactSections Q hFinite D B C
  letI := contactSectionsNormedAddCommGroup Q hFinite D B C
  letI := contactSectionsNormedSpace Q hFinite D B C
  exact continuous_action_of_evaluation
    𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line)
    (contactSectionRepresentation Q D B C) hEval

/-- It suffices to verify the actual isometry orbit of finitely many basis
sections at each twistor point. This is the remaining BG-R3 interface. -/
theorem continuous_contactSectionAction_of_basis_orbits
    (hFinite : CompactHolomorphicLineSectionFiniteness)
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B)
    (hOrbit :
      letI := B.charts
      letI := finiteDimensional_contactSections Q hFinite D B C
      letI := contactSectionsNormedAddCommGroup Q hFinite D B C
      ∀ (i : Fin (Module.finrank ℂ
        (GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
          (contactLineCore Q D C.line))))
        (z : SphereBundleTotal Q),
        Continuous (fun f : QuaternionicIsometries Q =>
          (contactSectionRepresentation Q D B C f
            ((Module.finBasis ℂ (GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
              (contactLineCore Q D C.line))) i)) z)) :
    letI := B.charts
    letI := contactSectionsNormedAddCommGroup Q hFinite D B C
    Continuous (fun p : QuaternionicIsometries Q ×
      GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore Q D C.line) =>
      contactSectionRepresentation Q D B C p.1 p.2) := by
  letI := B.charts
  letI := finiteDimensional_contactSections Q hFinite D B C
  letI := contactSectionsNormedAddCommGroup Q hFinite D B C
  letI := contactSectionsNormedSpace Q hFinite D B C
  exact continuous_action_of_basis_orbits
    𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line)
    (contactSectionRepresentation Q D B C) hOrbit

end
end QuaternionicSymmetry.ManifoldQuaternionicContactFiniteSections
