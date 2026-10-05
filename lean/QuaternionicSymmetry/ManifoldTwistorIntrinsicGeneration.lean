import QuaternionicSymmetry.GeneralComplexContactHomogeneousAction
import QuaternionicSymmetry.ManifoldTwistorGeneralContactInstantiation
import QuaternionicSymmetry.ManifoldTwistorLineCoreClasses

/-! The generation invariant for the revised classification induction.
The conclusion concerns the literal intrinsic twistor contact-line core used
by the existing fixed-component restriction and section-bound theorems.
No Wolf model, metric classification, or literature premise is used here;
the actual holomorphic family must still be constructed by recognition. -/

namespace QuaternionicSymmetry.ManifoldTwistorIntrinsicGeneration

open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldQuaternionicMetric ManifoldQuaternionicConnection
open ManifoldTwistorLineCoreClasses HolomorphicLineCorePullback
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)
  {n : ℕ} {A : CompatibleComplexAtlas Q D n}
  (C : NondegenerateHolomorphicContactData Q D n A)

/-- The generic contact core is definitionally the actual intrinsic twistor
core, not a model line or a merely isomorphic untracked replacement. -/
theorem general_contactLineCore_eq :
    letI := A.charts
    (C.toGeneralContactGeometry Q D).contactLineCore =
      contactLineCore Q D C.contact.line := by
  rfl

/-- Global tangent sections generate the actual intrinsic contact line. -/
theorem contactLine_globallyGenerated_of_tangent
    (hTangent : (C.toGeneralContactGeometry Q D).TangentGloballyGenerated) :
    letI := A.charts
    GloballyGenerated 𝓘(ℂ,ComplexTwistorModel n)
      (contactLineCore Q D C.contact.line) := by
  exact (C.toGeneralContactGeometry Q D).contactLine_globallyGenerated hTangent

variable {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace HG] [TopologicalSpace G] [ChartedSpace HG G]
  (IG : ModelWithCorners ℂ V HG) [IsManifold IG ∞ G]

/-- A generating holomorphic family on the genuine twistor supplies precisely
the smaller-line premise of the checked ambient fixed-component estimate. -/
theorem contactLine_globallyGenerated_of_homogeneousFamily
    (F : (C.toGeneralContactGeometry Q D).HolomorphicHomogeneousFamily
      (G := G) IG) :
    letI := A.charts
    GloballyGenerated 𝓘(ℂ,ComplexTwistorModel n)
      (contactLineCore Q D C.contact.line) := by
  exact (C.toGeneralContactGeometry Q D).contactLine_globallyGenerated_of_homogeneousFamily IG F

end
end QuaternionicSymmetry.ManifoldTwistorIntrinsicGeneration
