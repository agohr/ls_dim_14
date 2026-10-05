import QuaternionicSymmetry.ManifoldTwistorBKKPicardHomogeneityApplication
import QuaternionicSymmetry.HolomorphicLineCoreSheafPicardGenerator

/-! The actual twistor's source-relative BKK dichotomy expressed in the full
analytic Picard group of locally free rank-one module sheaves. The passage
from represented cores to that full analytic group is internally proved;
the reviewed generic BKK/Chow/GAGA-derived input is still an explicit
premise. No algebraic Picard comparison is asserted in this leaf. -/

namespace QuaternionicSymmetry.ManifoldTwistorBKKAnalyticPicardApplication

open GeneralContactFanoPicardHomogeneitySource
open ManifoldTwistorBKKPicardHomogeneityApplication
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorContactAutomorphisms ManifoldTwistorLineCoreClasses
open ManifoldPositiveQuaternionicKahlerGeometry
open HolomorphicLineCoreAmpleFiniteMap
open HolomorphicLineSheafClasses HolomorphicLineSheafClassGroup
open HolomorphicLineCoreSheafPicardGenerator
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

/-- Same actual twistor and contact line as the source-relative analytic dichotomy,
but the first branch now ranges over *all* locally free rank-one analytic
module-sheaf isomorphism classes. -/
theorem analyticPicard_generator_or_contactAut_transitive
    (hBKK : AnalyticContactPicardOrHomogeneousCorollary)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 1 ≤ n)
    (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)
    (hAmple :
      letI := A.charts
      letI := A.complexManifold
      AmpleCore 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore P.tangent P.connection C.contact.line)) :
    letI := A.charts
    letI := A.complexManifold
    Function.Bijective (fun r : ℤ =>
      (classMulEquiv 𝓘(ℂ,ComplexTwistorModel n)
        (contactClass P.tangent P.connection C.contact.line) :
        SheafClass (B := SphereBundleTotal P.tangent)
          𝓘(ℂ,ComplexTwistorModel n)) ^ r) ∨
    (∀ z w : SphereBundleTotal P.tangent,
      ∃ f : ContactAutomorphisms P.tangent P.connection A C.contact.line,
        f.1 z = w) := by
  letI := A.charts
  letI := A.complexManifold
  rcases contactClass_generator_or_contactAut_transitive hBKK P n hn A C hAmple with
    hPic | hHom
  · left
    exact (core_zpow_bijective_iff_analyticPicard
      (B := SphereBundleTotal P.tangent)
      𝓘(ℂ,ComplexTwistorModel n)
      (contactLineCore P.tangent P.connection C.contact.line)).mp hPic
  · exact Or.inr hHom

end
end QuaternionicSymmetry.ManifoldTwistorBKKAnalyticPicardApplication
