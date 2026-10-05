import QuaternionicSymmetry.ManifoldTwistorBKKPicardUniquenessApplication
import QuaternionicSymmetry.ManifoldTwistorUniqueContactFullLieTransfer
import QuaternionicSymmetry.GeneralHolomorphicFullAutomorphismLieSource
import QuaternionicSymmetry.ManifoldTwistorCompactHausdorff

/-! On the analytic Picard-generator branch, BKK uniqueness identifies the
actual contact automorphism group with the full biholomorphism group.
Kobayashi's compact-complex transformation theorem supplies a single
complex Lie atlas and holomorphic joint action on the full group. Both
are transported to the same actual contact group. No NT infinitesimal or
Hamiltonian identification and no unrelated BWW atlas are used. -/

namespace QuaternionicSymmetry.ManifoldTwistorPicardContactLieAction

open GeneralContactFanoPicardUniquenessSource
open GeneralHolomorphicFullAutomorphismLieSource
open ManifoldTwistorBKKPicardUniquenessApplication
open ManifoldTwistorUniqueContactFullEquiv
open ManifoldTwistorUniqueContactFullLieTransfer
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorFullAutomorphisms
open ManifoldTwistorContactAutomorphisms ManifoldTwistorLineCoreClasses
open ManifoldPositiveQuaternionicKahlerGeometry
open HolomorphicLineCoreAmpleFiniteMap
open HolomorphicLineSheafClasses HolomorphicLineSheafClassGroup
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

/-- Concrete same-atlas contact-group conclusion: finite-dimensional
complex manifold, complex Lie group, and jointly holomorphic evaluation
on the genuine twistor space. -/
def ContactLieActionConclusion
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    {n : ℕ} (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A) : Prop :=
  letI := A.charts
  letI := A.complexManifold
  let G := ContactAutomorphisms P.tangent P.connection A C.contact.line
  ∃ (V : Type) (hNorm : NormedAddCommGroup V),
    letI : NormedAddCommGroup V := hNorm
    ∃ (hSpace : NormedSpace ℂ V) (hFinite : FiniteDimensional ℂ V)
      (hChart : ChartedSpace V G),
      letI : NormedSpace ℂ V := hSpace
      letI : FiniteDimensional ℂ V := hFinite
      letI : ChartedSpace V G := hChart
      ∃ hManifold : IsManifold 𝓘(ℂ,V) ∞ G,
        letI : IsManifold 𝓘(ℂ,V) ∞ G := hManifold
        ∃ hLie : LieGroup 𝓘(ℂ,V) ∞ G,
          letI : LieGroup 𝓘(ℂ,V) ∞ G := hLie
          ContMDiff (𝓘(ℂ,V).prod 𝓘(ℂ,ComplexTwistorModel n))
            𝓘(ℂ,ComplexTwistorModel n) ∞
            (fun p : G × SphereBundleTotal P.tangent => p.1.1 p.2)

/-- The Picard-generator branch supplies the actual contact-group Lie
transformation structure from reviewed universal BKK uniqueness and
Kobayashi inputs. The same selected contact line and twistor are retained. -/
theorem contact_lie_action_of_analyticPicard_generator
    (hUnique : AnalyticContactPicardGeneratorPreservesDistribution)
    (hKob : KobayashiCompactAutomorphismTransformation)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 1 ≤ n)
    (A : CompatibleComplexAtlas P.tangent P.connection n)
    (C : NondegenerateHolomorphicContactData P.tangent P.connection n A)
    (hAmple :
      letI := A.charts
      letI := A.complexManifold
      AmpleCore 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore P.tangent P.connection C.contact.line))
    (hPic :
      letI := A.charts
      letI := A.complexManifold
      Function.Bijective (fun r : ℤ =>
        (classMulEquiv 𝓘(ℂ,ComplexTwistorModel n)
          (contactClass P.tangent P.connection C.contact.line) :
          SheafClass (B := SphereBundleTotal P.tangent)
            𝓘(ℂ,ComplexTwistorModel n)) ^ r)) :
    ContactLieActionConclusion P A C := by
  letI := A.charts
  letI := A.complexManifold
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  letI : T2Space (SphereBundleTotal P.tangent) := inferInstance
  letI : CompactSpace (SphereBundleTotal P.tangent) := inferInstance
  letI : PreconnectedSpace (SphereBundleTotal P.tangent) := inferInstance
  letI : Nonempty (SphereBundleTotal P.tangent) := inferInstance
  letI : SecondCountableTopology (SphereBundleTotal P.tangent) := inferInstance
  let hPreserve := fullPreservesContact_of_analyticPicard_generator
    hUnique P n hn A C hAmple hPic
  obtain ⟨V,hNorm,hSpace,hFinite,hChart,hManifold,hLie,hJoint⟩ :=
    hKob (W := ComplexTwistorModel n) (Z := SphereBundleTotal P.tangent)
  letI : NormedAddCommGroup V := hNorm
  letI : NormedSpace ℂ V := hSpace
  letI : FiniteDimensional ℂ V := hFinite
  letI : ChartedSpace V
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A) := hChart
  letI : IsManifold 𝓘(ℂ,V) ∞
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A) := hManifold
  letI : LieGroup 𝓘(ℂ,V) ∞
      (TwistorHolomorphicAutomorphisms P.tangent P.connection A) := hLie
  let hContactChart := contactCharts (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI : ChartedSpace V
      (ContactAutomorphisms P.tangent P.connection A C.contact.line) :=
    hContactChart
  let hContactManifold := contactManifold (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI : IsManifold 𝓘(ℂ,V) ∞
      (ContactAutomorphisms P.tangent P.connection A C.contact.line) :=
    hContactManifold
  let hContactLie := contactLieGroup (V := V)
    P.tangent P.connection A C.contact.line hPreserve
  letI : LieGroup 𝓘(ℂ,V) ∞
      (ContactAutomorphisms P.tangent P.connection A C.contact.line) :=
    hContactLie
  exact ⟨V,hNorm,hSpace,hFinite,hContactChart,hContactManifold,
    hContactLie,contact_joint_holomorphic_of_full (V := V)
      P.tangent P.connection A C.contact.line hPreserve hJoint⟩

end
end QuaternionicSymmetry.ManifoldTwistorPicardContactLieAction
