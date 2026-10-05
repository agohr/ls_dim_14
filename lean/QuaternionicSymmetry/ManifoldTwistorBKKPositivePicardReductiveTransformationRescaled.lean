import QuaternionicSymmetry.ManifoldTwistorBKKPositivePicardLieReductionRescaled
import QuaternionicSymmetry.ManifoldTwistorBWW66ReductiveTransformationSource

/-!
# Picard branch with a same-atlas reductive full transformation group

The existing positive-metric dichotomy selects a rescaling and *one*
twistor complex/contact atlas on its Picard branch. The universal
BWW--Matsushima--Kobayashi derived source is applied to that very atlas.
Thus its joint action and central radical share a full-automorphism Lie
atlas. The separately retained contact-group Lie action is not claimed
to have a central radical until the full/contact Lie-algebra transport
has actually been established.
-/

namespace QuaternionicSymmetry.ManifoldTwistorBKKPositivePicardReductiveTransformationRescaled

open GeneralContactFanoPicardHomogeneitySource
open GeneralContactFanoPicardUniquenessSource
open GeneralHolomorphicFullAutomorphismLieSource
open GeneralPositiveAnticanonicalSimplyConnectedSource
open ManifoldTwistorPositiveRicciInput
open ManifoldTwistorBKKPositivePicardLieReductionRescaled
open ManifoldTwistorBWW66ReductiveTransformationSource
open ManifoldTwistorFullAutReductiveTransformationTarget
open ManifoldTwistorPicardContactLieAction
open ManifoldTwistorHomogeneousContactSymmetrySource
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorLineCoreClasses ManifoldTwistorUniqueContactFullEquiv
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldPositiveQuaternionicKahlerHomothety
open ManifoldQuaternionicKSWEq38Input
open ManifoldRiemannianIntrinsicSymmetry
open HolomorphicLineCoreAmpleFiniteMap
open HolomorphicLineSheafClasses HolomorphicLineSheafClassGroup
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

/-- On the non-symmetric branch, the normalized actual twistor carries
Picard generation, contact uniqueness, a holomorphic contact Lie action,
and a reductive full-automorphism transformation structure on the *same*
twistor atlas `A` and contact datum `C`. The symmetric branch concerns
the original, unscaled metric. -/
theorem exists_rescaled_analyticPicard_reductiveTransformation_or_original_intrinsicSymmetric
    (hT1 : NormalizedPositiveRicciContactExistence)
    (hKodaira : HolomorphicPositiveLineKodairaSource.PositiveHermitianLineAmpleTheorem.{0,0,0})
    (hBKK : AnalyticContactPicardOrHomogeneousCorollary)
    (hUnique : AnalyticContactPicardGeneratorPreservesDistribution)
    (hKob : KobayashiCompactAutomorphismTransformation)
    (hBallmann : BallmannPositiveAnticanonicalSimplyConnected)
    (hWolfLeBrun : HomogeneousContactTwistorSymmetryCorollary)
    (hBWW : FullAutReductiveTransformationSource)
    (S : QuaternionicStructure E)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (heq38 : KSWEq38OnModel (E := E) (M := M))
    (hn : 2 ≤ S.quaternionicDimension) :
    (∃ s : ℝ, ∃ hs : 0 < s,
      let R := rescaleCompact P s hs
      ∃ A : CompatibleComplexAtlas R.tangent R.connection S.quaternionicDimension,
      ∃ C : NondegenerateHolomorphicContactData R.tangent R.connection
        S.quaternionicDimension A,
        letI := A.charts
        letI := A.complexManifold
        AmpleCore 𝓘(ℂ,ComplexTwistorModel S.quaternionicDimension)
          (contactLineCore R.tangent R.connection C.contact.line) ∧
        Function.Bijective (fun r : ℤ =>
          (classMulEquiv 𝓘(ℂ,ComplexTwistorModel S.quaternionicDimension)
            (contactClass R.tangent R.connection C.contact.line) :
            SheafClass (B := SphereBundleTotal R.tangent)
              𝓘(ℂ,ComplexTwistorModel S.quaternionicDimension)) ^ r) ∧
        FullPreservesContact R.tangent R.connection A C.contact.line ∧
        ContactLieActionConclusion R A C ∧
        FullAutReductiveTransformationConclusion R.tangent R.connection A) ∨
    IsRiemannianSymmetric P.tangent := by
  rcases exists_rescaled_analyticPicard_contactLie_or_original_intrinsicSymmetric
      hT1 hKodaira hBKK hUnique hKob hBallmann hWolfLeBrun
      S P heq38 hn with hPic | hSym
  · obtain ⟨s,hs,A,C,hAmple,hGenerator,hPreserve,hLie⟩ := hPic
    let R := rescaleCompact P s hs
    exact Or.inl ⟨s,hs,A,C,hAmple,hGenerator,hPreserve,hLie,
      hBWW R S.quaternionicDimension hn S.real_finrank A⟩
  · exact Or.inr hSym

end
end QuaternionicSymmetry.ManifoldTwistorBKKPositivePicardReductiveTransformationRescaled
