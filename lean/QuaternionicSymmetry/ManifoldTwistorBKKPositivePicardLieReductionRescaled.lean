import QuaternionicSymmetry.ManifoldTwistorBKKPositivePicardLieReduction
import QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerHomothety
import QuaternionicSymmetry.ManifoldRiemannianSymmetryTransport
import QuaternionicSymmetry.ManifoldMetricHomothety

/-!
# Arbitrary positive metric: normalized Picard/Lie data or original symmetry

The actual KSW scalar identity selects one positive metric homothety. The
already checked normalized BKK/contact-Lie reduction is then applied to
that rescaled geometry. Its Picard branch retains the *same* normalized
twistor atlas, contact form, ample line, full-Picard generator, distribution
preservation, and contact Lie action. If the normalized metric is symmetric,
the checked metric-homothety transport returns symmetry of the original
metric. No unscaled twistor/contact identification is needed or asserted.
-/

namespace QuaternionicSymmetry.ManifoldTwistorBKKPositivePicardLieReductionRescaled

open GeneralContactFanoPicardHomogeneitySource
open GeneralContactFanoPicardUniquenessSource
open GeneralHolomorphicFullAutomorphismLieSource
open GeneralPositiveAnticanonicalSimplyConnectedSource
open ManifoldTwistorPositiveRicciInput
open ManifoldTwistorBKKPositivePicardLieReduction
open ManifoldTwistorPicardContactLieAction
open ManifoldTwistorHomogeneousContactSymmetrySource
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorLineCoreClasses ManifoldTwistorUniqueContactFullEquiv
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldPositiveQuaternionicKahlerHomothety
open ManifoldQuaternionicKSWEq38Input
open ManifoldMetricHomothety
open ManifoldRiemannianIntrinsicSymmetry
open HolomorphicLineCoreAmpleFiniteMap
open HolomorphicLineSheafClasses HolomorphicLineSheafClassGroup
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

/-- No normalized scalar premise on the original positive geometry. Either
one genuine positive rescaling has a same-atlas Picard/uniqueness/contact-Lie
package, or the original metric itself has global Riemannian point
symmetries. All general literature clauses remain explicit. -/
theorem exists_rescaled_analyticPicard_contactLie_or_original_intrinsicSymmetric
    (hT1 : NormalizedPositiveRicciContactExistence)
    (hKodaira : HolomorphicPositiveLineKodairaSource.PositiveHermitianLineAmpleTheorem.{0,0,0})
    (hBKK : AnalyticContactPicardOrHomogeneousCorollary)
    (hUnique : AnalyticContactPicardGeneratorPreservesDistribution)
    (hKob : KobayashiCompactAutomorphismTransformation)
    (hBallmann : BallmannPositiveAnticanonicalSimplyConnected)
    (hWolfLeBrun : HomogeneousContactTwistorSymmetryCorollary)
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
        ContactLieActionConclusion R A C) ∨
    IsRiemannianSymmetric P.tangent := by
  obtain ⟨s, hs, hScalar⟩ := exists_normalized_scalar S P heq38 hn
  let R := rescaleCompact P s hs
  rcases exists_normalized_analyticPicard_contactLie_or_intrinsicSymmetric
      hT1 hKodaira hBKK hUnique hKob hBallmann hWolfLeBrun
      R S.quaternionicDimension hn S.real_finrank hScalar with hPic | hSym
  · obtain ⟨A, C, hAmple, hGenerator, hPreserve, hLie⟩ := hPic
    exact Or.inl ⟨s, hs, A, C, hAmple, hGenerator, hPreserve, hLie⟩
  · right
    change IsRiemannianSymmetric
      (ManifoldQuaternionicHomothetyReduction.rescaleMetric
        P.tangent s (ne_of_gt hs)) at hSym
    exact (isRiemannianSymmetric_iff_metricHomothety
      (rescaleHomothety P.tangent s hs)).mpr hSym

end
end QuaternionicSymmetry.ManifoldTwistorBKKPositivePicardLieReductionRescaled
