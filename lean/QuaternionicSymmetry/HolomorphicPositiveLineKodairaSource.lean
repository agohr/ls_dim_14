import QuaternionicSymmetry.HolomorphicLineHermitianMetric

/-! Published background: Wells, *Differential Analysis on Complex Manifolds*,
3rd ed., Springer GTM 65, VI §4 Theorem 4.1 and proof, pp.234–240:
the given positive line's sufficiently high tensor power embeds by complete
sections. III §2 supplies the Hermitian curvature convention.
See Textbooks/STAGE2_FIDELITY_REVIEW_20261001.md for provenance. -/

namespace QuaternionicSymmetry.HolomorphicPositiveLineKodairaSource

open QuaternionicSymmetry.HolomorphicLineCoreClasses
open QuaternionicSymmetry.HolomorphicLineCoreAmpleFiniteMap
open QuaternionicSymmetry.HolomorphicLineHermitianMetric
open scoped Manifold ContDiff
noncomputable section
universe uB uF uI

/-- The published Kodaira embedding theorem in the actual represented-line
presentation. The conclusion means that some positive tensor power's
complete holomorphic evaluation is a topological embedding with injective
complex manifold derivative. -/
def PositiveHermitianLineAmpleTheorem : Prop :=
  ∀ {B : Type uB} {F : Type uF}
    [TopologicalSpace B] [T2Space B] [SecondCountableTopology B]
    [CompactSpace B] [Nonempty B]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    [ChartedSpace F B] [IsManifold 𝓘(ℂ,F) ∞ B]
    (L : LineCore.{uI} (B := B) 𝓘(ℂ,F))
    (m : HermitianLineMetric L),
    m.PositiveChernCurvature → AmpleCore 𝓘(ℂ,F) L

/-- Applying the exact general source theorem to a separately constructed
positive Hermitian metric on one actual represented line. -/
theorem ampleCore_of_positiveHermitian
    {B : Type uB} {F : Type uF}
    [TopologicalSpace B] [T2Space B] [SecondCountableTopology B]
    [CompactSpace B] [Nonempty B]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    [ChartedSpace F B] [IsManifold 𝓘(ℂ,F) ∞ B]
    (hKodaira : PositiveHermitianLineAmpleTheorem.{uB,uF,uI})
    (L : LineCore.{uI} (B := B) 𝓘(ℂ,F))
    (m : HermitianLineMetric L)
    (hCurvature : m.PositiveChernCurvature) :
    AmpleCore 𝓘(ℂ,F) L :=
  hKodaira L m hCurvature

end
end QuaternionicSymmetry.HolomorphicPositiveLineKodairaSource
