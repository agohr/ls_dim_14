import QuaternionicSymmetry.ManifoldTwistorContactCanonicalApply
import QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerHomothety

/-! The exact existence boundary for LeBrun's positive twistor theorem.
The source premise supplies complex/contact geometry only for an actual
compact connected positive quaternionic-Kähler input in quaternionic
dimension `n ≥ 2` with scalar normalized to `16n(n+2)`. The normalization
itself is derived from the genuine homothety construction. No Hilbert
value, index, Fano/ample property, or classification conclusion is a
field of this premise. -/

namespace QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas

open QuaternionicSymmetry.GeneralComplexContactData
open QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerGeometry
open QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerHomothety
open QuaternionicSymmetry.ManifoldQuaternionicScalarCurvature
open QuaternionicSymmetry.ManifoldQuaternionicKSWEq38Input
open scoped Manifold ContDiff Quaternion

noncomputable section

universe uE uM

/-- Precisely restricted source theorem premise for the complex/contact
part of LeBrun 1995 Theorem 2.1. Its conclusion is actual geometry on
the already built twistor sphere total space, not a Hilbert value. -/
def NormalizedComplexContactExistence : Prop :=
  ∀ {E : Type uE} {M : Type uM}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Nontrivial E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4 * n)
    (hScalar : ∀ p y (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      localScalarCurvature P.tangent P.connection p y hy =
        16 * (n : ℝ) * ((n : ℝ) + 2)),
    ∃ A : CompatibleComplexAtlas P.tangent P.connection n,
      Nonempty (NondegenerateHolomorphicContactData
        P.tangent P.connection n A)

/-- LeBrun's normalized complex/contact conclusion applied after the
checked metric homothety, and the independent general contact canonical
theorem specialized to the resulting genuine holomorphic bundles. -/
theorem exists_normalized_contact_canonical
    {E : Type uE} {M : Type uM}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Nontrivial E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    (hT1 : NormalizedComplexContactExistence.{uE,uM})
    (hGeneral : GeneralContactCanonicalTheorem.{uE,uE,uM})
    (S : QuaternionicStructure E)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (heq38 : KSWEq38OnModel (E := E) (M := M))
    (hn : 2 ≤ S.quaternionicDimension) :
    ∃ s : ℝ, ∃ hs : 0 < s,
      ∃ A : CompatibleComplexAtlas
        (rescaleCompact P s hs).tangent (rescaleCompact P s hs).connection
        S.quaternionicDimension,
      Nonempty (NondegenerateHolomorphicContactData
        (rescaleCompact P s hs).tangent (rescaleCompact P s hs).connection
        S.quaternionicDimension A) ∧
      ∃ C : NondegenerateHolomorphicContactData
        (rescaleCompact P s hs).tangent (rescaleCompact P s hs).connection
        S.quaternionicDimension A,
        Nonempty (HolomorphicContactCanonicalIso
          (rescaleCompact P s hs).tangent (rescaleCompact P s hs).connection
          S.quaternionicDimension A C.contact.line) := by
  obtain ⟨s,hs,hscalar⟩ := exists_normalized_scalar S P heq38 hn
  let R := rescaleCompact P s hs
  obtain ⟨A,⟨C⟩⟩ := hT1 R S.quaternionicDimension hn S.real_finrank hscalar
  exact ⟨s,hs,A,⟨C⟩,C,
    contactCanonicalIso_of_generalContact R.tangent R.connection hGeneral C⟩

end
end QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas
