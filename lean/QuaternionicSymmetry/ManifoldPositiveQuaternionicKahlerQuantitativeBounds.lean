import QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerLowerVirtualBounds

/-! The volume in the main paper’s lower-bound corollary is the canonical
integral of the actual analytic quarter-Pontryagin form. Its strict positivity
uses the development’s existing geometric positivity theorem. -/
namespace QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerQuantitativeBounds
open ManifoldTangentCharacterNumber ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldPositiveQuaternionicKahlerLowerVirtualBounds
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [Nonempty M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
variable (S : QuaternionicStructure E)
  (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))

open ManifoldQuaternionicQuarterVolume ManifoldQuaternionicCanonicalIntegration

/-- The paper's `U = ∫ u^n`, using the development's actual analytic form. -/
def quaternionicVolume : ℝ :=
  integral P.tangent (quarterTop P.tangent P.connection S.quaternionicDimension
    S.real_finrank.symm)

theorem quaternionicVolume_pos
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M))
    (hn : 2 ≤ S.quaternionicDimension) :
    0 < quaternionicVolume S P :=
  quarterTop_positive S P S.quaternionicDimension hsp heq38 hn S.real_finrank.symm

end
end QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerQuantitativeBounds
