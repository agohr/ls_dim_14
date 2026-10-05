import QuaternionicSymmetry.ManifoldQuaternionicMaximalTorusComplexifiedLie

/-! A source-only actual selected maximal-isometry-torus Lie conclusion:
BG-R3 + BG-Q1 + Myers–Steenrod construct the real Lie atlas, and the
already registered Knapp BG-L1 correspondence handles that exact torus.
No full twistor automorphism Lie algebra is involved yet. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicMaximalTorusComplexifiedFromSources

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicIsometryPreservationInput
open ManifoldRiemannianMyersSteenrodInput
open ManifoldRiemannianIsometryLieInput
open ManifoldQuaternionicIsometryLieFromSources
open CompactLieTorusInputs CompactLieTorusMaximalTransfer
open CompactLieMaximalTorusTangentSource
open ManifoldQuaternionicMaximalTorusComplexifiedLie
open ComplexifiedLieCentralizerComponents IdentityComponentLie
open scoped Manifold ContDiff TensorProduct
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
  (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
  (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)

include n hn hDim

/-- The real Lie atlas is chosen from BG-R3, not supplied as an additional
hypothesis; the selected maximal torus `T` is unchanged. -/
theorem exists_actual_selected_complexified_selfCentralizing
    (hClosed : GeneralClosedSubgroupLieSource.LeeClosedEmbeddingTheorem)
    (hR3 : IsometryLieSource.{0,0})
    (hCorrespondence : MaximalTorusLieCorrespondenceSource)
    {r : ℕ} (T : TorusEmbedding (QuaternionicIsometries P.tangent) r)
    (hMax : T.IsMaximal (QuaternionicIsometries P.tangent)) :
    ∃ (V : Type) (hNorm : NormedAddCommGroup V),
      letI : NormedAddCommGroup V := hNorm
      ∃ (hSpace : NormedSpace ℝ V),
        letI : NormedSpace ℝ V := hSpace
        ∃ (hFinite : FiniteDimensional ℝ V)
          (hChart : ChartedSpace V (QuaternionicIsometries P.tangent)),
          letI : FiniteDimensional ℝ V := hFinite
          letI : ChartedSpace V (QuaternionicIsometries P.tangent) := hChart
          ∃ hLie : LieGroup 𝓘(ℝ,V) ∞ (QuaternionicIsometries P.tangent),
            letI : LieGroup 𝓘(ℝ,V) ∞ (QuaternionicIsometries P.tangent) := hLie
            letI : ChartedSpace V (Component (QuaternionicIsometries P.tangent)) :=
              IdentityComponentLie.charts V (QuaternionicIsometries P.tangent)
            letI : LieGroup 𝓘(ℝ,V) ∞ (Component (QuaternionicIsometries P.tangent)) :=
              IdentityComponentLie.lieGroup V (QuaternionicIsometries P.tangent)
            letI : CompleteSpace V := FiniteDimensional.complete ℝ V
            letI : ENat.LEInfty (minSmoothness ℝ 3) := by
              simpa only [minSmoothness_of_isRCLikeNormedField] using
                (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))
            letI : LieGroup 𝓘(ℝ,V) (minSmoothness ℝ 3)
                (Component (QuaternionicIsometries P.tangent)) :=
              LieGroup.of_le (ENat.LEInfty.out)
            let Tc := liftToComponent (QuaternionicIsometries P.tangent) T
            ∀ z : ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ,V)
                (Component (QuaternionicIsometries P.tangent)),
              z ∈ complexSpan (torusLieSpan (V := V) Tc) ↔
                ∀ t ∈ torusLieSpan (V := V) Tc,
                  ⁅z, (1 : ℂ) ⊗ₜ[ℝ] t⁆ = 0 := by
  obtain ⟨V,hNorm,hSpace,hFinite,hChart,_hManifold,hLie⟩ :=
    exists_real_lie_atlas P n hn hDim hClosed hR3
  refine ⟨V,hNorm,hSpace,hFinite,hChart,hLie,?_⟩
  exact selected_torus_complexified_selfCentralizing
    P n hn hDim
      (ManifoldQuaternionicIsometryCompactness.compactness_of_isometryLie hR3) hChart hLie hCorrespondence T hMax

end
end QuaternionicSymmetry.ManifoldQuaternionicMaximalTorusComplexifiedFromSources
