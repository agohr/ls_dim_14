import QuaternionicSymmetry.SelectedTorusSpanningCharacterImage
import QuaternionicSymmetry.LieCenterFromSeparatingWeights

/-! Same-eigenbasis centre elimination on a genuine selected compact torus
image. The integral weights are unpowered and literally the same weights
whose character differentials pull back the complex bracket characters.
No root multiplicity, Killing form or centre hypothesis is used. -/

namespace QuaternionicSymmetry.SelectedTorusLieCenterFromSpanningWeights

open Module CompactLieTorusInputs SelectedTorusEmbeddedLieAtlas
open SelectedTorusSpanningCharacterImage
open IntegralWeightRealSpanComplexSeparation
open RealToComplexTangentComplexification
open TorusWeightCharacterDifferentialLinear
open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open ManifoldQuaternionicTorusAction
open LieCenterFromSeparatingWeights
open scoped Manifold ContDiff TensorProduct
noncomputable section

variable {V G L ι : Type}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [Group G] [TopologicalSpace G] [T2Space G] [SecondCountableTopology G]
  [ChartedSpace V G] [IsManifold 𝓘(ℝ,V) ∞ G] [LieGroup 𝓘(ℝ,V) ∞ G]
  [LieRing L] [LieAlgebra ℂ L]
  {r d : ℕ}

theorem center_eq_bot_of_selected_integral_basis
    (T : TorusEmbedding G r)
    (g : EmbeddedRealLieAtlas V (Torus r) G T.hom d)
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    (H : LieSubalgebra ℂ L)
    (hSelf : ∀ x : L, (∀ y ∈ H, ⁅x,y⁆ = 0) → x ∈ H)
    (f : (Fin d → ℝ) →ₗ[ℝ] H)
    (hf : Function.Surjective (complexifiedMapComplex f))
    (b : Basis ι ℂ L) (μ : ι → Fin r → ℤ)
    (α : ι → H →ₗ[ℂ] ℂ)
    (hBracket : ∀ (h : H) i, ⁅(h : L),b i⁆ = α i h • b i)
    (hCompat : ∀ i, (α i).comp (complexifiedMapComplex f) =
      complexifiedMapComplex
        (weightCharacterDifferentialLinear (μ i) g.charts))
    (hSpan : Submodule.span ℝ
      (Set.range (fun i => realWeightVector (μ i))) = ⊤) :
    LieAlgebra.center ℂ L = ⊥ := by
  apply center_eq_bot_of_separating_weights H hSelf (fun i h => α i h)
  · intro i
    exact ⟨b i, b.ne_zero i, fun h => hBracket h i⟩
  · intro h hh
    exact selected_image_characters_separate_of_real_span
      T g hClosed hImm hLee μ hSpan f hf α hCompat h hh

end
end QuaternionicSymmetry.SelectedTorusLieCenterFromSpanningWeights
