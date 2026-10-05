import QuaternionicSymmetry.SelectedTorusSpanningDifferentials

/-! Real spanning of literal integral weights separates any genuine
complex-linear image characters whose pullbacks are the actual selected
compact-torus character differentials. Surjectivity of that image map is
an explicit premise, proved for the selected toral H in a separate leaf. -/

namespace QuaternionicSymmetry.SelectedTorusSpanningCharacterImage

open CompactLieTorusInputs SelectedTorusEmbeddedLieAtlas
open SelectedTorusSpanningDifferentials
open IntegralWeightRealSpanComplexSeparation
open TorusWeightCharacterDifferentialLinear
open RealToComplexTangentComplexification
open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open ManifoldQuaternionicTorusAction
open scoped Manifold ContDiff TensorProduct
noncomputable section

variable {V G W : Type}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [Group G] [TopologicalSpace G] [T2Space G]
  [SecondCountableTopology G]
  [ChartedSpace V G] [IsManifold 𝓘(ℝ,V) ∞ G]
  [LieGroup 𝓘(ℝ,V) ∞ G]
  [AddCommGroup W] [Module ℂ W]
  {r d : ℕ} {ι : Type*}

theorem selected_image_characters_separate_of_real_span
    (T : TorusEmbedding G r)
    (g : EmbeddedRealLieAtlas V (Torus r) G T.hom d)
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    (μ : ι → Fin r → ℤ)
    (hSpan : Submodule.span ℝ
      (Set.range (fun i => realWeightVector (μ i))) = ⊤)
    (f : (Fin d → ℝ) →ₗ[ℝ] W)
    (hf : Function.Surjective (complexifiedMapComplex f))
    (α : ι → W →ₗ[ℂ] ℂ)
    (hCompat : ∀ i, (α i).comp (complexifiedMapComplex f) =
      complexifiedMapComplex
        (weightCharacterDifferentialLinear (μ i) g.charts))
    (w : W) (hw : ∀ i, α i w = 0) : w = 0 := by
  letI : ChartedSpace (Fin d → ℝ) (Torus r) := g.charts
  obtain ⟨t,rfl⟩ := hf w
  have ht : t = 0 :=
    selected_character_differentials_separate_of_real_span
      T g hClosed hImm hLee μ hSpan t (by
        intro i
        rw [← hCompat i]
        exact hw i)
  rw [ht, map_zero]

end
end QuaternionicSymmetry.SelectedTorusSpanningCharacterImage
