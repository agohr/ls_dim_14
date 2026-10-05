import QuaternionicSymmetry.HolomorphicFamilyVectorFields

/-! The parameter derivative of a jointly holomorphic family is complex
linear as a map into genuine global holomorphic tangent sections. -/

namespace QuaternionicSymmetry.HolomorphicFamilyInfinitesimalLinear

open HolomorphicFamilyVectorFields
open scoped Manifold ContDiff
noncomputable section

variable {V F G Z : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace G] [TopologicalSpace Z]
  [ChartedSpace V G] [ChartedSpace F Z]
  [IsManifold 𝓘(ℂ,V) ∞ G] [IsManifold 𝓘(ℂ,F) ∞ Z]
  (a : G × Z → Z) (g₀ : G)
  (ha : ContMDiff (𝓘(ℂ,V).prod 𝓘(ℂ,F)) 𝓘(ℂ,F) ∞ a)
  (hId : ∀ z : Z, a (g₀,z) = z)

/-- No transitivity or contact assumption: this is the actual derivative
of the given holomorphic family, bundled into true holomorphic sections. -/
def infinitesimalActionLinear :
    TangentSpace 𝓘(ℂ,V) g₀ →ₗ[ℂ]
      ContMDiffSection 𝓘(ℂ,F) F ∞ (TangentSpace 𝓘(ℂ,F) : Z → Type _) where
  toFun v := variationSection 𝓘(ℂ,V) 𝓘(ℂ,F) a g₀ ha hId v
  map_add' v w := by
    apply ContMDiffSection.ext
    intro z
    exact map_add (mfderiv 𝓘(ℂ,V) 𝓘(ℂ,F) (fun g => a (g,z)) g₀) v w
  map_smul' c v := by
    apply ContMDiffSection.ext
    intro z
    exact map_smul (mfderiv 𝓘(ℂ,V) 𝓘(ℂ,F) (fun g => a (g,z)) g₀) c v

theorem infinitesimalActionLinear_apply (v : TangentSpace 𝓘(ℂ,V) g₀)
    (z : Z) :
    infinitesimalActionLinear a g₀ ha hId v z =
      (mfderiv 𝓘(ℂ,V) 𝓘(ℂ,F) (fun g => a (g,z)) g₀) v := rfl

end
end QuaternionicSymmetry.HolomorphicFamilyInfinitesimalLinear
