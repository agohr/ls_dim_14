import QuaternionicSymmetry.OpenSubsetTangentIdentity
import QuaternionicSymmetry.ComplexIdentityComponentLie
import QuaternionicSymmetry.ComplexLieRealCompanion

/-! The genuine inclusion of the open identity component into a
complex Lie group has identity derivative in the inherited real atlas.
This fixes the full-Aut versus Aut⁰ tangent comparison without a new
regularity source. -/

namespace QuaternionicSymmetry.ComplexIdentityComponentTangentIdentity

open QuaternionicSymmetry.IdentityComponentLie
open ComplexIdentityComponentLie ComplexLieRealCompanion
open OpenSubsetTangentIdentity
open scoped Manifold ContDiff
noncomputable section

variable {V G : Type}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace V G] [IsManifold 𝓘(ℂ,V) ∞ G]

theorem inclusion_mfderiv_eq_id (x : Component G) :
    letI : ChartedSpace V (Component G) :=
      ComplexIdentityComponentLie.charts V G
    mfderiv 𝓘(ℝ,V) 𝓘(ℝ,V)
      (Subtype.val : Component G → G) x =
        ContinuousLinearMap.id ℝ V := by
  letI : IsManifold 𝓘(ℝ,V) ∞ G :=
    ComplexLieRealCompanion.realManifold (V := V) (G := G)
  let U : TopologicalSpace.Opens G :=
    ⟨Component G, ComplexIdentityComponentLie.isOpen_component V G⟩
  exact subtype_mfderiv_eq_id U x

end
end QuaternionicSymmetry.ComplexIdentityComponentTangentIdentity
