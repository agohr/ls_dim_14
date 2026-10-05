import QuaternionicSymmetry.GeneralComplexContactSections
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-! Differentiating an actual jointly holomorphic family through the
identity produces global holomorphic vector fields. For a complex group
action the parameter point is the identity and these are its fundamental
vector fields. No transitivity or submersion theorem is assumed here. -/
namespace QuaternionicSymmetry.HolomorphicFamilyVectorFields
open scoped Manifold ContDiff
noncomputable section

variable {V F HG HZ G Z : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace HG] [TopologicalSpace HZ]
  [TopologicalSpace G] [TopologicalSpace Z]
  [ChartedSpace HG G] [ChartedSpace HZ Z]
  (IG : ModelWithCorners ℂ V HG) (IZ : ModelWithCorners ℂ F HZ)
  [IsManifold IG ∞ G] [IsManifold IZ ∞ Z]
  (a : G × Z → Z) (g₀ : G)
  (ha : ContMDiff (IG.prod IZ) IZ ∞ a)
  (hId : ∀ z : Z, a (g₀,z) = z)

/-- The actual parameter-direction derivative of a holomorphic family. -/
def variationField (v : TangentSpace IG g₀) :
    ∀ z : Z, TangentSpace IZ z :=
  fun z => mfderiv IG IZ (fun g => a (g,z)) g₀ v

include ha hId in
theorem variationField_holomorphic (v : TangentSpace IG g₀) :
    ContMDiff IZ IZ.tangent ∞
      (fun z => (⟨z, variationField IG IZ a g₀ v z⟩ : TangentBundle IZ Z)) := by
  let fv : Z → TangentBundle IG G := fun _ => ⟨g₀,v⟩
  let fz : Z → TangentBundle IZ Z := fun z => ⟨z,0⟩
  have hv : ContMDiff IZ IG.tangent ∞ fv := contMDiff_const
  have hz : ContMDiff IZ IZ.tangent ∞ fz := Bundle.contMDiff_zeroSection _ _
  let F₁ : Z → TangentBundle IG G × TangentBundle IZ Z := fun z => (fv z,fz z)
  have h₁ : ContMDiff IZ (IG.tangent.prod IZ.tangent) ∞ F₁ := hv.prodMk hz
  let F₂ := (equivTangentBundleProd IG G IZ Z).symm
  have h₂ : ContMDiff (IG.tangent.prod IZ.tangent) (IG.prod IZ).tangent ∞ F₂ :=
    contMDiff_equivTangentBundleProd_symm
  let F₃ := tangentMap (IG.prod IZ) IZ a
  have h₃ : ContMDiff (IG.prod IZ).tangent IZ.tangent ∞ F₃ :=
    ha.contMDiff_tangentMap (by simp)
  have h := (h₃.comp h₂).comp h₁
  convert h using 1
  funext z
  apply Bundle.TotalSpace.ext
  · exact (hId z).symm
  apply heq_of_eq
  change mfderiv IG IZ (fun g => a (g,z)) g₀ v =
    mfderiv (IG.prod IZ) IZ a (g₀,z) (v,0)
  rw [mfderiv_prod_eq_add_apply (ha.mdifferentiableAt (by simp))]
  simp

/-- Bundle the fundamental vector field as an actual holomorphic section
of the tangent bundle. -/
def variationSection (v : TangentSpace IG g₀) :
    ContMDiffSection IZ F ∞ (TangentSpace IZ : Z → Type _) :=
  ⟨variationField IG IZ a g₀ v, variationField_holomorphic IG IZ a g₀ ha hId v⟩

include ha hId in
/-- Surjectivity of the actual orbit derivative supplies tangent-generating
global holomorphic vector fields. The proof differentiates the family,
rather than stipulating a collection of global vector fields. -/
theorem tangent_sections_evaluation_surjective
    (hOrbit : ∀ z : Z,
      Function.Surjective (mfderiv IG IZ (fun g => a (g,z)) g₀))
    (z : Z) (w : TangentSpace IZ z) :
    ∃ X : ContMDiffSection IZ F ∞ (TangentSpace IZ : Z → Type _), X z = w := by
  obtain ⟨v,hv⟩ := hOrbit z w
  exact ⟨variationSection IG IZ a g₀ ha hId v, hv⟩

end
end QuaternionicSymmetry.HolomorphicFamilyVectorFields
