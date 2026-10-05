import QuaternionicSymmetry.ManifoldTwistorFixedTangentSmooth

/-!
# Coordinates on the tangent bundle of a base–sphere product

The natural reordering of a product tangent bundle into base position,
base direction, and genuine sphere tangent is smooth in both directions.
This gives the fixed-chart local complex operator a manifold-compatible
domain and codomain.
-/

namespace QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
open QuaternionicSymmetry.ManifoldTwistorCoefficientSphere
open scoped Manifold ContDiff
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
 [Nontrivial E] [FiniteDimensional ℝ E]
private abbrev I := (𝓘(ℝ,E)).prod (𝓡 2)

def productTangentCoordinates :
    TangentBundle (I (E := E)) (E × geometricSphere) → X (E := E) :=
  fun t => ((t.1.1,t.2.1),⟨t.1.2,t.2.2⟩)

omit [Nontrivial E] [FiniteDimensional ℝ E] in
theorem productTangentCoordinates_smooth :
    ContMDiff (I (E := E)).tangent (IX (E := E)) ∞
      (productTangentCoordinates (E := E)) := by
  have hprod : ContMDiff (I (E := E)).tangent
      ((𝓘(ℝ,E)).tangent.prod (𝓡 2).tangent) ∞
      (equivTangentBundleProd 𝓘(ℝ,E) E (𝓡 2) geometricSphere) :=
    contMDiff_equivTangentBundleProd
  have hbase : ContMDiff (𝓘(ℝ,E)).tangent 𝓘(ℝ,E) ∞
      (fun t : TangentBundle 𝓘(ℝ,E) E => t.1) :=
    Bundle.contMDiff_proj (TangentSpace 𝓘(ℝ,E))
  have hdir : ContMDiff (𝓘(ℝ,E)).tangent 𝓘(ℝ,E) ∞
      (fun t : TangentBundle 𝓘(ℝ,E) E => t.2) :=
    contMDiff_snd_tangentBundle_modelSpace E 𝓘(ℝ,E)
  have hsecond : ContMDiff
      ((𝓘(ℝ,E)).tangent.prod (𝓡 2).tangent)
      ((𝓘(ℝ,E)).prod 𝓘(ℝ,E)) ∞
      (fun t : TangentBundle 𝓘(ℝ,E) E × TangentBundle (𝓡 2) geometricSphere =>
        (t.1.1,t.1.2)) := by
    have hf : ContMDiff ((𝓘(ℝ,E)).tangent.prod (𝓡 2).tangent)
        (𝓘(ℝ,E)).tangent ∞
        (fun t : TangentBundle 𝓘(ℝ,E) E × TangentBundle (𝓡 2) geometricSphere => t.1) :=
      contMDiff_fst
    exact (hbase.comp hf).prodMk (hdir.comp hf)
  have hthird : ContMDiff
      ((𝓘(ℝ,E)).tangent.prod (𝓡 2).tangent)
      (𝓡 2).tangent ∞
      (fun t : TangentBundle 𝓘(ℝ,E) E × TangentBundle (𝓡 2) geometricSphere => t.2) :=
    contMDiff_snd
  exact (hsecond.prodMk hthird).comp hprod

def productTangentCoordinatesInv :
    X (E := E) → TangentBundle (I (E := E)) (E × geometricSphere) :=
  fun z => ⟨(z.1.1,z.2.1),(z.1.2,z.2.2)⟩

omit [Nontrivial E] [FiniteDimensional ℝ E] in
theorem productTangentCoordinatesInv_smooth :
    ContMDiff (IX (E := E)) (I (E := E)).tangent ∞
      (productTangentCoordinatesInv (E := E)) := by
  have hleft : ContMDiff ((𝓘(ℝ,E)).prod 𝓘(ℝ,E))
      (𝓘(ℝ,E)).tangent ∞
      ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ,E)).symm :
      E × E → TangentBundle 𝓘(ℝ,E) E) :=
    contMDiff_tangentBundleModelSpaceHomeomorph_symm
  have hid : ContMDiff ((𝓘(ℝ,E)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E × E) ∞
      (fun x : E × E => x) :=
    contMDiff_fst.prodMk_space contMDiff_snd
  have hleft' : ContMDiff (IX (E := E)) (𝓘(ℝ,E)).tangent ∞
      (fun z : X (E := E) =>
        (tangentBundleModelSpaceHomeomorph 𝓘(ℝ,E)).symm z.1) :=
    hleft.comp (hid.comp
      (contMDiff_fst (I := (𝓘(ℝ,E)).prod 𝓘(ℝ,E))
        (J := (𝓡 2).tangent) (M := E × E)
        (N := TangentBundle (𝓡 2) geometricSphere)))
  have hright : ContMDiff (IX (E := E)) (𝓡 2).tangent ∞
      (fun z : X (E := E) => z.2) := contMDiff_snd
  exact (contMDiff_equivTangentBundleProd_symm
    (I := 𝓘(ℝ,E)) (I' := 𝓡 2) (M := E) (M' := geometricSphere)).comp
      (hleft'.prodMk hright)

omit [Nontrivial E] [FiniteDimensional ℝ E] in
@[simp] theorem productTangentCoordinates_left_inverse
    (t : TangentBundle (I (E := E)) (E × geometricSphere)) :
    productTangentCoordinatesInv (productTangentCoordinates t) = t := by
  cases t with
  | mk p v =>
    cases p
    cases v
    rfl

omit [Nontrivial E] [FiniteDimensional ℝ E] in
@[simp] theorem productTangentCoordinates_right_inverse
    (t : X (E := E)) :
    productTangentCoordinates (productTangentCoordinatesInv t) = t := by
  rcases t with ⟨⟨y,u⟩,⟨s,v⟩⟩
  rfl
end
end QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
