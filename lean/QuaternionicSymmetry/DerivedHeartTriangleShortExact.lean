import QuaternionicSymmetry.DerivedHeartExtensionTriangles
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! A distinguished triangle between single objects in degree zero is
an actual short exact sequence in the original abelian category. Exactness
and both mono/epi conditions are obtained from true derived homology. -/

namespace QuaternionicSymmetry.DerivedHeartTriangleShortExact

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open DerivedCategory
noncomputable section

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

theorem shortExact_of_single_triangle {X M Y : C}
    (f : X ⟶ M) (g : M ⟶ Y) (hfg : f ≫ g = 0)
    (δ : (singleFunctor C 0).obj Y ⟶ ((singleFunctor C 0).obj X)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk ((singleFunctor C 0).map f)
      ((singleFunctor C 0).map g) δ ∈ distTriang (DerivedCategory C)) :
    (ShortComplex.mk f g hfg).ShortExact := by
  let F := singleFunctor C 0
  let H := homologyFunctor C 0
  let S := ShortComplex.mk f g hfg
  let T := Triangle.mk (F.map f) (F.map g) δ
  have hm : Mono (H.map (F.map f)) := by
    apply (HomologySequence.mono_homologyMap_mor₁_iff T hT (-1) 0 (by omega)).2
    exact (DerivedCategory.isZero_of_isGE (F.obj Y) 0 (-1) (by omega)).eq_of_src _ _
  have he : Epi (H.map (F.map g)) := by
    apply (HomologySequence.epi_homologyMap_mor₂_iff T hT 0 1 rfl).2
    exact (DerivedCategory.isZero_of_isLE (F.obj X) 0 1 (by omega)).eq_of_tgt _ _
  have hS : (S.map (F ⋙ H)).ShortExact := {
    exact := H.map_distinguished_exact T hT
    mono_f := hm
    epi_g := he }
  exact ShortComplex.shortExact_of_iso
    (S.mapNatIso (singleFunctorCompHomologyFunctorIso C 0)) hS

end
end QuaternionicSymmetry.DerivedHeartTriangleShortExact
