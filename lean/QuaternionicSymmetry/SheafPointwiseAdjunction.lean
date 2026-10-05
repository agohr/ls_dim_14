import Mathlib.CategoryTheory.Sites.Adjunction

/-! An adjunction whose two coefficient functors preserve sheaves lifts
pointwise to the actual sheaf categories, without any sheafification or
comparison assumption. -/

namespace QuaternionicSymmetry.SheafPointwiseAdjunction

open CategoryTheory
noncomputable section

variable {C A B : Type*} [Category* C] [Category* A] [Category* B]
  (J : GrothendieckTopology C) {F : A ⥤ B} {G : B ⥤ A}
  [J.HasSheafCompose F] [J.HasSheafCompose G] (adj : F ⊣ G)

def sheafAdjunction : sheafCompose J F ⊣ sheafCompose J G where
  unit :=
    { app := fun P => ⟨{
        app := fun U => adj.unit.app (P.val.obj U)
        naturality := fun U V f => adj.unit.naturality (P.val.map f) }⟩
      naturality := fun P Q f => by
        apply Sheaf.Hom.ext
        ext U
        exact adj.unit.naturality (f.val.app U) }
  counit :=
    { app := fun P => ⟨{
        app := fun U => adj.counit.app (P.val.obj U)
        naturality := fun U V f => adj.counit.naturality (P.val.map f) }⟩
      naturality := fun P Q f => by
        apply Sheaf.Hom.ext
        ext U
        exact adj.counit.naturality (f.val.app U) }
  left_triangle_components P := by
    apply Sheaf.Hom.ext
    ext U
    exact adj.left_triangle_components (P.val.obj U)
  right_triangle_components P := by
    apply Sheaf.Hom.ext
    ext U
    exact adj.right_triangle_components (P.val.obj U)

end
end QuaternionicSymmetry.SheafPointwiseAdjunction
