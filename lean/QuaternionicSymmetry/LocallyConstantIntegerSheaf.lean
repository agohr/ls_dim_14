import Mathlib.Topology.Sheaves.CommRingCat
import Mathlib.Topology.Sheaves.LocalPredicate
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Ring.Limits

/-! The actual abelian sheaf of locally constant integers on a topological
space. It is constructed as continuous maps to the discrete topological
ring of integers; the local-constant interpretation is explicit. Comparison
with categorical sheafification of the constant presheaf is separate. -/

namespace QuaternionicSymmetry.LocallyConstantIntegerSheaf

open CategoryTheory TopologicalSpace Opposite
noncomputable section

variable (B : Type) [TopologicalSpace B]

def integerPresheaf : TopCat.Presheaf AddCommGrpCat (TopCat.of B) :=
  TopCat.presheafToTopCommRing (TopCat.of B) (TopCommRingCat.of ℤ) ⋙
    forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat

theorem integerPresheaf_isSheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology (TopCat.of B))
      (integerPresheaf B) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget AddCommGrpCat)]
  exact (TopCat.sheafToTop (X := TopCat.of B) (TopCat.of ℤ)).cond

def integerSheaf : TopCat.Sheaf AddCommGrpCat (TopCat.of B) :=
  ⟨integerPresheaf B, integerPresheaf_isSheaf B⟩

def sectionLocallyConstant (U : Opens B)
    (s : (integerSheaf B).val.obj (op U)) : LocallyConstant U ℤ :=
  ⟨s.hom, (IsLocallyConstant.iff_continuous _).mpr s.hom.continuous⟩

def locallyConstantSection (U : Opens B) (s : LocallyConstant U ℤ) :
    (integerSheaf B).val.obj (op U) := TopCat.ofHom s.toContinuousMap

def sectionEquiv (U : Opens B) :
    (integerSheaf B).val.obj (op U) ≃ LocallyConstant U ℤ where
  toFun := sectionLocallyConstant B U
  invFun := locallyConstantSection B U
  left_inv _ := rfl
  right_inv _ := rfl

end
end QuaternionicSymmetry.LocallyConstantIntegerSheaf
