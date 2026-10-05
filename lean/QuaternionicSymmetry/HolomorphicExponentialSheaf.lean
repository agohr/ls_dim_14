import QuaternionicSymmetry.HolomorphicUnitSheaf
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! The actual complex exponential gives a morphism from the additive
holomorphic function sheaf to its genuine unit sheaf. Local logarithms
and the exact integer kernel are separate analytic steps. -/

namespace QuaternionicSymmetry.HolomorphicExponentialSheaf

open CategoryTheory TopologicalSpace Manifold Opposite
open HolomorphicLineModuleSheaf HolomorphicUnitSheaf
open scoped Manifold ContDiff
noncomputable section

variable {B : Type} {H F : Type*}
  [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)

def expFunction {U : Opens B} (f : Functions IB U) : Functions IB U :=
  ⟨fun x => Complex.exp (f x), Complex.contDiff_exp.contMDiff.comp f.contMDiff⟩

def expUnit {U : Opens B} (f : Functions IB U) : (Functions IB U)ˣ where
  val := expFunction IB f
  inv := expFunction IB (-f)
  val_inv := by
    apply Subtype.ext
    funext x
    change Complex.exp (f x) * Complex.exp (-(f x)) = (1 : ℂ)
    exact (Complex.exp_add (f x) (-(f x))).symm.trans (by simp)
  inv_val := by
    apply Subtype.ext
    funext x
    change Complex.exp (-(f x)) * Complex.exp (f x) = (1 : ℂ)
    exact (Complex.exp_add (-(f x)) (f x)).symm.trans (by simp)

def expAddHom (U : Opens B) : Functions IB U →+ Additive (Functions IB U)ˣ where
  toFun f := Additive.ofMul (expUnit IB f)
  map_zero' := by
    apply Units.ext
    apply Subtype.ext
    funext x
    exact Complex.exp_zero
  map_add' f g := by
    apply Units.ext
    apply Subtype.ext
    funext x
    exact Complex.exp_add (f x) (g x)

/-- The genuine sheaf exponential; addition in the target is unit
multiplication, and every restriction square commutes literally. -/
def exponential : functionSheaf (B := B) IB ⟶ unitSheaf (B := B) IB where
  val := {
    app := fun U => AddCommGrpCat.ofHom (expAddHom IB U.unop)
    naturality := by
      intro U V j
      apply AddCommGrpCat.ext
      intro f
      apply Units.ext
      rfl }

theorem exponential_app (U : Opens B) (f : Functions IB U) :
    (exponential (B := B) IB).val.app (op U) f = Additive.ofMul (expUnit IB f) := rfl

end
end QuaternionicSymmetry.HolomorphicExponentialSheaf
