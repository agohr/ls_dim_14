import QuaternionicSymmetry.HolomorphicLineModuleTensorPresheaf
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Sites.LeftExact

/-! The actual holomorphic-function sheaf and its sheaf of units as
abelian-group-valued sheaves. Sections of the latter are genuine units
of the ring of holomorphic functions, not pointwise nonzero functions
with an unproved holomorphic inverse. -/

namespace QuaternionicSymmetry.HolomorphicUnitSheaf

open CategoryTheory TopologicalSpace Manifold Opposite
open HolomorphicLineModuleSheaf HolomorphicLineModuleTensorPresheaf
open scoped Manifold ContDiff
noncomputable section

private instance : CategoryTheory.Limits.PreservesLimits
    (forget₂ CommRingCat.{0} CommMonCat.{0}) := by
  letI : CategoryTheory.Limits.ReflectsLimits (forget CommMonCat.{0}) :=
    CategoryTheory.Limits.reflectsLimits_of_reflectsIsomorphisms
  letI : CategoryTheory.Limits.PreservesLimits
      (forget₂ CommRingCat.{0} CommMonCat.{0} ⋙ forget CommMonCat) :=
    inferInstanceAs (CategoryTheory.Limits.PreservesLimits (forget CommRingCat.{0}))
  exact CategoryTheory.Limits.preservesLimits_of_reflects_of_preserves
    (forget₂ CommRingCat CommMonCat) (forget CommMonCat)

variable {B : Type} {H F : Type*}
  [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)

/-- The additive sheaf of actual holomorphic scalar functions. -/
def functionSheaf : TopCat.Sheaf AddCommGrpCat (TopCat.of B) :=
  (sheafCompose (Opens.grothendieckTopology (TopCat.of B))
    (forget₂ RingCat AddCommGrpCat)).obj (structureSheaf (B := B) IB)

/-- The genuine multiplicative-unit sheaf, written additively so that it
can be used in the existing abelian-sheaf cohomology category. -/
def unitSheaf : TopCat.Sheaf AddCommGrpCat (TopCat.of B) :=
  (sheafCompose (Opens.grothendieckTopology (TopCat.of B))
    (forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units ⋙
      commGroupAddCommGroupEquivalence.functor)).obj
      (structureCommSheaf (B := B) IB)

/-- A section is exactly a ring unit of holomorphic functions. -/
def unitSectionEquiv (U : Opens B) :
    (unitSheaf (B := B) IB).val.obj (op U) ≃+ Additive (Functions IB U)ˣ :=
  AddEquiv.refl _

theorem unit_restrict (U V : Opens B) (hVU : V ≤ U)
    (s : Additive (Functions IB U)ˣ) :
    (unitSheaf (B := B) IB).val.map (homOfLE hVU).op s =
      Additive.ofMul (Units.map
        (ContMDiffMap.restrictRingHom IB 𝓘(ℂ,ℂ) ℂ hVU).toMonoidHom s.toMul) := rfl

theorem unit_value_ne_zero (U : Opens B) (s : (Functions IB U)ˣ) (x : U) :
    (s.val x : ℂ) ≠ 0 := by
  have h := congrArg (fun f : Functions IB U => f x) s.val_inv
  change s.val x * s.inv x = 1 at h
  intro hz
  rw [hz, zero_mul] at h
  exact zero_ne_one h

end
end QuaternionicSymmetry.HolomorphicUnitSheaf
