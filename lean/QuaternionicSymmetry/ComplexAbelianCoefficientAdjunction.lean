import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Analysis.Complex.Basic

/-! The actual complexification/forgetful adjunction on small coefficient
categories. Complexification is exact because ℂ is a flat ℤ-module. The
forgetful functor also has a right adjoint, so it preserves colimits as
well as limits. No sheaf-cohomology comparison is assumed here. -/

namespace QuaternionicSymmetry.ComplexAbelianCoefficientAdjunction

open CategoryTheory CategoryTheory.Limits
noncomputable section

abbrev integerEquivalence : ModuleCat.{0} ℤ ≌ AddCommGrpCat.{0} :=
  (forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat.{0}).asEquivalence

abbrev complexification : AddCommGrpCat.{0} ⥤ ModuleCat.{0} ℂ :=
  integerEquivalence.inverse ⋙ ModuleCat.extendScalars (Int.castRingHom ℂ)

abbrev underlying : ModuleCat.{0} ℂ ⥤ AddCommGrpCat.{0} :=
  ModuleCat.restrictScalars (Int.castRingHom ℂ) ⋙ integerEquivalence.functor

abbrev coinduction : AddCommGrpCat.{0} ⥤ ModuleCat.{0} ℂ :=
  integerEquivalence.inverse ⋙ ModuleCat.coextendScalars (Int.castRingHom ℂ)

def complexificationAdjunction : complexification ⊣ underlying :=
  integerEquivalence.symm.toAdjunction.comp
    (ModuleCat.extendRestrictScalarsAdj (Int.castRingHom ℂ))

def underlyingAdjunction : underlying ⊣ coinduction :=
  (ModuleCat.restrictCoextendScalarsAdj (Int.castRingHom ℂ)).comp
    integerEquivalence.toAdjunction

instance : underlying.IsRightAdjoint := complexificationAdjunction.isRightAdjoint
instance : underlying.IsLeftAdjoint := underlyingAdjunction.isLeftAdjoint
instance : complexification.IsLeftAdjoint := complexificationAdjunction.isLeftAdjoint
instance : coinduction.IsRightAdjoint := underlyingAdjunction.isRightAdjoint

instance : underlying.Additive where
  map_add := by intro X Y f g; rfl

instance : complexification.Additive := complexificationAdjunction.left_adjoint_additive

instance : PreservesFiniteLimits complexification := by
  have hflat : (Int.castRingHom ℂ).Flat := by
    change (algebraMap ℤ ℂ).Flat
    exact RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat ℤ ℂ)
  letI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
  exact comp_preservesFiniteLimits _ _

/-- Restriction of integer scalars does not change the underlying additive
group, so the composite above is the ordinary forgetful functor. -/
def underlyingIsoForget : underlying ≅ forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0} :=
  Iso.refl _

end
end QuaternionicSymmetry.ComplexAbelianCoefficientAdjunction
