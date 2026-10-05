import QuaternionicSymmetry.LocallyConstantIntegerSheaf
import QuaternionicSymmetry.HolomorphicIntegerPeriods
import QuaternionicSymmetry.AbelianSheafCategory

/-! The actual integer-period inclusion is a morphism of abelian sheaves,
injective on every open set, whose composite with the holomorphic
exponential is zero. -/

namespace QuaternionicSymmetry.HolomorphicIntegerSheafInclusion

open CategoryTheory TopologicalSpace Manifold Opposite
open HolomorphicLineModuleSheaf HolomorphicUnitSheaf
open HolomorphicExponentialSheaf HolomorphicIntegerPeriods
open LocallyConstantIntegerSheaf ComplexExponentialIntegerKernel
open scoped Manifold ContDiff
noncomputable section

variable {B : Type} {H F : Type*}
  [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)

def integerPeriodAddHom (U : Opens B) :
    (integerSheaf B).val.obj (op U) →+ Functions IB U where
  toFun s := periodFunction IB (sectionLocallyConstant B U s)
  map_zero' := by
    apply Subtype.ext
    funext x
    change ((0 : ℤ) : ℂ) * period = 0
    simp
  map_add' s t := by
    apply Subtype.ext
    funext x
    change (Int.cast (s.hom x + t.hom x) : ℂ) * period =
      Int.cast (s.hom x) * period + Int.cast (t.hom x) * period
    rw [Int.cast_add, add_mul]

def integerInclusion : integerSheaf B ⟶ functionSheaf (B := B) IB where
  val := {
    app := fun U => AddCommGrpCat.ofHom (integerPeriodAddHom IB U.unop)
    naturality := by
      intro U V j
      apply AddCommGrpCat.ext
      intro s
      rfl }

theorem integerInclusion_app_injective (U : Opens B) :
    Function.Injective ((integerInclusion IB).val.app (op U)) := by
  intro s t h
  apply (sectionEquiv B U).injective
  exact periodFunction_injective IB U h

theorem integerInclusion_exponential :
    integerInclusion (B := B) IB ≫ exponential IB = 0 := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.ext
  intro s
  apply Units.ext
  apply Subtype.ext
  funext x
  exact exp_integer_period (s.hom x)

theorem exponential_section_kernel (U : Opens B) (f : Functions IB U) :
    expAddHom IB U f = 0 ↔
      ∃ s : (integerSheaf B).val.obj (op U), integerPeriodAddHom IB U s = f := by
  constructor
  · intro h
    have he : ∀ x, Complex.exp (f x) = 1 := by
      intro x
      exact congrArg (fun s : Additive (Functions IB U)ˣ => s.toMul.val x) h
    obtain ⟨k, hk⟩ := (exponential_kernel_iff IB f).mp he
    exact ⟨locallyConstantSection B U k, hk⟩
  · rintro ⟨s, rfl⟩
    apply Units.ext
    apply Subtype.ext
    funext x
    exact exp_integer_period (s.hom x)

end
end QuaternionicSymmetry.HolomorphicIntegerSheafInclusion
