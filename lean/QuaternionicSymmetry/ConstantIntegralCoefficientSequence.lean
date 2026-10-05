import QuaternionicSymmetry.IntegerCoefficientExactSequence
import QuaternionicSymmetry.AbelianSheafCohomology
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! The integral multiplication/reduction sequence remains short exact
after taking actual constant sheaves. Its first map is literally integer
multiplication, not an unspecified map between isomorphic coefficients. -/

namespace QuaternionicSymmetry.ConstantIntegralCoefficientSequence

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AbelianSheafCohomology IntegerCoefficientExactSequence
noncomputable section

variable (B : Type) [TopologicalSpace B]

def constantCoefficients : AddCommGrpCat ⥤ AbelianSheaves B :=
  constantSheaf (Opens.grothendieckTopology (TopCat.of B)) AddCommGrpCat

instance : (constantCoefficients B).Additive := by
  letI : (Functor.const (Opens (TopCat.of B))ᵒᵖ :
      AddCommGrpCat ⥤ _).Additive := {
    map_add := by intros; rfl }
  dsimp [constantCoefficients, constantSheaf]
  infer_instance

instance : PreservesFiniteLimits (constantCoefficients B) := by
  dsimp [constantCoefficients, constantSheaf]
  exact comp_preservesFiniteLimits _ _

instance : PreservesFiniteColimits (constantCoefficients B) := by
  dsimp [constantCoefficients, constantSheaf]
  exact comp_preservesFiniteColimits _ _

def finiteCoefficientSheaf (k : ℕ) : AbelianSheaves B :=
  (constantCoefficients B).obj (AddCommGrpCat.of (ZMod k))

def integralCoefficientComplex (k : ℕ) : ShortComplex (AbelianSheaves B) :=
  (coefficientComplex k).map (constantCoefficients B)

theorem integralCoefficientComplex_shortExact (k : ℕ) (hk : k ≠ 0) :
    (integralCoefficientComplex B k).ShortExact :=
  (coefficientComplex_shortExact k hk).map_of_exact (constantCoefficients B)

theorem integralCoefficientComplex_f (k : ℕ) :
    (integralCoefficientComplex B k).f = k • 𝟙 (integralSheaf B) := by
  change (constantCoefficients B).map (k • 𝟙 integralCoefficient) = _
  rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
  rfl

end
end QuaternionicSymmetry.ConstantIntegralCoefficientSequence
