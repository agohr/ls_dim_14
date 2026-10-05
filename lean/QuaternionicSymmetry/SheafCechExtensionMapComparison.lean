import QuaternionicSymmetry.SheafCechExtensionUnitSections
import QuaternionicSymmetry.SheafCechCocycleComparison
import QuaternionicSymmetry.SheafShortExactSections

/-! A genuine middle map of the cocycle extensions, identity on both
end sheaves, reconstructs a coboundary comparison on the actual common
cover. The coefficient sections are unique kernel preimages, not new data
assumed from equality of derived classes. -/

namespace QuaternionicSymmetry.SheafCechExtensionMapComparison

open CategoryTheory TopologicalSpace Opposite
open AbelianSheafCohomology SheafCechOneCocycle SheafCechExtension
open SheafCechExtensionUnitSections SheafCechCocycleComparison SheafShortExactSections
noncomputable section

variable {B : Type} [TopologicalSpace B] {ι κ : Type}
  {A : TopCat.Sheaf AddCommGrpCat (TopCat.of B)}
  {U : ι → Opens B} {V : κ → Opens B}
  (c : OneCocycle A U) (d : OneCocycle A V)
  (hd : ∀ x : B, ∃ a, x ∈ V a)
  (k : (extensionComplex c).X₂ ⟶ (extensionComplex d).X₂)
  (hkg : k ≫ (extensionComplex d).g = (extensionComplex c).g)

def difference (i : ι) (a : κ) (W : Opens B) (hi : W ≤ U i) (ha : W ≤ V a) :
    (extensionComplex d).X₂.val.obj (op W) :=
  k.val.app (op W) (unitLift c i W hi) - unitLift d a W ha

include hkg in
theorem difference_kernel (i : ι) (a : κ) (W : Opens B)
    (hi : W ≤ U i) (ha : W ≤ V a) :
    (extensionComplex d).g.val.app (op W) (difference c d k i a W hi ha) = 0 := by
  have hg := congrArg (fun φ => φ.val.app (op W) (unitLift c i W hi)) hkg
  change (extensionComplex d).g.val.app (op W)
      (k.val.app (op W) (unitLift c i W hi)) =
    (extensionComplex c).g.val.app (op W) (unitLift c i W hi) at hg
  change ((extensionComplex d).g.val.app (op W)).hom (_ - _) = 0
  rw [map_sub, hg, unitLift_projection, unitLift_projection, sub_self]

def value (i : ι) (a : κ) (W : Opens B) (hi : W ≤ U i) (ha : W ≤ V a) :
    A.val.obj (op W) :=
  kernelSection (extensionComplex_shortExact d hd) W (difference c d k i a W hi ha)
    (difference_kernel c d k hkg i a W hi ha)

@[simp] theorem inclusion_value (i : ι) (a : κ) (W : Opens B)
    (hi : W ≤ U i) (ha : W ≤ V a) :
    (extensionComplex d).f.val.app (op W) (value c d hd k hkg i a W hi ha) =
      difference c d k i a W hi ha :=
  inclusion_kernelSection (extensionComplex_shortExact d hd) W _ _

theorem difference_restrict (i : ι) (a : κ) {W T : Opens B} (hTW : T ≤ W)
    (hi : W ≤ U i) (ha : W ≤ V a) :
    restrict (extensionComplex d).X₂ hTW (difference c d k i a W hi ha) =
      difference c d k i a T (hTW.trans hi) (hTW.trans ha) := by
  change (restrict (extensionComplex d).X₂ hTW).hom (_ - _) = _
  rw [map_sub, ← map_restrict, unitLift_restrict, unitLift_restrict]
  rfl

variable (hkf : (extensionComplex c).f ≫ k = (extensionComplex d).f)

def comparison : Comparison c d where
  value := value c d hd k hkg
  naturality i a W T hTW hi ha := by
    apply inclusion_injective (extensionComplex_shortExact d hd) T
    calc
      _ = restrict (extensionComplex d).X₂ hTW
          ((extensionComplex d).f.val.app (op W) (value c d hd k hkg i a W hi ha)) :=
        map_restrict (extensionComplex d).f hTW _
      _ = _ := by rw [inclusion_value, inclusion_value, difference_restrict]
  compatibility i j a b W hi hj ha hb := by
    apply inclusion_injective (extensionComplex_shortExact d hd) W
    change ((extensionComplex d).f.val.app (op W)).hom (_ + _) =
      ((extensionComplex d).f.val.app (op W)).hom (_ + _)
    rw [map_add, map_add, inclusion_value, inclusion_value]
    have hC : (extensionComplex d).f.val.app (op W) (c.value i j W hi hj) =
        k.val.app (op W) (unitLift c i W hi) -
          k.val.app (op W) (unitLift c j W hj) := by
      have hf := congrArg (fun φ => φ.val.app (op W) (c.value i j W hi hj)) hkf
      change k.val.app (op W)
          ((extensionComplex c).f.val.app (op W) (c.value i j W hi hj)) =
        (extensionComplex d).f.val.app (op W) (c.value i j W hi hj) at hf
      rw [← hf, ← unitLift_sub]
      exact map_sub (k.val.app (op W)).hom _ _
    rw [hC, ← unitLift_sub d a b W ha hb]
    dsimp only [difference]
    abel

end
end QuaternionicSymmetry.SheafCechExtensionMapComparison
