import QuaternionicSymmetry.IntegralSheafLocalUnitLift

/-! Local lifts of the integral unit in an actual short exact sequence
produce a cocycle in its original coefficient sheaf. The sign is chosen
so that a twisted section (n,bᵢ) maps locally to f(bᵢ) + n sᵢ. -/

namespace QuaternionicSymmetry.SheafExtensionCocycle

open CategoryTheory TopologicalSpace Opposite
open AbelianSheafCohomology SheafCechOneCocycle SheafShortExactSections
open IntegralSheafLocalUnitLift
noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type}
  {A M : AbelianSheaves B} (f : A ⟶ M) (g : M ⟶ integralSheaf B)
  (hfg : f ≫ g = 0) (hS : (ShortComplex.mk f g hfg).ShortExact)
  {U : ι → Opens B} (s : ∀ i, M.val.obj (op (U i)))
  (hs : ∀ i, g.val.app (op (U i)) (s i) = unitSection (U i))

def difference (i j : ι) (V : Opens B) (hi : V ≤ U i) (hj : V ≤ U j) :
    M.val.obj (op V) := restrict M hi (s i) - restrict M hj (s j)

include hs in
theorem difference_kernel (i j : ι) (V : Opens B) (hi : V ≤ U i) (hj : V ≤ U j) :
    g.val.app (op V) (difference s i j V hi hj) = 0 := by
  change (g.val.app (op V)).hom (_ - _) = 0
  rw [map_sub, map_restrict, map_restrict, hs, hs,
    unitSection_restrict, unitSection_restrict, sub_self]

def value (i j : ι) (V : Opens B) (hi : V ≤ U i) (hj : V ≤ U j) :
    A.val.obj (op V) :=
  kernelSection hS V (difference s i j V hi hj)
    (difference_kernel g s hs i j V hi hj)

@[simp] theorem inclusion_value (i j : ι) (V : Opens B)
    (hi : V ≤ U i) (hj : V ≤ U j) :
    f.val.app (op V) (value f g hfg hS s hs i j V hi hj) =
      difference s i j V hi hj :=
  inclusion_kernelSection hS V _ _

def cocycle : OneCocycle A U where
  value := value f g hfg hS s hs
  naturality i j V W hWV hi hj := by
    apply inclusion_injective hS W
    rw [map_restrict, inclusion_value, inclusion_value]
    change (restrict M hWV).hom (_ - _) = _
    rw [map_sub]
    change restrict M hWV (restrict M hi (s i)) -
      restrict M hWV (restrict M hj (s j)) = _
    rw [restrict_restrict, restrict_restrict]
    rfl
  cocycle i j k V hi hj hk := by
    apply inclusion_injective hS V
    change (f.val.app (op V)).hom (_ + _) = _
    rw [map_add, inclusion_value, inclusion_value, inclusion_value]
    dsimp only [difference]
    abel

/-- The covering and lifts are obtained from the actual epimorphism;
they are not additional hypotheses on the extension. -/
def canonicalCocycle : OneCocycle A (@liftOpen B _ M g hS.epi_g) := by
  letI := hS.epi_g
  exact cocycle f g hfg hS (localUnitLift g) (localUnitLift_image g)

end
end QuaternionicSymmetry.SheafExtensionCocycle
