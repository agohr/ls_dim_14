import QuaternionicSymmetry.LocallyConstantRingSheaf
import QuaternionicSymmetry.SheafCechOneCocycle
import Mathlib.Topology.Homotopy.Lifting

/-! An actual locally constant additive Čech cocycle constructs a
discrete-fiber covering. A simply connected base supplies a continuous
section by the proved covering-lifting theorem. -/

namespace QuaternionicSymmetry.LocallyConstantCocycleCovering

open CategoryTheory TopologicalSpace Opposite
open LocallyConstantRingSheaf SheafCechOneCocycle
noncomputable section

variable {B R : Type} {ι : Type*} [TopologicalSpace B] [CommRing R]
  [TopologicalSpace R] [IsTopologicalRing R] [DiscreteTopology R]
  {U : ι → Opens B} (c : OneCocycle (sectionSheaf B R) U)

def scalar (i j : ι) (x : B) : R := by
  classical
  exact if hx : x ∈ U i ⊓ U j then
    (c.value i j (U i ⊓ U j) inf_le_left inf_le_right).hom ⟨x, hx⟩
  else 0

theorem scalar_of_mem (i j : ι) (x : B) (hx : x ∈ U i ⊓ U j) :
    scalar c i j x =
      (c.value i j (U i ⊓ U j) inf_le_left inf_le_right).hom ⟨x, hx⟩ :=
  dif_pos hx

theorem scalar_continuousOn (i j : ι) :
    ContinuousOn (scalar c i j) (U i ∩ U j) := by
  apply continuousOn_iff_continuous_restrict.mpr
  convert (c.value i j (U i ⊓ U j) inf_le_left inf_le_right).hom.continuous using 1
  funext x
  exact scalar_of_mem c i j x.1 x.2

theorem scalar_eq_value (i j : ι) (V : Opens B)
    (hi : V ≤ U i) (hj : V ≤ U j) (x : V) :
    scalar c i j x.1 = (c.value i j V hi hj).hom x := by
  rw [scalar_of_mem c i j x.1 ⟨hi x.2, hj x.2⟩]
  exact congrArg (fun s : (sectionSheaf B R).val.obj (op V) => s.hom x)
    (c.naturality i j (U i ⊓ U j) V (le_inf hi hj) inf_le_left inf_le_right)

theorem scalar_self (i : ι) (x : B) (hx : x ∈ U i) : scalar c i i x = 0 := by
  rw [scalar_eq_value c i i (U i) le_rfl le_rfl ⟨x, hx⟩]
  exact congrArg (fun s : (sectionSheaf B R).val.obj (op (U i)) => s.hom ⟨x, hx⟩)
    (c.self i (U i) le_rfl)

theorem scalar_comp (i j k : ι) (x : B) (hx : x ∈ (U i ⊓ U j) ⊓ U k) :
    scalar c i j x + scalar c j k x = scalar c i k x := by
  let V := (U i ⊓ U j) ⊓ U k
  have hi : V ≤ U i := inf_le_left.trans inf_le_left
  have hj : V ≤ U j := inf_le_left.trans inf_le_right
  have hk : V ≤ U k := inf_le_right
  let xx : V := ⟨x, hx⟩
  rw [scalar_eq_value c i j V hi hj xx, scalar_eq_value c j k V hj hk xx,
    scalar_eq_value c i k V hi hk xx]
  exact congrArg (fun s : (sectionSheaf B R).val.obj (op V) => s.hom xx)
    (c.cocycle i j k V hi hj hk)

variable (indexAt : B → ι) (mem_at : ∀ x : B, x ∈ U (indexAt x))

def coveringCore : FiberBundleCore ι B R where
  baseSet i := U i
  isOpen_baseSet i := (U i).isOpen
  indexAt := indexAt
  mem_baseSet_at := mem_at
  coordChange i j x v := v - scalar c i j x
  coordChange_self i x hx v := by rw [scalar_self c i x hx, sub_zero]
  continuousOn_coordChange i j :=
    continuousOn_snd.sub ((scalar_continuousOn c i j).comp continuousOn_fst
      (fun _ hx => hx.1))
  coordChange_comp i j k x hx v := by
    rw [sub_sub, scalar_comp c i j k x hx]

theorem coveringCore_isCoveringMap :
    IsCoveringMap (coveringCore c indexAt mem_at).proj :=
  FiberBundle.isCoveringMap (F := R) (E := (coveringCore c indexAt mem_at).Fiber)

theorem exists_continuous_section [SimplyConnectedSpace B] [LocPathConnectedSpace B]
    [Nonempty B] :
    ∃ s : C(B, (coveringCore c indexAt mem_at).TotalSpace),
      ∀ x : B, (s x).proj = x := by
  let x₀ : B := Classical.choice inferInstance
  obtain ⟨s, hs, _⟩ := (coveringCore_isCoveringMap c indexAt mem_at).existsUnique_continuousMap_lifts
    (ContinuousMap.id B) x₀ ⟨x₀, (0 : R)⟩ rfl
  exact ⟨s, fun x => congrFun hs.2 x⟩

end
end QuaternionicSymmetry.LocallyConstantCocycleCovering
