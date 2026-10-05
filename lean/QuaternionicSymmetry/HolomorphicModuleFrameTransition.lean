import QuaternionicSymmetry.HolomorphicModuleLocalFrame

/-! Holomorphic transition scalars obtained from actual local frames of an
arbitrary module sheaf. The scalars obey identity and cocycle laws because
all frames use the same sheaf and commute with its actual restrictions. -/

namespace QuaternionicSymmetry.HolomorphicModuleFrameTransition

open CategoryTheory TopologicalSpace Manifold Opposite
open HolomorphicLineModuleSheaf HolomorphicModuleLocalFrame
open scoped Manifold ContDiff
noncomputable section

variable {B : Type} {H F : Type*}
  [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  {IB : ModelWithCorners ℂ F H}
  {M : SheafOfModules.{0} (structureSheaf (B := B) IB)}
  {U V W : Opens B}

def localScalar (f : LocalFrame IB M U) (g : LocalFrame IB M V)
    (S : Opens B) (hSU : S ≤ U) (hSV : S ≤ V) : Functions IB S :=
  g.coordinate S hSV ((f.coordinate S hSU).symm 1)

theorem localScalar_restrict (f : LocalFrame IB M U) (g : LocalFrame IB M V)
    (S T : Opens B) (hTS : T ≤ S) (hSU : S ≤ U) (hSV : S ≤ V) :
    localScalar f g T (hTS.trans hSU) (hTS.trans hSV) =
      ContMDiffMap.restrictRingHom IB 𝓘(ℂ,ℂ) ℂ hTS (localScalar f g S hSU hSV) := by
  unfold localScalar
  rw [← f.unit_restrict S T hTS hSU]
  exact g.restrict S T hTS hSV _

/-- The transition from `f`-coordinates to `g`-coordinates. Values off
the genuine overlap are irrelevant and are set to zero. -/
def scalar (f : LocalFrame IB M U) (g : LocalFrame IB M V) (x : B) : ℂ := by
  classical
  exact if hx : x ∈ U ⊓ V then
    localScalar f g (U ⊓ V) inf_le_left inf_le_right ⟨x, hx⟩ else 0

theorem scalar_of_mem (f : LocalFrame IB M U) (g : LocalFrame IB M V)
    (x : B) (hx : x ∈ U ⊓ V) :
    scalar f g x = localScalar f g (U ⊓ V) inf_le_left inf_le_right ⟨x, hx⟩ :=
  dif_pos hx

theorem scalar_holomorphic (f : LocalFrame IB M U) (g : LocalFrame IB M V) :
    ContMDiffOn IB 𝓘(ℂ,ℂ) ∞ (scalar f g) ((U : Set B) ∩ V) := by
  have h : ContMDiff IB 𝓘(ℂ,ℂ) ∞
      (fun x : (U ⊓ V : Opens B) => scalar f g x.1) := by
    convert (localScalar f g (U ⊓ V) inf_le_left inf_le_right).contMDiff using 1
    funext x
    exact scalar_of_mem f g x.1 x.2
  intro x hx
  exact (contMDiffAt_subtype_iff.mp (h ⟨x, hx⟩)).contMDiffWithinAt

theorem scalar_eq_localScalar (f : LocalFrame IB M U) (g : LocalFrame IB M V)
    (S : Opens B) (hSU : S ≤ U) (hSV : S ≤ V) (x : S) :
    scalar f g x.1 = localScalar f g S hSU hSV x := by
  rw [scalar_of_mem f g x.1 ⟨hSU x.2, hSV x.2⟩]
  have hS : S ≤ U ⊓ V := le_inf hSU hSV
  have h := localScalar_restrict f g (U ⊓ V) S hS inf_le_left inf_le_right
  exact (congrArg (fun t : Functions IB S => t x) h).symm

theorem scalar_self (f : LocalFrame IB M U) (x : B) (hx : x ∈ U) :
    scalar f f x = 1 := by
  rw [scalar_eq_localScalar f f U le_rfl le_rfl ⟨x, hx⟩]
  simp [localScalar]

/-- The exact transition cocycle on the genuine triple overlap. -/
theorem scalar_comp (f : LocalFrame IB M U) (g : LocalFrame IB M V)
    (h : LocalFrame IB M W) (x : B) (hx : x ∈ (U ⊓ V) ⊓ W) :
    scalar g h x * scalar f g x = scalar f h x := by
  let S := (U ⊓ V) ⊓ W
  have hSU : S ≤ U := inf_le_left.trans inf_le_left
  have hSV : S ≤ V := inf_le_left.trans inf_le_right
  have hSW : S ≤ W := inf_le_right
  let xx : S := ⟨x, hx⟩
  rw [scalar_eq_localScalar g h S hSV hSW xx,
    scalar_eq_localScalar f g S hSU hSV xx,
    scalar_eq_localScalar f h S hSU hSW xx]
  exact (congrArg (fun t : Functions IB S => t xx)
    (g.coordinate_change h S hSV hSW ((f.coordinate S hSU).symm 1))).symm

theorem scalar_mul_reverse (f : LocalFrame IB M U) (g : LocalFrame IB M V)
    (x : B) (hx : x ∈ U ⊓ V) : scalar g f x * scalar f g x = 1 := by
  rw [scalar_comp f g f x ⟨hx, hx.1⟩, scalar_self f x hx.1]

theorem scalar_ne_zero (f : LocalFrame IB M U) (g : LocalFrame IB M V)
    (x : B) (hx : x ∈ U ⊓ V) : scalar f g x ≠ 0 := by
  intro hz
  have h := scalar_mul_reverse f g x hx
  rw [hz, mul_zero] at h
  exact zero_ne_one h

end
end QuaternionicSymmetry.HolomorphicModuleFrameTransition
