import QuaternionicSymmetry.HolomorphicExponentialSheaf
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! Every actual holomorphic unit admits a holomorphic logarithm near
each point. The logarithm uses a branch near the normalized value `1`,
so no global branch or global logarithm is assumed. -/

namespace QuaternionicSymmetry.HolomorphicLocalLogarithm

open CategoryTheory TopologicalSpace Manifold
open HolomorphicLineModuleSheaf HolomorphicUnitSheaf HolomorphicExponentialSheaf
open scoped Manifold ContDiff
noncomputable section

variable {B : Type} {H F : Type*}
  [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)

theorem exists_local_log (U : Opens B) (s : (Functions IB U)ˣ) (x : U) :
    ∃ (V : Opens B) (hVU : V ≤ U), x.1 ∈ V ∧
      ∃ g : Functions IB V, ∀ y : V,
        Complex.exp (g y) = s.val ⟨y.1, hVU y.2⟩ := by
  let f : Functions IB U := s.val
  have hx0 : f x ≠ 0 := unit_value_ne_zero IB U s x
  let T : Set U := (fun y : U => f y / f x) ⁻¹' Complex.slitPlane
  have hT : IsOpen T := Complex.isOpen_slitPlane.preimage
    (f.contMDiff.continuous.div_const (f x))
  let V : Opens B := ⟨Subtype.val '' T, U.isOpen.isOpenMap_subtype_val _ hT⟩
  have hVU : V ≤ U := by
    rintro y ⟨z, _, rfl⟩
    exact z.2
  have hxV : x.1 ∈ V := ⟨x, by simp [T, hx0], rfl⟩
  have hslit (y : V) : f ⟨y.1, hVU y.2⟩ / f x ∈ Complex.slitPlane := by
    obtain ⟨z, hz, heq⟩ := y.2
    have hz' : (⟨y.1, hVU y.2⟩ : U) = z := Subtype.ext heq.symm
    rw [hz']
    exact hz
  have hnorm : ContMDiff IB 𝓘(ℂ,ℂ) ∞
      (fun y : V => f ⟨y.1, hVU y.2⟩ / f x) := by
    exact (f.contMDiff.comp (contMDiff_inclusion hVU)).div_const (f x)
  have hlog : ContMDiff IB 𝓘(ℂ,ℂ) ∞
      (fun y : V => Complex.log (f ⟨y.1, hVU y.2⟩ / f x)) := by
    intro y
    exact (Complex.contDiffAt_log (hslit y)).contMDiffAt.comp y (hnorm y)
  let g : Functions IB V := ⟨fun y => Complex.log (f x) +
    Complex.log (f ⟨y.1, hVU y.2⟩ / f x), contMDiff_const.add hlog⟩
  refine ⟨V, hVU, hxV, g, ?_⟩
  intro y
  change Complex.exp (Complex.log (f x) +
    Complex.log (f ⟨y.1, hVU y.2⟩ / f x)) = f ⟨y.1, hVU y.2⟩
  rw [Complex.exp_add, Complex.exp_log hx0,
    Complex.exp_log (Complex.slitPlane_ne_zero (hslit y))]
  exact mul_div_cancel₀ _ hx0

end
end QuaternionicSymmetry.HolomorphicLocalLogarithm
