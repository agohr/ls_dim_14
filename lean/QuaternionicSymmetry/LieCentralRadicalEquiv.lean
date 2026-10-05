import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.Solvable
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Complex.Basic

/-! A finite-dimensional complex Lie-algebra equivalence transports the
central-radical condition. This is proved by mapping the actual solvable
radical ideal, not supplied as a new geometry or classification premise. -/

namespace QuaternionicSymmetry.LieCentralRadicalEquiv

open LieAlgebra
noncomputable section

variable {L L' : Type*} [LieRing L] [LieAlgebra ℂ L]
  [LieRing L'] [LieAlgebra ℂ L']
  [FiniteDimensional ℂ L]

theorem hasCentralRadical_of_lieEquiv
    (e : L ≃ₗ⁅ℂ⁆ L') (h : HasCentralRadical ℂ L') :
    HasCentralRadical ℂ L := by
  let I : LieIdeal ℂ L := radical ℂ L
  let J : LieIdeal ℂ L' := I.map e.toLieHom
  let fIJ : I →ₗ⁅ℂ⁆ J := {
    toFun := fun z => ⟨e z, LieIdeal.mem_map z.property⟩
    map_add' := by intro a b; ext; simp
    map_smul' := by intro c a; ext; simp
    map_lie' := by intro a b; ext; exact e.map_lie a b }
  have hfSurj : Function.Surjective fIJ := by
    intro y
    obtain ⟨z,hz⟩ := LieIdeal.mem_map_of_surjective e.surjective y.property
    exact ⟨z,Subtype.ext hz⟩
  haveI : IsSolvable I := inferInstance
  haveI : IsSolvable J := hfSurj.lieAlgebra_isSolvable
  have hJrad : J ≤ radical ℂ L' := le_sSup (show IsSolvable J from inferInstance)
  letI : HasCentralRadical ℂ L' := h
  apply hasCentralRadical_of_radical_le
  intro x hx
  have hxJ : e x ∈ J := LieIdeal.mem_map hx
  have hxCenter : e x ∈ center ℂ L' := by
    rw [← HasCentralRadical.radical_eq_center]
    exact hJrad hxJ
  change ∀ y : L, ⁅y,x⁆ = 0
  intro y
  apply e.injective
  change e ⁅y,x⁆ = e 0
  rw [e.map_lie, map_zero]
  exact hxCenter (e y)

end
end QuaternionicSymmetry.LieCentralRadicalEquiv
