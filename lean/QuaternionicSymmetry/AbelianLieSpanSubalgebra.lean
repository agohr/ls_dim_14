import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Analysis.Complex.Circle

/-! A commuting family generates an actual abelian Lie subalgebra. This
packages bracket closure without Cartan or maximality assumptions. -/

namespace QuaternionicSymmetry.AbelianLieSpanSubalgebra

noncomputable section

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]

theorem span_bracket_eq_zero (S : Set L)
    (hComm : ∀ x ∈ S, ∀ y ∈ S, ⁅x,y⁆ = 0)
    {x y : L} (hx : x ∈ Submodule.span ℂ S)
    (hy : y ∈ Submodule.span ℂ S) : ⁅x,y⁆ = 0 := by
  have hleft (a : L) (ha : a ∈ Submodule.span ℂ S)
      (b : L) (hb : b ∈ S) : ⁅a,b⁆ = 0 := by
    induction ha using Submodule.span_induction with
    | mem a ha => exact hComm a ha b hb
    | zero => simp
    | add a c ha hc iha ihc => simpa only [add_lie, iha, ihc, zero_add]
    | smul c a ha iha => simpa only [smul_lie, iha, smul_zero]
  induction hy using Submodule.span_induction with
  | mem y hy => exact hleft x hx y hy
  | zero => simp
  | add y z hy hz ihy ihz => simpa only [lie_add, ihy, ihz, zero_add]
  | smul c y hy ihy => simpa only [lie_smul, ihy, smul_zero]

def lieSubalgebra (S : Set L)
    (hComm : ∀ x ∈ S, ∀ y ∈ S, ⁅x,y⁆ = 0) : LieSubalgebra ℂ L where
  toSubmodule := Submodule.span ℂ S
  lie_mem' := by
    intro x y hx hy
    rw [span_bracket_eq_zero S hComm hx hy]
    exact (Submodule.span ℂ S).zero_mem

theorem lieSubalgebra_abelian (S : Set L)
    (hComm : ∀ x ∈ S, ∀ y ∈ S, ⁅x,y⁆ = 0)
    (x y : lieSubalgebra S hComm) : ⁅(x : L),(y : L)⁆ = 0 :=
  span_bracket_eq_zero S hComm x.2 y.2

end
end QuaternionicSymmetry.AbelianLieSpanSubalgebra
