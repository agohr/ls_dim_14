import Mathlib.Algebra.Lie.CartanSubalgebra
import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.Analysis.Complex.Basic

/-! An elementary Cartan criterion. A commuting subalgebra whose centralizer
is itself is self-normalizing when every adjoint operator has no nonzero
length-two Jordan chain at eigenvalue zero. The final kernel condition is
the precise algebraic consequence to be derived from the selected weight
eigenbasis; this file does not assert it for the geometric model. -/

namespace QuaternionicSymmetry.AbelianSelfCentralizingCartan

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]

/-- Self-normalization from the zero-eigenvalue semisimplicity condition.
The hypotheses are explicit algebraic facts, not external sources. -/
theorem normalizer_eq_self_of_squareKernel
    (H : LieSubalgebra ℂ L)
    (hAb : ∀ x ∈ H, ∀ y ∈ H, ⁅x,y⁆ = 0)
    (hSelf : ∀ x : L, (∀ y ∈ H, ⁅x,y⁆ = 0) → x ∈ H)
    (hSquare : ∀ h ∈ H, ∀ x : L,
      ⁅h,⁅h,x⁆⁆ = 0 → ⁅h,x⁆ = 0) :
    H.normalizer = H := by
  apply le_antisymm _ H.le_normalizer
  intro x hx
  apply hSelf x
  intro h hh
  have hXh : ⁅x,h⁆ ∈ H := (H.mem_normalizer_iff x).mp hx h hh
  have hHx : ⁅h,x⁆ ∈ H := by
    rw [← lie_skew h x]
    exact H.neg_mem hXh
  have hSq : ⁅h,⁅h,x⁆⁆ = 0 := hAb h hh _ hHx
  have hZero := hSquare h hh x hSq
  have hNegZero : -⁅h,x⁆ = 0 := by simpa only [hZero, neg_zero]
  simpa only [lie_skew x h] using hNegZero

/-- The same criterion gives Mathlib's genuine nilpotent,
self-normalizing `IsCartanSubalgebra`, not merely a maximal-abelian label. -/
theorem isCartan_of_abelian_selfCentralizing_squareKernel
    (H : LieSubalgebra ℂ L)
    (hAb : ∀ x ∈ H, ∀ y ∈ H, ⁅x,y⁆ = 0)
    (hSelf : ∀ x : L, (∀ y ∈ H, ⁅x,y⁆ = 0) → x ∈ H)
    (hSquare : ∀ h ∈ H, ∀ x : L,
      ⁅h,⁅h,x⁆⁆ = 0 → ⁅h,x⁆ = 0) :
    H.IsCartanSubalgebra := by
  letI : IsLieAbelian H := ⟨fun x y => by
    apply Subtype.ext
    exact hAb x x.property y y.property⟩
  exact ⟨inferInstance,
    normalizer_eq_self_of_squareKernel H hAb hSelf hSquare⟩

end QuaternionicSymmetry.AbelianSelfCentralizingCartan
