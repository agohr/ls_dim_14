import Mathlib.LinearAlgebra.Quotient.Basic

/-! Source-free quotient transport from equality of membership predicates.
This allows a contact-plane comparison to be passed as a checked pointwise
iff, without exposing a dependent equality of geometric submodule terms. -/

namespace QuaternionicSymmetry.HorizontalQuotientTransport
noncomputable section

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

def equiv (P Q : Submodule R V)
    (h : ∀ v : V, v ∈ P ↔ v ∈ Q) : (V ⧸ P) ≃ₗ[R] V ⧸ Q :=
  Submodule.quotEquivOfEq P Q (Submodule.ext h)

theorem equiv_mk (P Q : Submodule R V)
    (h : ∀ v : V, v ∈ P ↔ v ∈ Q) (v : V) :
    equiv P Q h (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := by
  exact Submodule.quotEquivOfEq_mk P Q (Submodule.ext h) v

end
end QuaternionicSymmetry.HorizontalQuotientTransport
