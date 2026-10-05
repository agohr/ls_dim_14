import QuaternionicSymmetry.ContinuousWedge
import QuaternionicSymmetry.LocalCovariantExterior
import QuaternionicSymmetry.ContinuousWedgeLeibnizLeft
import QuaternionicSymmetry.ContinuousWedgeRightInsertion
import QuaternionicSymmetry.ContinuousWedgeLeibniz

/-!
# Pointwise commutator derivation on normalized continuous wedges

The coefficient commutator with a one-form is an ordinary derivation of
ring multiplication before exterior alternation.  This module proves that
identity for the actual bounded normalized wedge, in every pair of degrees.
The graded shuffle identity for `alternatizeUncurryFin` then turns this
slotwise result into the covariant exterior Leibniz rule.
-/

namespace QuaternionicSymmetry.LocalContinuousWedgeCommutator

open QuaternionicSymmetry.ContinuousWedge
  QuaternionicSymmetry.LocalConnection
  QuaternionicSymmetry.LocalCovariantExterior
  QuaternionicSymmetry.ContinuousWedgeLeibnizLeft
  QuaternionicSymmetry.ContinuousWedgeRightInsertion
  QuaternionicSymmetry.ContinuousWedgeShuffle
  QuaternionicSymmetry.ContinuousWedgeLeibniz

noncomputable section

variable {E R : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [NormedAlgebra ℝ R]
  {p q : ℕ}

local instance : NormedSpace ℝ R := NormedAlgebra.toNormedSpace R

/-- The unalternated coefficient commutator in one directional slot. -/
def commutatorSlot (Γ : Form (E := E) (A := R))
    (ω : E [⋀^Fin p]→L[ℝ] R) (x : E) :
    E →L[ℝ] E [⋀^Fin p]→L[ℝ] R :=
  (((ContinuousLinearMap.compContinuousAlternatingMapCLM ℝ E R R).flip ω).comp
    (((ContinuousLinearMap.mul ℝ R) -
      (ContinuousLinearMap.mul ℝ R).flip).comp (Γ x)))

@[simp] theorem commutatorSlot_apply (Γ : Form (E := E) (A := R))
    (ω : E [⋀^Fin p]→L[ℝ] R) (x u : E) (v : Fin p → E) :
    commutatorSlot Γ ω x u v =
      Γ x u * ω v - ω v * Γ x u := rfl

@[simp] theorem wedge_mul_zero_left
    (β : E [⋀^Fin q]→L[ℝ] R) :
    wedge (ContinuousLinearMap.mul ℝ R)
      (0 : E [⋀^Fin p]→L[ℝ] R) β = 0 := by
  have h := (wedgeCLM (E := E) (p := p) (q := q)
    (ContinuousLinearMap.mul ℝ R)).map_zero
  exact congrArg (fun L : (E [⋀^Fin q]→L[ℝ] R) →L[ℝ]
    (E [⋀^Fin (p + q)]→L[ℝ] R) => L β) h

@[simp] theorem wedge_mul_zero_right
    (α : E [⋀^Fin p]→L[ℝ] R) :
    wedge (ContinuousLinearMap.mul ℝ R) α
      (0 : E [⋀^Fin q]→L[ℝ] R) = 0 := by
  exact (wedgeCLM (E := E) (p := p) (q := q)
    (ContinuousLinearMap.mul ℝ R) α).map_zero

theorem commutator_eq_alternatizeSlot (Γ : Form (E := E) (A := R))
    (ω : E [⋀^Fin p]→L[ℝ] R) (x : E) :
    commutator Γ ω x =
      ContinuousAlternatingMap.alternatizeUncurryFin (commutatorSlot Γ ω x) := rfl

theorem commutatorSlot_wedge_mul (Γ : Form (E := E) (A := R))
    (α : E [⋀^Fin p]→L[ℝ] R) (β : E [⋀^Fin q]→L[ℝ] R)
    (x u : E) :
    commutatorSlot Γ (wedge (ContinuousLinearMap.mul ℝ R) α β) x u =
      wedge (ContinuousLinearMap.mul ℝ R) (commutatorSlot Γ α x u) β +
        wedge (ContinuousLinearMap.mul ℝ R) α (commutatorSlot Γ β x u) := by
  ext v
  simp only [commutatorSlot_apply, ContinuousAlternatingMap.add_apply,
    wedge_apply]
  simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
    ← smul_sub, Finset.mul_sum, Finset.sum_mul,
    ← Finset.sum_sub_distrib]
  rw [← smul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · simp [hs]
    noncomm_ring
  · simp [hs]
    noncomm_ring

/-- The coefficient commutator is a graded derivation of the actual
normalized exterior product.  The left product is transported along the
canonical order-preserving equivalence of `Fin` index types. -/
theorem commutator_wedge_mul_apply (Γ : Form (E := E) (A := R))
    (α : E [⋀^Fin p]→L[ℝ] R) (β : E [⋀^Fin q]→L[ℝ] R)
    (x : E) (v : Fin (p + q + 1) → E) :
    commutator Γ (wedge (ContinuousLinearMap.mul ℝ R) α β) x v =
      wedge (ContinuousLinearMap.mul ℝ R) (commutator Γ α x) β
        (v ∘ wedgeLeftIndex p q) +
        (-1 : ℤ) ^ p •
          wedge (ContinuousLinearMap.mul ℝ R) α (commutator Γ β x) v := by
  rw [commutator_eq_alternatizeSlot,
    ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  have hsplit :
      (∑ i : Fin (p + q + 1), (-1 : ℤ) ^ i.val •
        (commutatorSlot Γ
          (wedge (ContinuousLinearMap.mul ℝ R) α β) x (v i))
          (i.removeNth v)) =
        (∑ i : Fin (p + q + 1), (-1 : ℤ) ^ i.val •
          wedge (ContinuousLinearMap.mul ℝ R)
            (commutatorSlot Γ α x (v i)) β (i.removeNth v)) +
        (∑ i : Fin (p + q + 1), (-1 : ℤ) ^ i.val •
          wedge (ContinuousLinearMap.mul ℝ R) α
            (commutatorSlot Γ β x (v i)) (i.removeNth v)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [commutatorSlot_wedge_mul Γ α β x (v i),
      ContinuousAlternatingMap.add_apply, smul_add]
  rw [hsplit]
  rw [alternatizeUncurryFin_wedge_left
    (ContinuousLinearMap.mul ℝ R) (commutatorSlot Γ α x) β v]
  rw [insertion_wedge_right_eq_signed_wedge_ext
    (ContinuousLinearMap.mul ℝ R) α (commutatorSlot Γ β x) v]
  rw [← commutator_eq_alternatizeSlot Γ α x,
    ← commutator_eq_alternatizeSlot Γ β x]

/-- The actual covariant exterior derivative obeys graded Leibniz for
ring-valued normalized wedges in all degrees. -/
theorem covariantExteriorDerivative_wedge_mul_apply
    (Γ : Form (E := E) (A := R))
    (α : E → E [⋀^Fin p]→L[ℝ] R)
    (β : E → E [⋀^Fin q]→L[ℝ] R) (x : E)
    (hα : DifferentiableAt ℝ α x) (hβ : DifferentiableAt ℝ β x)
    (v : Fin (p + q + 1) → E) :
    covariantExteriorDerivative Γ
      (fun y => wedge (ContinuousLinearMap.mul ℝ R) (α y) (β y)) x v =
      wedge (ContinuousLinearMap.mul ℝ R)
        (covariantExteriorDerivative Γ α x) (β x)
        (v ∘ wedgeLeftIndex p q) +
      (-1 : ℤ) ^ p • wedge (ContinuousLinearMap.mul ℝ R)
        (α x) (covariantExteriorDerivative Γ β x) v := by
  rw [covariantExteriorDerivative, ContinuousAlternatingMap.add_apply]
  rw [ContinuousWedgeLeibniz.extDeriv_wedge_apply (ContinuousLinearMap.mul ℝ R)
    α β x hα hβ v]
  rw [commutator_wedge_mul_apply Γ (α x) (β x) x v]
  simp only [covariantExteriorDerivative, wedge_add_left, wedge_add_right,
    ContinuousAlternatingMap.add_apply, smul_add]
  abel

end
end QuaternionicSymmetry.LocalContinuousWedgeCommutator
