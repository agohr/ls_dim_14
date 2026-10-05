import QuaternionicSymmetry.ConstantIntegralCoefficientSequence
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-! Torsion in actual integral sheaf cohomology is detected by the
preceding finite-coefficient group via the genuine coefficient sequence.
Vanishing of those groups is an explicit hypothesis, not yet a claimed
consequence of simple connectedness of a twistor. -/

namespace QuaternionicSymmetry.IntegralCohomologyTorsion

open CategoryTheory CategoryTheory.Abelian
open AbelianSheafCohomology ConstantIntegralCoefficientSequence
noncomputable section

variable {C : Type*} [Category C] [Abelian C] [HasExt.{1} C]

theorem comp_mk₀_nsmul_id {X Y : C} {s : ℕ}
    (x : Ext X Y s) (k : ℕ) :
    x.comp (Ext.mk₀ (k • 𝟙 Y)) (add_zero s) = k • x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [succ_nsmul, Ext.mk₀_add, Ext.comp_add, ih, Ext.comp_mk₀_id,
      succ_nsmul]

variable (B : Type) [TopologicalSpace B]

theorem nsmul_eq_zero_imp_eq_zero (s k : ℕ) (hk : k ≠ 0)
    (hvan : Subsingleton (cohomology B (finiteCoefficientSheaf B k) s))
    (x : cohomology B (integralSheaf B) (s + 1))
    (hx : k • x = 0) : x = 0 := by
  have he := integralCoefficientComplex_shortExact B k hk
  have hx' : x.comp (Ext.mk₀ (integralCoefficientComplex B k).f)
      (add_zero (s + 1)) = 0 := by
    rw [integralCoefficientComplex_f, comp_mk₀_nsmul_id]
    exact hx
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ (integralSheaf B) he x hx' rfl
  have hy0 : y = 0 := hvan.elim y 0
  rw [hy0, Ext.zero_comp] at hy
  exact hy.symm

theorem isAddTorsionFree_of_finiteCoefficient_vanishing (s : ℕ)
    (hvan : ∀ k : ℕ, k ≠ 0 →
      Subsingleton (cohomology B (finiteCoefficientSheaf B k) s)) :
    IsAddTorsionFree (cohomology B (integralSheaf B) (s + 1)) where
  nsmul_right_injective := by
    intro k hk x y hxy
    change k • x = k • y at hxy
    apply sub_eq_zero.mp
    apply nsmul_eq_zero_imp_eq_zero B s k hk (hvan k hk)
    rw [nsmul_sub, hxy, sub_self]

end
end QuaternionicSymmetry.IntegralCohomologyTorsion
