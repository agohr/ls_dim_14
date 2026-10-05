import QuaternionicSymmetry.HolomorphicLineSheafClassGroup

/-!
# Generator comparison with the full analytic line-sheaf Picard group

The existing reconstructed `classMulEquiv` identifies represented line cores
with *all* locally free rank-one analytic module sheaves at universe zero.
This leaf transfers the precise integral-power generator predicate through
that multiplicative equivalence. No algebraic Picard or GAGA assertion occurs
here; those remain separate published-background application obligations.
-/

namespace QuaternionicSymmetry.HolomorphicLineCoreSheafPicardGenerator

open HolomorphicLineCoreClasses HolomorphicLineSheafClasses
open HolomorphicLineSheafClassGroup
open scoped Manifold ContDiff

noncomputable section

variable {B H F : Type} [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)

private theorem bijective_comp_equiv {X A C : Type*}
    (e : A ≃ C) (f : X → A) :
    Function.Bijective (e ∘ f) ↔ Function.Bijective f := by
  constructor
  · rintro ⟨hi, hs⟩
    constructor
    · intro x y hxy
      exact hi (congrArg e hxy)
    · intro a
      obtain ⟨x, hx⟩ := hs (e a)
      exact ⟨x, e.injective hx⟩
  · rintro ⟨hi, hs⟩
    constructor
    · intro x y hxy
      exact hi (e.injective hxy)
    · intro c
      obtain ⟨x, hx⟩ := hs (e.symm c)
      exact ⟨x, by simp [hx]⟩

/-- The contact-line generator condition on the represented core group is
exactly generation of the full analytic Picard group of locally free
rank-one holomorphic module sheaves, not just of a chosen bundle subclass. -/
theorem core_zpow_bijective_iff_analyticPicard
    (L : LineCore.{0} (B := B) IB) :
    Function.Bijective (fun r : ℤ =>
      (Quotient.mk _ L : CoreClass.{0} (B := B) IB) ^ r) ↔
    Function.Bijective (fun r : ℤ =>
      (classMulEquiv IB (Quotient.mk _ L) : SheafClass (B := B) IB) ^ r) := by
  let e : CoreClass.{0} (B := B) IB ≃* SheafClass (B := B) IB :=
    classMulEquiv (B := B) IB
  let f : ℤ → CoreClass.{0} (B := B) IB :=
    fun r => (Quotient.mk _ L : CoreClass.{0} (B := B) IB) ^ r
  have hmap : (fun r : ℤ =>
      (classMulEquiv IB (Quotient.mk _ L) : SheafClass (B := B) IB) ^ r) =
      e ∘ f := by
    funext r
    exact (map_zpow e (Quotient.mk _ L) r).symm
  rw [hmap]
  exact (bijective_comp_equiv e.toEquiv f).symm

end
end QuaternionicSymmetry.HolomorphicLineCoreSheafPicardGenerator
