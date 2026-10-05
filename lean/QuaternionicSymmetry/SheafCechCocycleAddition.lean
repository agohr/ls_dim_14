import QuaternionicSymmetry.SheafCechCoefficientMap

/-! Addition and pairing of genuine cocycles, using the actual categorical
binary biproduct of their coefficient sheaves. -/

namespace QuaternionicSymmetry.SheafCechCocycleAddition

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AbelianSheafCohomology SheafCechOneCocycle SheafCechCoefficientMap
noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type}
  {A D : AbelianSheaves B} {U : ι → Opens B}

theorem cocycle_ext (c d : OneCocycle A U)
    (h : ∀ i j V hi hj, c.value i j V hi hj = d.value i j V hi hj) : c = d := by
  cases c
  cases d
  congr 1
  funext i j V hi hj
  exact h i j V hi hj

def sumCocycle (c d : OneCocycle A U) : OneCocycle A U where
  value i j V hi hj := c.value i j V hi hj + d.value i j V hi hj
  naturality i j V W hWV hi hj := by
    change (restrict A hWV).hom (_ + _) = _
    rw [map_add, c.naturality, d.naturality]
  cocycle i j k V hi hj hk := by
    calc
      _ = (c.value i j V hi hj + c.value j k V hj hk) +
          (d.value i j V hi hj + d.value j k V hj hk) := by abel
      _ = _ := by rw [c.cocycle, d.cocycle]

def pairedCocycle (c : OneCocycle A U) (d : OneCocycle D U) : OneCocycle (A ⊞ D) U :=
  sumCocycle (mappedCocycle biprod.inl c) (mappedCocycle biprod.inr d)

theorem mapped_pair_fst (c : OneCocycle A U) (d : OneCocycle D U) :
    mappedCocycle biprod.fst (pairedCocycle c d) = c := by
  apply cocycle_ext
  intro i j V hi hj
  change ((biprod.fst : A ⊞ D ⟶ A).val.app (op V)).hom (_ + _) = _
  rw [map_add]
  dsimp only [mappedCocycle]
  have h₁ := congrArg (fun f : A ⟶ A => f.val.app (op V) (c.value i j V hi hj))
    (biprod.inl_fst (X := A) (Y := D))
  have h₂ := congrArg (fun f : D ⟶ A => f.val.app (op V) (d.value i j V hi hj))
    (biprod.inr_fst (X := A) (Y := D))
  change (biprod.fst : A ⊞ D ⟶ A).val.app (op V)
    ((biprod.inl : A ⟶ A ⊞ D).val.app (op V) (c.value i j V hi hj)) = _ at h₁
  change (biprod.fst : A ⊞ D ⟶ A).val.app (op V)
    ((biprod.inr : D ⟶ A ⊞ D).val.app (op V) (d.value i j V hi hj)) = 0 at h₂
  rw [h₁, h₂, add_zero]
  rfl

theorem mapped_pair_snd (c : OneCocycle A U) (d : OneCocycle D U) :
    mappedCocycle biprod.snd (pairedCocycle c d) = d := by
  apply cocycle_ext
  intro i j V hi hj
  change ((biprod.snd : A ⊞ D ⟶ D).val.app (op V)).hom (_ + _) = _
  rw [map_add]
  dsimp only [mappedCocycle]
  have h₁ := congrArg (fun f : A ⟶ D => f.val.app (op V) (c.value i j V hi hj))
    (biprod.inl_snd (X := A) (Y := D))
  have h₂ := congrArg (fun f : D ⟶ D => f.val.app (op V) (d.value i j V hi hj))
    (biprod.inr_snd (X := A) (Y := D))
  change (biprod.snd : A ⊞ D ⟶ D).val.app (op V)
    ((biprod.inl : A ⟶ A ⊞ D).val.app (op V) (c.value i j V hi hj)) = 0 at h₁
  change (biprod.snd : A ⊞ D ⟶ D).val.app (op V)
    ((biprod.inr : D ⟶ A ⊞ D).val.app (op V) (d.value i j V hi hj)) = _ at h₂
  rw [h₁, h₂, zero_add]
  rfl

theorem mapped_add (f g : A ⟶ D) (c : OneCocycle A U) :
    mappedCocycle (f + g) c = sumCocycle (mappedCocycle f c) (mappedCocycle g c) := by
  apply cocycle_ext
  intro i j V hi hj
  rfl

theorem mapped_pair_add (c d : OneCocycle A U) :
    mappedCocycle (biprod.fst + biprod.snd) (pairedCocycle c d) = sumCocycle c d := by
  rw [mapped_add, mapped_pair_fst, mapped_pair_snd]

end
end QuaternionicSymmetry.SheafCechCocycleAddition
