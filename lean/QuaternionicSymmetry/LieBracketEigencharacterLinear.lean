import QuaternionicSymmetry.ToralBracketEigenbasis

/-! A nonzero genuine bracket eigenvector forces its scalar character to
be complex-linear on the acting Lie subalgebra. -/

namespace QuaternionicSymmetry.LieBracketEigencharacterLinear

noncomputable section

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]

def eigencharacterLinear (H : LieSubalgebra ℂ L)
    (v : L) (hv : v ≠ 0) (χ : H → ℂ)
    (hEig : ∀ h : H, ⁅(h : L),v⁆ = χ h • v) : H →ₗ[ℂ] ℂ where
  toFun := χ
  map_add' := by
    intro x y
    apply smul_left_injective ℂ hv
    calc
      χ (x+y) • v = ⁅((x+y : H) : L),v⁆ := (hEig (x+y)).symm
      _ = ⁅(x : L),v⁆ + ⁅(y : L),v⁆ := by change ⁅(x : L)+(y : L),v⁆ = _; simp
      _ = (χ x + χ y) • v := by rw [hEig x, hEig y, add_smul]
  map_smul' := by
    intro a x
    apply smul_left_injective ℂ hv
    calc
      χ (a • x) • v = ⁅((a • x : H) : L),v⁆ := (hEig (a • x)).symm
      _ = a • ⁅(x : L),v⁆ := by simp only [SetLike.val_smul, smul_lie]
      _ = (a • χ x) • v := by rw [hEig x, smul_smul, smul_eq_mul]

@[simp] theorem eigencharacterLinear_apply (H : LieSubalgebra ℂ L)
    (v : L) (hv : v ≠ 0) (χ : H → ℂ)
    (hEig : ∀ h : H, ⁅(h : L),v⁆ = χ h • v) (h : H) :
    eigencharacterLinear H v hv χ hEig h = χ h := rfl

/-- Every column of a genuine bracket eigenbasis is a complex-linear
character of the same acting Lie subalgebra. -/
def basisEigencharactersLinear {ι : Type*} (H : LieSubalgebra ℂ L)
    (b : Module.Basis ι ℂ L) (χ : H → ι → ℂ)
    (hEig : ∀ (h : H) i, ⁅(h : L),b i⁆ = χ h i • b i) :
    ι → (H →ₗ[ℂ] ℂ) :=
  fun i => eigencharacterLinear H (b i) (b.ne_zero i)
    (fun h => χ h i) (fun h => hEig h i)

@[simp] theorem basisEigencharactersLinear_apply {ι : Type*}
    (H : LieSubalgebra ℂ L) (b : Module.Basis ι ℂ L)
    (χ : H → ι → ℂ)
    (hEig : ∀ (h : H) i, ⁅(h : L),b i⁆ = χ h i • b i)
    (i : ι) (h : H) :
    basisEigencharactersLinear H b χ hEig i h = χ h i := rfl

end
end QuaternionicSymmetry.LieBracketEigencharacterLinear
