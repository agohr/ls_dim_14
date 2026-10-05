import QuaternionicSymmetry.AbelianSelfCentralizingCartan
import Mathlib.LinearAlgebra.Basis.Defs

/-! An actual common eigenbasis supplies the square-kernel condition in the
checked Cartan criterion. No diagonalizability or Cartan literature input is
introduced. Geometric applications must supply the same actual basis and
bracket eigenrelations, as well as self-centralization. -/

namespace QuaternionicSymmetry.AbelianSelfCentralizingEigenbasisCartan

open AbelianSelfCentralizingCartan

variable {ι L : Type*}

theorem map_eq_zero_of_map_map_eq_zero_of_eigenbasis
    [AddCommGroup L] [Module ℂ L]
    (b : Module.Basis ι ℂ L) (f : L →ₗ[ℂ] L) (c : ι → ℂ)
    (hEig : ∀ i, f (b i) = c i • b i)
    (x : L) (hx : f (f x) = 0) : f x = 0 := by
  classical
  have hCoord (i : ι) (y : L) :
      b.repr (f y) i = c i * b.repr y i := by
    have hMap : (b.coord i).comp f = c i • b.coord i := by
      apply b.ext
      intro j
      simp only [LinearMap.comp_apply, hEig, map_smul,
        LinearMap.smul_apply, smul_eq_mul, Module.Basis.coord_apply,
        Module.Basis.repr_self_apply]
      by_cases h : j = i <;> simp [h]
    exact DFunLike.congr_fun hMap y
  apply b.ext_elem
  intro i
  have hSq : c i * (c i * b.repr x i) = 0 := by
    rw [← hCoord i x, ← hCoord i (f x), hx]
    simp
  have hSingle : c i * b.repr x i = 0 := by
    rcases mul_eq_zero.mp hSq with hZero | hZero
    · simp [hZero]
    · exact hZero
  simpa only [hCoord, map_zero, Finsupp.zero_apply] using hSingle

/-- A common bracket eigenbasis and the actual self-centralizer property
give Mathlib's genuine Cartan-subalgebra predicate. -/
theorem isCartan_of_abelian_selfCentralizing_eigenbasis
    [LieRing L] [LieAlgebra ℂ L]
    (H : LieSubalgebra ℂ L)
    (hAb : ∀ x ∈ H, ∀ y ∈ H, ⁅x,y⁆ = 0)
    (hSelf : ∀ x : L, (∀ y ∈ H, ⁅x,y⁆ = 0) → x ∈ H)
    (b : Module.Basis ι ℂ L)
    (χ : H → ι → ℂ)
    (hEig : ∀ (h : H) i, ⁅(h : L), b i⁆ = χ h i • b i) :
    H.IsCartanSubalgebra := by
  apply isCartan_of_abelian_selfCentralizing_squareKernel H hAb hSelf
  intro h hh x hx
  exact map_eq_zero_of_map_map_eq_zero_of_eigenbasis b
    (LieAlgebra.ad ℂ L h) (χ ⟨h,hh⟩) (hEig ⟨h,hh⟩) x hx

end QuaternionicSymmetry.AbelianSelfCentralizingEigenbasisCartan
