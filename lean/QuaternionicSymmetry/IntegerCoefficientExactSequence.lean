import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Data.ZMod.Basic

/-! The actual integral multiplication/reduction short exact sequence,
with the lifted integral coefficient object used by sheaf cohomology. -/

namespace QuaternionicSymmetry.IntegerCoefficientExactSequence

open CategoryTheory
noncomputable section

abbrev integralCoefficient : AddCommGrpCat := AddCommGrpCat.of (ULift.{0} ℤ)

def reduction (k : ℕ) : integralCoefficient ⟶ AddCommGrpCat.of (ZMod k) :=
  AddCommGrpCat.ofHom {
    toFun := fun z => (z.down : ZMod k)
    map_zero' := by simp
    map_add' := by intros; simp }

def coefficientComplex (k : ℕ) : ShortComplex AddCommGrpCat :=
  ShortComplex.mk (k • 𝟙 integralCoefficient) (reduction k) (by
    ext z
    change (((k • z).down : ℤ) : ZMod k) = 0
    simp [nsmul_eq_mul])

theorem coefficientComplex_shortExact (k : ℕ) (hk : k ≠ 0) :
    (coefficientComplex k).ShortExact where
  exact := by
    apply (ShortComplex.ab_exact_iff _).mpr
    intro z hz
    change (z.down : ZMod k) = 0 at hz
    obtain ⟨a, ha⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd z.down k).mp hz
    refine ⟨ULift.up a, ?_⟩
    apply ULift.ext
    change (k : ℤ) * a = z.down
    exact ha.symm
  mono_f := by
    apply (AddCommGrpCat.mono_iff_injective _).mpr
    intro z w h
    apply ULift.ext
    have h' := congrArg ULift.down h
    change (k : ℤ) * z.down = (k : ℤ) * w.down at h'
    exact mul_left_cancel₀ (Int.natCast_ne_zero.mpr hk) h'
  epi_g := by
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    intro z
    obtain ⟨a, ha⟩ := ZMod.intCast_surjective z
    exact ⟨ULift.up a, ha⟩

end
end QuaternionicSymmetry.IntegerCoefficientExactSequence
