import QuaternionicSymmetry.HolomorphicIntegerSheafInclusion
import QuaternionicSymmetry.HolomorphicExponentialLocallySurjective
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Sites.LeftExact

/-! The genuine holomorphic exponential sequence is short exact in
Mathlib's abelian category of sheaves. Its left term is the actual sheaf
of locally constant integer functions, with inclusion `k ↦ 2πi k`.
Comparison of that term with the categorical constant sheaf, and the
Picard/cohomology identification, are separate obligations. -/

namespace QuaternionicSymmetry.HolomorphicExponentialSequence

open CategoryTheory CategoryTheory.Limits TopologicalSpace Manifold Opposite
open HolomorphicLineModuleSheaf HolomorphicUnitSheaf
open HolomorphicExponentialSheaf HolomorphicIntegerSheafInclusion
open HolomorphicExponentialLocallySurjective LocallyConstantIntegerSheaf
open scoped Manifold ContDiff
noncomputable section

private theorem presheaf_exact_of_sectionwise
    {C : Type*} [Category C] (S : ShortComplex (C ⥤ AddCommGrpCat))
    (hS : ∀ U, (S.map ((evaluation C AddCommGrpCat).obj U)).Exact) :
    S.Exact := by
  rw [ShortComplex.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
  apply NatTrans.ext
  funext U
  exact (IsZero.of_iso
    ((ShortComplex.exact_iff_isZero_homology _).mp (hS U))
    (S.mapHomologyIso ((evaluation C AddCommGrpCat).obj U)).symm).eq_of_src _ _

variable {B : Type} {H F : Type*}
  [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)

def exponentialComplex :
    ShortComplex (Sheaf (Opens.grothendieckTopology (TopCat.of B)) AddCommGrpCat) :=
  ShortComplex.mk (integerInclusion (B := B) IB) (exponential IB)
    (integerInclusion_exponential IB)

theorem exponentialComplex_exact : (exponentialComplex (B := B) IB).Exact := by
  let V := sheafToPresheaf (Opens.grothendieckTopology (TopCat.of B)) AddCommGrpCat
  apply V.reflects_exact_of_faithful
  apply presheaf_exact_of_sectionwise
  intro U
  rw [ShortComplex.ab_exact_iff]
  intro f hf
  exact (exponential_section_kernel IB U.unop f).mp hf

instance exponentialComplex_mono : Mono (exponentialComplex (B := B) IB).f where
  right_cancellation {Z} f g h := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.ext
    intro s
    apply integerInclusion_app_injective IB U.unop
    exact congrArg (fun φ => φ.val.app U s) h

instance exponentialComplex_epi : Epi (exponentialComplex (B := B) IB).g := by
  change Epi (exponential (B := B) IB)
  exact Sheaf.epi_of_isLocallySurjective (exponential (B := B) IB)

/-- The analytic exponential sequence is genuinely short exact, including
local logarithms, the global sectionwise integer kernel, and injectivity. -/
theorem exponentialComplex_shortExact :
    (exponentialComplex (B := B) IB).ShortExact where
  exact := exponentialComplex_exact IB

end
end QuaternionicSymmetry.HolomorphicExponentialSequence
