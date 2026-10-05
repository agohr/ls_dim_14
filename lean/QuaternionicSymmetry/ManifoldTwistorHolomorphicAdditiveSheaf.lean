import QuaternionicSymmetry.ManifoldTwistorHolomorphicSectionSheaf
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! The additive sheaf of locally holomorphic sections of the genuine
integer contact-line twists. Local holomorphicity is tested in each actual
line-bundle trivialization, so addition is pointwise in complex coordinates. -/

namespace QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas

universe u v

open QuaternionicSymmetry.ManifoldTwistorSphereCore
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open QuaternionicSymmetry.ManifoldQuaternionicConnection
open CategoryTheory TopologicalSpace
open scoped Manifold ContDiff
noncomputable section

variable {E : Type u} {M : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : CompatibleTangentConnection Q)

private abbrev IX (n : ℕ) := 𝓘(ℂ, ComplexTwistorModel n)

/-- The coefficient of a section in the actual `i`-th bundle chart. -/
def twistCoefficient {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (r : ℤ) (i : L.Index) {U : Opens (SphereBundleTotal Q)}
    (f : ∀ x : U, (L.integerTwistCore Q D r).Fiber x) (x : U) : ℂ :=
  (L.integerTwistCore Q D r).coordChange
    ((L.integerTwistCore Q D r).indexAt x.1) i x.1 (f x)

theorem twistCoefficient_zero {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (r : ℤ) (i : L.Index) (U : Opens (SphereBundleTotal Q)) (x : U) :
    twistCoefficient Q D L r i (0 : ∀ x : U, (L.integerTwistCore Q D r).Fiber x) x = 0 := by
  exact map_zero _

theorem twistCoefficient_add {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (r : ℤ) (i : L.Index) {U : Opens (SphereBundleTotal Q)}
    (f g : ∀ x : U, (L.integerTwistCore Q D r).Fiber x) (x : U) :
    twistCoefficient Q D L r i (f + g) x =
      twistCoefficient Q D L r i f x + twistCoefficient Q D L r i g x := by
  exact map_add _ _ _

theorem twistCoefficient_neg {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (r : ℤ) (i : L.Index) {U : Opens (SphereBundleTotal Q)}
    (f : ∀ x : U, (L.integerTwistCore Q D r).Fiber x) (x : U) :
    twistCoefficient Q D L r i (-f) x = -twistCoefficient Q D L r i f x := by
  exact map_neg _ _

theorem twistCoefficient_smul {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (r : ℤ) (i : L.Index) {U : Opens (SphereBundleTotal Q)}
    (c : ℂ) (f : ∀ x : U, (L.integerTwistCore Q D r).Fiber x) (x : U) :
    twistCoefficient Q D L r i (c • f) x =
      c • twistCoefficient Q D L r i f x := by
  exact map_smul
    ((L.integerTwistCore Q D r).coordChange
      ((L.integerTwistCore Q D r).indexAt x.1) i x.1) c (f x)

/-- Holomorphicity of all actual bundle-chart coefficient functions. -/
def coefficientPrelocal {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (r : ℤ) :
    letI := A.charts
    TopCat.PrelocalPredicate
      (fun z : TopCat.of (SphereBundleTotal Q) => (L.integerTwistCore Q D r).Fiber z) := by
  letI := A.charts
  let P : ∀ {U : Opens (TopCat.of (SphereBundleTotal Q))},
      (∀ x : U, (L.integerTwistCore Q D r).Fiber x) → Prop :=
    fun {U} f => ∀ i : L.Index,
      ContMDiffOn (IX n) 𝓘(ℂ,ℂ) ∞ (twistCoefficient Q D L r i f)
        {x : U | x.1 ∈ (L.integerTwistCore Q D r).baseSet i}
  refine { pred := P, res := ?_ }
  intro U V h f hf i
  have hcomp := (hf i).comp (contMDiff_inclusion h.le).contMDiffOn
    (show Set.MapsTo (fun x : U => (⟨x.1, h.le x.2⟩ : V))
      {x : U | x.1 ∈ (L.integerTwistCore Q D r).baseSet i}
      {x : V | x.1 ∈ (L.integerTwistCore Q D r).baseSet i} by
      intro x hx; exact hx)
  convert hcomp using 1

/-- Locally holomorphic coefficient sections form an additive subgroup on
every open set. This is the algebraic input for the additive sheaf. -/
def coefficientSectionSubgroup {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (r : ℤ) (U : Opens (SphereBundleTotal Q)) :
    AddSubgroup (∀ x : U, (L.integerTwistCore Q D r).Fiber x) := by
  letI := A.charts
  let P := coefficientPrelocal Q D L r
  have hz : P.sheafify.pred
      (0 : ∀ x : U, (L.integerTwistCore Q D r).Fiber x) := by
    apply P.sheafifyOf
    change ∀ i : L.Index, ContMDiffOn (IX n) 𝓘(ℂ,ℂ) ∞ _ _
    intro i
    convert contMDiffOn_const using 1
    funext x
    exact twistCoefficient_zero Q D L r i U x
  have ha : ∀ a b : ∀ x : U, (L.integerTwistCore Q D r).Fiber x,
      P.sheafify.pred a → P.sheafify.pred b → P.sheafify.pred (a + b) := by
    intro a b ha hb
    apply P.sheafify_inductionOn₂' P P (fun x y => x + y) ?_ ha hb
    intro V W f g hf hg
    change ∀ i : L.Index, ContMDiffOn (IX n) 𝓘(ℂ,ℂ) ∞ _ _
    intro i
    have hf' := P.res (Opens.infLELeft V W) f hf i
    have hg' := P.res (Opens.infLERight V W) g hg i
    convert hf'.add hg' using 1
    funext x
    exact twistCoefficient_add Q D L r i _ _ x
  have hn : ∀ a : ∀ x : U, (L.integerTwistCore Q D r).Fiber x,
      P.sheafify.pred a → P.sheafify.pred (-a) := by
    intro a ha
    apply P.sheafify_inductionOn' (fun x => -x) ?_ ha
    intro V f hf
    change ∀ i : L.Index, ContMDiffOn (IX n) 𝓘(ℂ,ℂ) ∞ _ _
    intro i
    convert (hf i).neg using 1
    funext x
    exact twistCoefficient_neg Q D L r i f x
  let S0 : AddSubsemigroup (∀ x : U, (L.integerTwistCore Q D r).Fiber x) :=
    ⟨{f | P.sheafify.pred f}, fun {a b} ha' hb' => ha a b ha' hb'⟩
  let S1 : AddSubmonoid (∀ x : U, (L.integerTwistCore Q D r).Fiber x) :=
    ⟨S0, hz⟩
  exact ⟨S1, fun {x} hx => hn x hx⟩

/-- The same local holomorphic sections are closed under constant complex
scalars. This records their natural vector-space structure independently of
the additive category used to define derived sheaf cohomology. -/
def coefficientSectionSubmodule {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (r : ℤ) (U : Opens (SphereBundleTotal Q)) :
    Submodule ℂ (∀ x : U, (L.integerTwistCore Q D r).Fiber x) := by
  letI := A.charts
  let P := coefficientPrelocal Q D L r
  let S := coefficientSectionSubgroup Q D L r U
  refine { toAddSubmonoid := S.toAddSubmonoid, smul_mem' := ?_ }
  intro c f hf
  change P.sheafify.pred (c • f)
  apply P.sheafify_inductionOn' (fun x => c • x) ?_ hf
  intro V g hg
  change ∀ i : L.Index, ContMDiffOn (IX n) 𝓘(ℂ,ℂ) ∞ _ _
  intro i
  convert contMDiffOn_const.smul (hg i) using 1
  funext x
  exact twistCoefficient_smul Q D L r i c g x

/-- The sheaf of actual contact-line sections described in line charts. -/
def coefficientSectionSheaf {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (r : ℤ) :
    letI := A.charts
    TopCat.Sheaf (Type _) (TopCat.of (SphereBundleTotal Q)) := by
  letI := A.charts
  exact TopCat.subsheafToTypes (coefficientPrelocal Q D L r).sheafify

noncomputable instance coefficientSectionSheaf_addCommGroup {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (r : ℤ) (U : (Opens (TopCat.of (SphereBundleTotal Q)))ᵒᵖ) :
    letI := A.charts
    AddCommGroup ((coefficientSectionSheaf Q D L r).presheaf.obj U) := by
  letI := A.charts
  change AddCommGroup (coefficientSectionSubgroup Q D L r U.unop)
  infer_instance

/-- The values of the additive holomorphic sheaf carry their genuine
pointwise complex vector-space structure. -/
noncomputable instance coefficientSectionSheaf_module {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (r : ℤ) (U : (Opens (TopCat.of (SphereBundleTotal Q)))ᵒᵖ) :
    letI := A.charts
    Module ℂ ((coefficientSectionSheaf Q D L r).presheaf.obj U) := by
  letI := A.charts
  change Module ℂ (coefficientSectionSubmodule Q D L r U.unop)
  infer_instance

def coefficientRestrictionAddHom {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (r : ℤ) {U V : (Opens (TopCat.of (SphereBundleTotal Q)))ᵒᵖ}
    (h : U ⟶ V) :
    letI := A.charts
    (coefficientSectionSheaf Q D L r).presheaf.obj U →+
      (coefficientSectionSheaf Q D L r).presheaf.obj V := by
  letI := A.charts
  letI := coefficientSectionSheaf_addCommGroup Q D L r U
  letI := coefficientSectionSheaf_addCommGroup Q D L r V
  let T := coefficientSectionSheaf Q D L r
  exact {
    toFun := T.presheaf.map h
    map_zero' := rfl
    map_add' := by intro a b; rfl }

/-- Restriction of genuine holomorphic sections is complex linear. -/
def coefficientRestrictionLinearMap {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (r : ℤ) {U V : (Opens (TopCat.of (SphereBundleTotal Q)))ᵒᵖ}
    (h : U ⟶ V) :
    letI := A.charts
    (coefficientSectionSheaf Q D L r).presheaf.obj U →ₗ[ℂ]
      (coefficientSectionSheaf Q D L r).presheaf.obj V := by
  letI := A.charts
  letI := coefficientSectionSheaf_addCommGroup Q D L r U
  letI := coefficientSectionSheaf_addCommGroup Q D L r V
  letI := coefficientSectionSheaf_module Q D L r U
  letI := coefficientSectionSheaf_module Q D L r V
  exact {
    coefficientRestrictionAddHom Q D L r h with
    map_smul' := by intro c f; rfl }

/-- The actual contact twist as a presheaf of complex vector spaces. -/
def coefficientSectionPresheafComplex {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (r : ℤ) :
    letI := A.charts
    TopCat.Presheaf (ModuleCat.{v} ℂ) (TopCat.of (SphereBundleTotal Q)) := by
  letI := A.charts
  letI (U : (Opens (TopCat.of (SphereBundleTotal Q)))ᵒᵖ) :=
    coefficientSectionSheaf_addCommGroup Q D L r U
  letI (U : (Opens (TopCat.of (SphereBundleTotal Q)))ᵒᵖ) :=
    coefficientSectionSheaf_module Q D L r U
  let T := coefficientSectionSheaf Q D L r
  exact {
    obj := fun U => ModuleCat.of ℂ (T.presheaf.obj U)
    map := fun h => ModuleCat.ofHom (coefficientRestrictionLinearMap Q D L r h)
    map_id := by intro U; rfl
    map_comp := by intro U V W f g; rfl }

/-- A sheaf of complex vector spaces underlying the additive cohomology
sheaf; its fibers are the same genuine locally holomorphic sections. -/
def holomorphicSectionComplexSheaf {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (r : ℤ) :
    letI := A.charts
    TopCat.Sheaf (ModuleCat.{v} ℂ) (TopCat.of (SphereBundleTotal Q)) := by
  letI := A.charts
  letI (U : (Opens (TopCat.of (SphereBundleTotal Q)))ᵒᵖ) :=
    coefficientSectionSheaf_addCommGroup Q D L r U
  letI (U : (Opens (TopCat.of (SphereBundleTotal Q)))ᵒᵖ) :=
    coefficientSectionSheaf_module Q D L r U
  refine { val := coefficientSectionPresheafComplex Q D L r, cond := ?_ }
  rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _
    (CategoryTheory.forget (ModuleCat.{v} ℂ))]
  convert CategoryTheory.Sheaf.cond (coefficientSectionSheaf Q D L r) using 1

/-- Restriction maps of the holomorphic section sheaf are additive. -/
def coefficientSectionPresheafAdd {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (r : ℤ) :
    letI := A.charts
    TopCat.Presheaf AddCommGrpCat (TopCat.of (SphereBundleTotal Q)) := by
  letI := A.charts
  letI (U : (Opens (TopCat.of (SphereBundleTotal Q)))ᵒᵖ) :=
    coefficientSectionSheaf_addCommGroup Q D L r U
  let T := coefficientSectionSheaf Q D L r
  exact {
    obj := fun U => AddCommGrpCat.of (T.presheaf.obj U)
    map := fun h => AddCommGrpCat.ofHom (coefficientRestrictionAddHom Q D L r h)
    map_id := by intro U; rfl
    map_comp := by intro U V W f g; rfl }

/-- The actual sheaf of abelian groups used for derived cohomology. -/
def holomorphicSectionAdditiveSheaf {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (r : ℤ) :
    letI := A.charts
    TopCat.Sheaf AddCommGrpCat (TopCat.of (SphereBundleTotal Q)) := by
  letI := A.charts
  letI (U : (Opens (TopCat.of (SphereBundleTotal Q)))ᵒᵖ) :=
    coefficientSectionSheaf_addCommGroup Q D L r U
  refine { val := coefficientSectionPresheafAdd Q D L r, cond := ?_ }
  rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _
    (CategoryTheory.forget AddCommGrpCat)]
  convert CategoryTheory.Sheaf.cond (coefficientSectionSheaf Q D L r) using 1

end
end QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas
