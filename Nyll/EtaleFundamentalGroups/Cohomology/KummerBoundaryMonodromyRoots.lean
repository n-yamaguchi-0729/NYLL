/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionMonodromy
public import Nyll.EtaleFundamentalGroups.Cohomology.GeometricUnitEvaluation
public import Nyll.EtaleFundamentalGroups.Cohomology.KummerBoundaryRepresenter
public import Nyll.EtaleFundamentalGroups.GeometricFiber.ExtendedFiberGaloisAction
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGalois
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGaloisPoint
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroup
public import Mathlib.CategoryTheory.Galois.Equivalence

/-!
# Actual roots on the original Kummer monodromy fiber

Evaluate the universal root of the actual finite étale representer at
its actual geometric fiber points. Original coefficient translations
multiply this root by the original structural coefficient, and the
original field-source Galois action acts through the same field
automorphism. No comparison of characters is supplied as a premise.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian
open EtaleCohomology

namespace EtaleFundamentalGroups.Cohomology

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
  [ConnectedSpace X] (c : X ⟶ Spec (.of K))
  {n : ℕ} [NeZero n] (hn : 0 < n) (hnK : IsUnit (n : K))
  (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 0)

local notation "A" => AddCommGrpCat.of (Additive (rootsOfUnity n K))
local notation "P" => constantKummerBoundaryExtension c hn hnK a
local notation "hP" => constantKummerBoundaryExtension_shortExact c hn hnK a

section GeometricPoint

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)

/-- The actual unit root obtained by evaluating the original universal
root on the actual geometric point of its original representing cover. -/
def constantKummerBoundaryMonodromyRoot
    (q : (extensionMonodromy A (P).f (P).g (P).zero hP (integerUnitSection X) ξ).obj.V) : Ωˣ :=
  geometricUnitEvaluation
    (FiniteEtale.fiberObjEquivHom ξ (constantKummerBoundaryCover c hn hnK a) q).left
      (constantKummerBoundaryUniversalRoot c hn hnK a)

/-- The original monodromy root is an actual nth root of the original
global unit evaluated at that same geometric point. -/
theorem constantKummerBoundaryMonodromyRoot_pow
    (q : (extensionMonodromy A (P).f (P).g (P).zero hP (integerUnitSection X) ξ).obj.V) :
    let hT := MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) X
    let T := Scheme.Etale.mk (𝟙 X)
    constantKummerBoundaryMonodromyRoot c hn hnK a ξ q ^ n =
      geometricUnitEvaluation ξ
        ((etaleMultiplicativeGroupSectionsEquiv X T)
          (Sheaf.H.equiv₀.{u} (etaleMultiplicativeGroupSheaf X) hT a)).toMul := by
  intro hT T
  let V := constantKummerBoundaryCover c hn hnK a
  let p := FiniteEtale.fiberObjEquivHom ξ V q
  let r := constantKummerBoundaryUniversalRoot c hn hnK a
  let b := ((etaleMultiplicativeGroupSectionsEquiv X T)
    (Sheaf.H.equiv₀.{u} (etaleMultiplicativeGroupSheaf X) hT a)).toMul
  calc
    geometricUnitEvaluation p.left r ^ n =
        geometricUnitEvaluation p.left (r ^ n) :=
      (map_pow (geometricUnitEvaluation p.left) r n).symm
    _ = geometricUnitEvaluation p.left (Units.map V.hom.appTop.hom.toMonoidHom b) :=
      congrArg (geometricUnitEvaluation p.left)
        (constantKummerBoundaryUniversalRoot_pow c hn hnK a)
    _ = geometricUnitEvaluation (p.left ≫ V.hom) b :=
      geometricUnitEvaluation_pullback p.left V.hom b
    _ = geometricUnitEvaluation ξ b :=
      congrArg (fun f => geometricUnitEvaluation f b) p.w

/-- The original coefficient torsor action multiplies the actual
monodromy root by the same original structural root of unity. -/
theorem constantKummerBoundaryMonodromyRoot_translation
    (ζ : rootsOfUnity n K)
    (q : (extensionMonodromy A (P).f (P).g (P).zero hP (integerUnitSection X) ξ).obj.V) :
    let _ := extensionMonodromyTorsor A (P).f (P).g (P).zero hP (integerUnitSection X) ξ
    constantKummerBoundaryMonodromyRoot c hn hnK a ξ
        (Multiplicative.ofAdd (Additive.ofMul ζ) • q) =
      Units.map (((Scheme.ΓSpecIso (.of K)).inv ≫ (ξ ≫ c).appTop ≫
        (Scheme.ΓSpecIso (.of Ω)).hom).hom.toMonoidHom) (ζ : Kˣ) *
          constantKummerBoundaryMonodromyRoot c hn hnK a ξ q := by
  intro coefficientTorsor
  let F := constantKummerBoundaryLocalSystem c hn hnK a
  let V : FiniteEtale X := constantKummerBoundaryCover c hn hnK a
  let r : (Γ(V.left, ⊤) : Type u)ˣ := constantKummerBoundaryUniversalRoot c hn hnK a
  let t : F ⟶ F := ObjectProperty.homMk
    (constantFiberTranslation A (P).f (P).g (P).zero (integerUnitSection X) (Additive.ofMul ζ))
  let k : V ⟶ V := (finiteEtaleEquivFiniteLocallyConstantSetSheaf X).inverse.map t
  let p := FiniteEtale.fiberObjEquivHom ξ V q
  have ht : (FiniteEtale.fiber ξ).map k q =
      Multiplicative.ofAdd (Additive.ofMul ζ) • q :=
    translation_on_monodromy A (P).f (P).g (P).zero hP (integerUnitSection X) ξ
      (Additive.ofMul ζ) q
  have hp : p.left ≫ k.left =
      (FiniteEtale.fiberObjEquivHom ξ V
        (Multiplicative.ofAdd (Additive.ofMul ζ) • q)).left :=
    (congrArg (fun f => f.left)
      (FiniteEtale.fiberObjEquivHom_naturality ξ k q)).trans
      (congrArg (fun z => (FiniteEtale.fiberObjEquivHom ξ V z).left) ht)
  have hbase : p.left ≫ (V.hom ≫ c) = ξ ≫ c :=
    (Category.assoc p.left V.hom c).symm.trans (congrArg (fun f => f ≫ c) p.w)
  calc
    constantKummerBoundaryMonodromyRoot c hn hnK a ξ
        (Multiplicative.ofAdd (Additive.ofMul ζ) • q) =
      geometricUnitEvaluation (p.left ≫ k.left) r :=
        congrArg (fun f => geometricUnitEvaluation f r) hp.symm
    _ = geometricUnitEvaluation p.left (Units.map k.left.appTop.hom.toMonoidHom r) :=
      (geometricUnitEvaluation_pullback p.left k.left r).symm
    _ = geometricUnitEvaluation p.left
        (Units.map (((Scheme.ΓSpecIso (.of K)).inv ≫
          ((show V.left ⟶ X from V.hom) ≫ c).appTop).hom.toMonoidHom)
          (ζ : Kˣ) * r) :=
      congrArg (geometricUnitEvaluation p.left)
        (constantKummerBoundaryUniversalRoot_translation c hn hnK a ζ)
    _ = geometricUnitEvaluation p.left
        (Units.map (((Scheme.ΓSpecIso (.of K)).inv ≫
          ((show V.left ⟶ X from V.hom) ≫ c).appTop).hom.toMonoidHom)
          (ζ : Kˣ)) * geometricUnitEvaluation p.left r := map_mul _ _ _
    _ = Units.map (((Scheme.ΓSpecIso (.of K)).inv ≫ (ξ ≫ c).appTop ≫
        (Scheme.ΓSpecIso (.of Ω)).hom).hom.toMonoidHom) (ζ : Kˣ) *
          constantKummerBoundaryMonodromyRoot c hn hnK a ξ q := by
      rw [geometricUnitEvaluation_structural, hbase]
      rfl

end GeometricPoint

/-- The original field-source fundamental-group action evaluates on
the actual monodromy root as the same original field automorphism. -/
theorem constantKummerBoundaryMonodromyRoot_fieldSource
    [IsIntegral X] (F Ω : Type u) [Field F] [Field Ω] [Algebra F Ω]
    [IsSepClosure F Ω] [IsSepClosed Ω]
    (j : Spec (.of F) ⟶ X) (σ : Gal(Ω/F))
    (q : (extensionMonodromy A (P).f (P).g (P).zero hP (integerUnitSection X)
      (Spec.algebraMap F Ω ≫ j)).obj.V) :
    constantKummerBoundaryMonodromyRoot c hn hnK a (Spec.algebraMap F Ω ≫ j)
        (FiniteEtale.fieldSourceAbsoluteGaloisHom F Ω j σ • q) =
      Units.map σ.toRingHom.toMonoidHom
        (constantKummerBoundaryMonodromyRoot c hn hnK a (Spec.algebraMap F Ω ≫ j) q) := by
  let V := constantKummerBoundaryCover c hn hnK a
  let p := Spec.algebraMap F Ω ≫ j
  let r := constantKummerBoundaryUniversalRoot c hn hnK a
  have h := FiniteEtale.fundamentalGroupHom_point_of_point_action j (Spec.algebraMap F Ω)
    (FiniteEtale.suppliedGaloisEquivFundamentalGroup F Ω σ) σ.toRingHom
    (FiniteEtale.suppliedGaloisEquivFundamentalGroup_point F Ω σ) V q
  change (FiniteEtale.fiberObjEquivHom p V
      (FiniteEtale.fieldSourceAbsoluteGaloisHom F Ω j σ • q)).left =
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (FiniteEtale.fiberObjEquivHom p V q).left at h
  exact (congrArg (fun f => geometricUnitEvaluation f r) h).trans
    (geometricUnitEvaluation_specMap (FiniteEtale.fiberObjEquivHom p V q).left σ.toRingHom r)

end EtaleFundamentalGroups.Cohomology
