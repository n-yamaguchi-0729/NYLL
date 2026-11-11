/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Constructible.FiniteEtaleSheaf
public import Nyll.EtaleCohomology.Constructible.FiniteLocallyConstantEquivalence
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteAbelianConstants
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteLocalSystemUniversalSection
public import Nyll.EtaleFundamentalGroups.Cohomology.FiberTranslation
public import Nyll.EtaleFundamentalGroups.Cohomology.KummerBoundaryRootAction
public import Nyll.EtaleFundamentalGroups.Cohomology.LocalTrivialization

/-!
# The actual finite étale representer of a Kummer boundary

The original lift sheaf is finite locally constant by the original
extension exactness and finite constant kernel. Its actual finite étale
representer therefore carries an actual universal root. The original
coefficient translation pulls back that same root by multiplication by
the original structural root of unity.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian
open EtaleCohomology

namespace EtaleFundamentalGroups.Cohomology

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
  (c : X ⟶ Spec (.of K)) {n : ℕ} [NeZero n] (hn : 0 < n) (hnK : IsUnit (n : K))

/-- The original boundary lift sheaf, with finite local constancy
supplied by its actual short exact sequence and actual finite kernel. -/
def constantKummerBoundaryLocalSystem
    (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 0) :
    EtaleFiniteLocallyConstantSetSheaf X :=
  ⟨extensionFiber (constantKummerBoundaryExtension c hn hnK a) (integerUnitSection X),
    extensionFiber_isFiniteLocallyConstant
      (constantKummerBoundaryExtension c hn hnK a) (integerUnitSection X)
      (constantKummerBoundaryExtension_shortExact c hn hnK a)
      (constantAbelian_isFiniteLocallyConstant X
        (AddCommGrpCat.of (Additive (rootsOfUnity n K))))⟩

/-- The original finite étale representability equivalence applied
to the actual Kummer boundary lift sheaf. -/
abbrev constantKummerBoundaryCover
    (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 0) : FiniteEtale X :=
  finiteLocalSystemRepresenter (constantKummerBoundaryLocalSystem c hn hnK a)

/-- The actual root obtained from the original universal section of
the actual finite étale representing cover. -/
def constantKummerBoundaryUniversalRoot
    (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 0) :
    (Γ((constantKummerBoundaryCover c hn hnK a).left, ⊤) : Type u)ˣ :=
  constantKummerBoundaryRoot c hn hnK a
    ((finiteEtaleToEtale X).obj (constantKummerBoundaryCover c hn hnK a))
    (finiteLocalSystemUniversalSection (constantKummerBoundaryLocalSystem c hn hnK a))

/-- The nth power of the actual universal root is the actual original
unit restricted to the actual representing cover. -/
theorem constantKummerBoundaryUniversalRoot_pow
    (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 0) :
    let hT := MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) X
    let T := Scheme.Etale.mk (𝟙 X)
    constantKummerBoundaryUniversalRoot c hn hnK a ^ n =
      Units.map (show (constantKummerBoundaryCover c hn hnK a).left ⟶ X from
          (constantKummerBoundaryCover c hn hnK a).hom).appTop.hom.toMonoidHom
        ((etaleMultiplicativeGroupSectionsEquiv X T)
          (Sheaf.H.equiv₀.{u} (etaleMultiplicativeGroupSheaf X) hT a)).toMul := by
  intro hT T
  let V := (finiteEtaleToEtale X).obj (constantKummerBoundaryCover c hn hnK a)
  let s := finiteLocalSystemUniversalSection (constantKummerBoundaryLocalSystem c hn hnK a)
  let v : V ⟶ T := MorphismProperty.Over.homMk
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
      V.hom (Category.comp_id V.hom)
  have hv : hT.from V = v := hT.hom_ext _ _
  have h : constantKummerBoundaryRoot c hn hnK a V s ^ n =
      (etaleMultiplicativeGroupSectionsEquiv X V
        ((etaleMultiplicativeGroupSheaf X).obj.map (hT.from V).op
          (Sheaf.H.equiv₀ (etaleMultiplicativeGroupSheaf X) hT a))).toMul :=
    constantKummerBoundaryRoot_pow c hn hnK a V s
  have hmap := congrArg (fun m : V ⟶ T =>
    (etaleMultiplicativeGroupSectionsEquiv X V
      ((etaleMultiplicativeGroupSheaf X).obj.map m.op
        (Sheaf.H.equiv₀ (etaleMultiplicativeGroupSheaf X) hT a))).toMul) hv
  exact h.trans hmap

/-- The actual morphism of representing covers induced by original
coefficient translation scales the same actual universal root. -/
theorem constantKummerBoundaryUniversalRoot_translation
    (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 0) (ζ : rootsOfUnity n K) :
    let P := constantKummerBoundaryExtension c hn hnK a
    let F := constantKummerBoundaryLocalSystem c hn hnK a
    let t : F ⟶ F := ObjectProperty.homMk
      (constantFiberTranslation (AddCommGrpCat.of (Additive (rootsOfUnity n K)))
        P.f P.g P.zero (integerUnitSection X) (Additive.ofMul ζ))
    Units.map
        ((Scheme.Hom.appTop
          (show (constantKummerBoundaryCover c hn hnK a).left ⟶
            (constantKummerBoundaryCover c hn hnK a).left from
            ((finiteEtaleEquivFiniteLocallyConstantSetSheaf X).inverse.map
              t).left)).hom.toMonoidHom)
        (constantKummerBoundaryUniversalRoot c hn hnK a) =
      Units.map (((Scheme.ΓSpecIso (.of K)).inv ≫
        ((show (constantKummerBoundaryCover c hn hnK a).left ⟶ X from
          (constantKummerBoundaryCover c hn hnK a).hom) ≫ c).appTop).hom.toMonoidHom)
          (ζ : Kˣ) * constantKummerBoundaryUniversalRoot c hn hnK a := by
  intro P F t
  let V := (finiteEtaleToEtale X).obj (constantKummerBoundaryCover c hn hnK a)
  let k : V ⟶ V := (finiteEtaleToEtale X).map
    ((finiteEtaleEquivFiniteLocallyConstantSetSheaf X).inverse.map t)
  let kScheme : V.left ⟶ V.left := k.left
  let s := finiteLocalSystemUniversalSection F
  calc
    Units.map kScheme.appTop.hom.toMonoidHom
        (constantKummerBoundaryRoot c hn hnK a V s) =
      constantKummerBoundaryRoot c hn hnK a V (F.obj.obj.map k.op s) :=
        (constantKummerBoundaryRoot_naturality c hn hnK a k s).symm
    _ = constantKummerBoundaryRoot c hn hnK a V (t.hom.hom.app (op V) s) :=
      congrArg (constantKummerBoundaryRoot c hn hnK a V)
        (finiteLocalSystemUniversalSection_naturality t)
    _ = Units.map (((Scheme.ΓSpecIso (.of K)).inv ≫
        ((show V.left ⟶ X from V.hom) ≫ c).appTop).hom.toMonoidHom)
        (ζ : Kˣ) * constantKummerBoundaryRoot c hn hnK a V s :=
      constantKummerBoundaryRoot_translation c hn hnK a V s ζ

end EtaleFundamentalGroups.Cohomology
