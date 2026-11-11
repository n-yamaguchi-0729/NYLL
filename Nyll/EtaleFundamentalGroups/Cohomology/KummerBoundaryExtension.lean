/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnity
public import Nyll.EtaleCohomology.Classical.FiniteLevelKummerKernel
public import Nyll.EtaleCohomology.Classical.KummerSequence
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionFiberSquare
public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionMonodromy
public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionPullback
public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionPullbackClass
public import Nyll.EtaleFundamentalGroups.Cohomology.H1Character
public import Nyll.EtaleFundamentalGroups.Cohomology.H1FiniteCover
public import Nyll.EtaleFundamentalGroups.Cohomology.IntegerH0Sections
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences

/-!
# The actual extension representing a Kummer boundary

Pull the original Kummer sequence back along the actual morphism represented
by a degree-zero class, and retain the original constant-root identification
of its kernel. Its Ext class is precisely the original Kummer boundary in
those constant coordinates. The original sheaf of lifts over integer one
maps to actual roots of the original unit section, and its original
monodromy is the canonical character of that same boundary class.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian
open EtaleCohomology

namespace EtaleFundamentalGroups.Cohomology

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
  (c : X ⟶ Spec (.of K)) {n : ℕ} (hn : 0 < n) (hnK : IsUnit (n : K))

/-- The actual pullback of the original Kummer extension along the
original degree-zero morphism, with its actual constant-root kernel. -/
abbrev constantKummerBoundaryExtension
    (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 0) :
    ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
  coefficientPullbackExtension (etaleKummerComplex X n)
    (constantRootsOfUnityKummerKernelIso c hn hnK) (Ext.addEquiv₀ a)

/-- Short exactness is supplied by the original geometric Kummer
sequence and the actual categorical pullback. -/
theorem constantKummerBoundaryExtension_shortExact
    (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 0) :
    (constantKummerBoundaryExtension c hn hnK a).ShortExact :=
  coefficientPullbackExtension_shortExact (etaleKummerComplex X n)
    (constantRootsOfUnityKummerKernelIso c hn hnK) (Ext.addEquiv₀ a)
    (etaleKummerComplex_shortExact X hn (etaleKummerExponentUnit_of_base c hnK))

/-- The original extension class is the original Kummer boundary,
transported through the actual roots-of-unity coefficient isomorphism. -/
theorem constantKummerBoundaryExtension_extClass
    (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 0) :
    (constantKummerBoundaryExtension_shortExact c hn hnK a).extClass =
      Sheaf.H.map (constantRootsOfUnityKummerKernelIso c hn hnK).inv 1
        (Sheaf.H.δ (etaleKummerComplex_shortExact X hn
          (etaleKummerExponentUnit_of_base c hnK)) 0 1 rfl a) := by
  change (coefficientPullbackExtension_shortExact (etaleKummerComplex X n)
      (constantRootsOfUnityKummerKernelIso c hn hnK) (Ext.addEquiv₀ a)
      (etaleKummerComplex_shortExact X hn
        (etaleKummerExponentUnit_of_base c hnK))).extClass =
    (a.comp (etaleKummerComplex_shortExact X hn
      (etaleKummerExponentUnit_of_base c hnK)).extClass (zero_add 1)).comp
        (Ext.mk₀ (constantRootsOfUnityKummerKernelIso c hn hnK).inv) (add_zero 1)
  rw [coefficientPullbackExtension_extClass, Ext.mk₀_addEquiv₀_apply]

/-- The original lift sheaf over integer one is the original Kummer
root sheaf over the image of the same actual degree-zero morphism. -/
def constantKummerBoundaryLiftIso
    (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 0) :
    extensionFiber (constantKummerBoundaryExtension c hn hnK a) (integerUnitSection X) ≅
      extensionFiber (etaleKummerComplex X n)
        (integerUnitSection X ≫ Functor.whiskerRight (Ext.addEquiv₀ a).hom
          (forget AddCommGrpCat.{u})) :=
  coefficientPullbackExtensionFiberIso (etaleKummerComplex X n)
    (constantRootsOfUnityKummerKernelIso c hn hnK) (Ext.addEquiv₀ a) (integerUnitSection X)

/-- A section of the actual boundary lift sheaf has an actual unit as
its original Kummer middle-term coordinate. -/
def constantKummerBoundaryRoot
    (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 0) (V : X.Etale)
    (s : (extensionFiber (constantKummerBoundaryExtension c hn hnK a)
      (integerUnitSection X)).obj.obj (op V)) :
    (Γ(V.left, ⊤) : Type u)ˣ :=
  (etaleMultiplicativeGroupSectionsEquiv X V
    ((pullback.fst (etaleMultiplicativeGroupPower X n) (Ext.addEquiv₀ a)).hom.app
      (op V) s.val)).toMul

/-- The original middle-term coordinate is an nth root of the actual
restriction of the original global unit section. -/
theorem constantKummerBoundaryRoot_pow
    (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 0) (V : X.Etale)
    (s : (extensionFiber (constantKummerBoundaryExtension c hn hnK a)
      (integerUnitSection X)).obj.obj (op V)) :
    let hT := MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) X
    constantKummerBoundaryRoot c hn hnK a V s ^ n =
      (etaleMultiplicativeGroupSectionsEquiv X V
        ((etaleMultiplicativeGroupSheaf X).obj.map (hT.from V).op
          (Sheaf.H.equiv₀.{u} (etaleMultiplicativeGroupSheaf X) hT a))).toMul := by
  intro hT
  let f := Ext.addEquiv₀ a
  let p := etaleMultiplicativeGroupPower X n
  have hp := ConcreteCategory.congr_hom
    (congrArg
      (fun k : pullback p f ⟶ etaleMultiplicativeGroupSheaf X => k.hom.app (op V))
      (pullback.condition (f := p) (g := f))) s.val
  change p.hom.app (op V) ((pullback.fst p f).hom.app (op V) s.val) =
    f.hom.app (op V) ((pullback.snd p f).hom.app (op V) s.val) at hp
  have hs : (pullback.snd p f).hom.app (op V) s.val =
      (integerUnitSection X).app (op V) PUnit.unit := s.property
  rw [hs] at hp
  have h := hp.trans (cohomologyZero_integerUnitSection
    (etaleMultiplicativeGroupSheaf X) a V)
  have he := congrArg (etaleMultiplicativeGroupSectionsEquiv X V) h
  rw [etaleMultiplicativeGroupPower_apply] at he
  exact congrArg Additive.toMul he

/-- The canonical character of the actual Kummer boundary is computed
by the original monodromy of this actual extension's lift sheaf. -/
theorem h1Character_constantKummerBoundary [ConnectedSpace X] [NeZero n]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)
    (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 0) :
    let P := constantKummerBoundaryExtension c hn hnK a
    let : TopologicalSpace (Multiplicative (Additive (rootsOfUnity n K))) := ⊥
    h1Character (AddCommGrpCat.of (Additive (rootsOfUnity n K))) ξ
        (Sheaf.H.map (constantRootsOfUnityKummerKernelIso c hn hnK).inv 1
          (Sheaf.H.δ (etaleKummerComplex_shortExact X hn
            (etaleKummerExponentUnit_of_base c hnK)) 0 1 rfl a)) =
      extensionMonodromyCharacter (AddCommGrpCat.of (Additive (rootsOfUnity n K)))
        P.f P.g P.zero (constantKummerBoundaryExtension_shortExact c hn hnK a)
        (integerUnitSection X) ξ := by
  intro P coefficientTopology
  rw [← constantKummerBoundaryExtension_extClass c hn hnK a]
  exact h1Character_extClass (AddCommGrpCat.of (Additive (rootsOfUnity n K))) ξ
    P.f P.g P.zero (constantKummerBoundaryExtension_shortExact c hn hnK a)

end EtaleFundamentalGroups.Cohomology
