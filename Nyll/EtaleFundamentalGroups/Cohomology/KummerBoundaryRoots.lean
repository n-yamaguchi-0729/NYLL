/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnity
public import Nyll.EtaleCohomology.Classical.KummerSequence
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionFiberSquare
public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionPullbackClass
public import Nyll.EtaleFundamentalGroups.Cohomology.H1FiniteCover
public import Nyll.EtaleFundamentalGroups.Cohomology.IntegerH0Sections
public import Nyll.EtaleFundamentalGroups.Cohomology.KummerBoundaryExtension
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Types.Basic

/-!
# Actual roots in the original Kummer boundary lift sheaf

The lift sheaf of the original Kummer boundary has exactly the actual
nth roots of the original unit as its sections. This comparison uses the
literal first projection of the actual categorical pullback extension.
It is compatible with the original restriction maps on units.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian
open EtaleCohomology

namespace EtaleFundamentalGroups.Cohomology

/-- Sections of the original Kummer fiber over the actual degree-zero
section are exactly the actual roots of its restriction. -/
def kummerExtensionFiberRootEquiv (X : Scheme.{u}) (n : ℕ)
    (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 0) (V : X.Etale) :
    let hT := MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) X
    (extensionFiber (etaleKummerComplex X n)
      (integerUnitSection X ≫ Functor.whiskerRight (Ext.addEquiv₀ a).hom
        (forget AddCommGrpCat.{u}))).obj.obj (op V) ≃
      {b : (Γ(V.left, ⊤) : Type u)ˣ // b ^ n =
        (etaleMultiplicativeGroupSectionsEquiv X V
          ((etaleMultiplicativeGroupSheaf X).obj.map (hT.from V).op
            (Sheaf.H.equiv₀.{u} (etaleMultiplicativeGroupSheaf X) hT a))).toMul} := by
  intro hT
  refine
    { toFun := fun s => ⟨(etaleMultiplicativeGroupSectionsEquiv X V s.val).toMul, ?_⟩
      invFun := fun b => ⟨(etaleMultiplicativeGroupSectionsEquiv X V).symm
        (Additive.ofMul b.val), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hs : (etaleMultiplicativeGroupPower X n).hom.app (op V) s.val =
        (Ext.addEquiv₀ a).hom.app (op V)
          ((integerUnitSection X).app (op V) PUnit.unit) := s.property
    have h := congrArg (etaleMultiplicativeGroupSectionsEquiv X V)
      (hs.trans (cohomologyZero_integerUnitSection
        (etaleMultiplicativeGroupSheaf X) a V))
    rw [etaleMultiplicativeGroupPower_apply] at h
    exact congrArg Additive.toMul h
  · change (etaleMultiplicativeGroupPower X n).hom.app (op V)
        ((etaleMultiplicativeGroupSectionsEquiv X V).symm (Additive.ofMul b.val)) =
      (Ext.addEquiv₀ a).hom.app (op V)
        ((integerUnitSection X).app (op V) PUnit.unit)
    apply (etaleMultiplicativeGroupSectionsEquiv X V).injective
    rw [etaleMultiplicativeGroupPower_apply, AddEquiv.apply_symm_apply]
    apply Additive.toMul.injective
    change b.val ^ n = (etaleMultiplicativeGroupSectionsEquiv X V
      ((Ext.addEquiv₀ a).hom.app (op V)
        ((integerUnitSection X).app (op V) PUnit.unit))).toMul
    simpa only [cohomologyZero_integerUnitSection
      (etaleMultiplicativeGroupSheaf X) a V] using b.property
  · intro s
    apply Subtype.ext
    exact (etaleMultiplicativeGroupSectionsEquiv X V).symm_apply_apply s.val
  · intro b
    apply Subtype.ext
    exact congrArg Additive.toMul
      ((etaleMultiplicativeGroupSectionsEquiv X V).apply_symm_apply
        (Additive.ofMul b.val))

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
  (c : X ⟶ Spec (.of K)) {n : ℕ} (hn : 0 < n) (hnK : IsUnit (n : K))

/-- The actual lift-sheaf isomorphism retains the literal middle-term
coordinate of the original categorical pullback extension. -/
theorem constantKummerBoundaryLiftIso_hom_val
    (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 0) (V : X.Etale)
    (s : (extensionFiber (constantKummerBoundaryExtension c hn hnK a)
      (integerUnitSection X)).obj.obj (op V)) :
    ((constantKummerBoundaryLiftIso c hn hnK a).hom.hom.app (op V) s).val =
      (pullback.fst (etaleMultiplicativeGroupPower X n)
        (Ext.addEquiv₀ a)).hom.app (op V) s.val := by
  have h := coefficientPullbackExtensionFiberIso_hom_inclusion
    (etaleKummerComplex X n) (constantRootsOfUnityKummerKernelIso c hn hnK)
    (Ext.addEquiv₀ a) (integerUnitSection X)
  exact ConcreteCategory.congr_hom
    (congrArg
      (fun f : extensionFiber (constantKummerBoundaryExtension c hn hnK a)
          (integerUnitSection X) ⟶
          (sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj
            (etaleKummerComplex X n).X₂ => f.hom.app (op V)) h) s

/-- The actual boundary lift sheaf is identified sectionwise with the
actual roots of the same original unit, using the original projection. -/
def constantKummerBoundaryRootEquiv
    (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 0) (V : X.Etale) :
    let hT := MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) X
    (extensionFiber (constantKummerBoundaryExtension c hn hnK a)
      (integerUnitSection X)).obj.obj (op V) ≃
      {b : (Γ(V.left, ⊤) : Type u)ˣ // b ^ n =
        (etaleMultiplicativeGroupSectionsEquiv X V
          ((etaleMultiplicativeGroupSheaf X).obj.map (hT.from V).op
            (Sheaf.H.equiv₀.{u} (etaleMultiplicativeGroupSheaf X) hT a))).toMul} := by
  intro hT
  exact (((sheafSections X.smallEtaleTopology (Type u)).obj (op V)).mapIso
    (constantKummerBoundaryLiftIso c hn hnK a)).toEquiv.trans
      (kummerExtensionFiberRootEquiv X n a V)

/-- The section equivalence has exactly the root coordinate already
defined by the original Kummer pullback projection. -/
theorem constantKummerBoundaryRootEquiv_val
    (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 0) (V : X.Etale)
    (s : (extensionFiber (constantKummerBoundaryExtension c hn hnK a)
      (integerUnitSection X)).obj.obj (op V)) :
    (constantKummerBoundaryRootEquiv c hn hnK a V s).val =
      constantKummerBoundaryRoot c hn hnK a V s := by
  change (etaleMultiplicativeGroupSectionsEquiv X V
      (((constantKummerBoundaryLiftIso c hn hnK a).hom.hom.app (op V) s).val)).toMul =
    (etaleMultiplicativeGroupSectionsEquiv X V
      ((pullback.fst (etaleMultiplicativeGroupPower X n)
        (Ext.addEquiv₀ a)).hom.app (op V) s.val)).toMul
  exact congrArg (fun t => (etaleMultiplicativeGroupSectionsEquiv X V t).toMul)
    (constantKummerBoundaryLiftIso_hom_val c hn hnK a V s)

/-- Restriction of the original boundary lift sheaf becomes ordinary
pullback of the same actual unit root along the original scheme map. -/
theorem constantKummerBoundaryRoot_naturality
    (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 0)
    {V W : X.Etale} (m : V ⟶ W)
    (s : (extensionFiber (constantKummerBoundaryExtension c hn hnK a)
      (integerUnitSection X)).obj.obj (op W)) :
    constantKummerBoundaryRoot c hn hnK a V
        ((extensionFiber (constantKummerBoundaryExtension c hn hnK a)
          (integerUnitSection X)).obj.map m.op s) =
      Units.map m.left.appTop.hom.toMonoidHom
        (constantKummerBoundaryRoot c hn hnK a W s) := by
  let p := pullback.fst (etaleMultiplicativeGroupPower X n) (Ext.addEquiv₀ a)
  have h := ConcreteCategory.congr_hom (p.hom.naturality m.op) s.val
  exact congrArg (fun t => (etaleMultiplicativeGroupSectionsEquiv X V t).toMul) h

end EtaleFundamentalGroups.Cohomology
