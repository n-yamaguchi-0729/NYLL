/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.CategoryTheory.Galois.ContAction
public import Mathlib.CategoryTheory.Galois.Topology
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.CategoryTheory.Galois.Equivalence
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# The Galois category with a prescribed trivial monodromy subgroup

An object belongs to this full subcategory precisely when the chosen subgroup
of the original fibre-functor automorphism group fixes its entire fibre.
Closure under finite limits, finite colimits and subobjects follows from the
actual equivalence with continuous finite actions. Mathlib's full-subcategory
theorem then supplies the Galois-category axioms and the restricted fibre functor.
Normality and closedness are needed for the subsequent quotient-group comparison,
not for these categorical closure statements.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory Limits
open scoped FintypeCatDiscrete

namespace CategoryTheory.PreGaloisCategory

variable {C : Type u} [Category.{v} C] (F : C ⥤ FintypeCat.{w})
  (N : Subgroup (Aut F))

/-- The actual objects whose monodromy action is trivial on the given subgroup. -/
def trivialMonodromy : ObjectProperty C :=
  (Action.trivialOnSet FintypeCat.{w} (N : Set (Aut F))).inverseImage (functorToAction F)

/-- Trivial monodromy means pointwise fixation in the original fibre. -/
theorem trivialMonodromy_iff (X : C) :
    trivialMonodromy F N X ↔ ∀ g ∈ N, ∀ x : F.obj X, g • x = x := by
  constructor
  · intro h g hg x
    exact congrArg (fun a : End (F.obj X) => a.asHom x) (h g hg)
  · intro h g hg
    apply End.ext
    apply FintypeCat.hom_ext
    exact h g hg


/-- The actual finite monodromy representation is a coordinate of the original
continuous automorphism embedding; the fibre and its automorphisms are unchanged. -/
def fiberMonodromy (X : C) : Aut F →ₜ* Aut (F.obj X) where
  toMonoidHom :=
    (Pi.evalMonoidHom (fun Y : C => Aut (F.obj Y)) X).comp (autEmbedding F)
  continuous_toFun := (continuous_apply X).comp (autEmbedding_isClosedEmbedding F).continuous

/-- Evaluation of finite monodromy is the original natural automorphism component. -/
@[simp] theorem fiberMonodromy_apply (X : C) (g : Aut F) (x : F.obj X) :
    (fiberMonodromy F X g).asIso.hom x = g.asIso.hom.app X x := rfl

/-- Trivial monodromy is precisely containment in the kernel of the actual finite
monodromy representation. No change of fibre or permutation-action structure is made. -/
theorem trivialMonodromy_iff_le_ker_fiberMonodromy (X : C) :
    trivialMonodromy F N X ↔ N ≤ (fiberMonodromy F X).toMonoidHom.ker := by
  rw [trivialMonodromy_iff]
  constructor
  · intro h g hg
    change fiberMonodromy F X g = 1
    apply Aut.ext
    apply Iso.ext
    apply FintypeCat.hom_ext
    intro x
    exact h g hg x
  · intro h g hg x
    have heq : fiberMonodromy F X g = 1 := h hg
    exact congrArg (fun a : Aut (F.obj X) => a.asIso.hom x) heq

/-- The full subcategory of original objects with trivial `N`-monodromy. -/
abbrev TrivialMonodromy : Type u := (trivialMonodromy F N).FullSubcategory

/-- Inclusion retains the original objects and their original morphisms. -/
abbrev trivialMonodromyInclusion : TrivialMonodromy F N ⥤ C :=
  (trivialMonodromy F N).ι

/-- The restricted fibre functor uses the original fibres and fibre maps. -/
abbrev trivialMonodromyFiber : TrivialMonodromy F N ⥤ FintypeCat.{w} :=
  trivialMonodromyInclusion F N ⋙ F

variable [GaloisCategory C] [FiberFunctor F]

/-- Finite limits retain trivial monodromy. -/
instance trivialMonodromy_isClosedUnderFiniteLimits :
    (trivialMonodromy F N).IsClosedUnderFiniteLimits where
  isClosedUnderLimitsOfShape J _ _ := by
    change ((Action.trivialOnSet FintypeCat.{w} (N : Set (Aut F))).inverseImage
      (functorToContAction F ⋙
        (Action.isContinuous FintypeCat.{w} (Aut F)).ι)).IsClosedUnderLimitsOfShape J
    infer_instance

/-- Finite colimits retain trivial monodromy. -/
instance trivialMonodromy_isClosedUnderFiniteColimits :
    (trivialMonodromy F N).IsClosedUnderFiniteColimits where
  isClosedUnderColimitsOfShape J _ _ := by
    change ((Action.trivialOnSet FintypeCat.{w} (N : Set (Aut F))).inverseImage
      (functorToContAction F ⋙
        (Action.isContinuous FintypeCat.{w} (Aut F)).ι)).IsClosedUnderColimitsOfShape J
    infer_instance

/-- Subobjects retain trivial monodromy. -/
instance trivialMonodromy_isClosedUnderSubobjects :
    (trivialMonodromy F N).IsClosedUnderSubobjects :=
  inferInstanceAs (((Action.trivialOnSet FintypeCat.{w} (N : Set (Aut F))).inverseImage
    (functorToAction F)).IsClosedUnderSubobjects)

/-- The inclusion preserves epimorphisms because it creates pushouts.
Together with the established closure properties, this proves the Galois
subcategory axioms. The inherited instances give `GaloisCategory` on
`TrivialMonodromy F N` and `FiberFunctor (trivialMonodromyFiber F N)`. -/
instance trivialMonodromy_isGaloisSubcategory :
    (trivialMonodromy F N).IsGaloisSubcategory where
  preservesEpimorphisms := by
    have : HasPushouts C :=
      Adjunction.hasColimitsOfShape_of_equivalence (functorToContAction F)
    infer_instance

/-- The original fibre-action equivalence restricts to precisely the continuous
finite actions on which the same subgroup acts trivially. -/
def trivialMonodromyContActionEquivalence :
    TrivialMonodromy F N ≌
      ((Action.trivialOnSet FintypeCat.{w} (N : Set (Aut F))).inverseImage
        (Action.isContinuous FintypeCat.{w} (Aut F)).ι).FullSubcategory :=
  (functorToContAction F).asEquivalence.congrFullSubcategory rfl

end CategoryTheory.PreGaloisCategory
