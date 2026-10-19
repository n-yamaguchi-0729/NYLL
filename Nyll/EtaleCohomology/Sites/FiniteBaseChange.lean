/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.BaseChangeStalkCompatibility
import Nyll.EtaleCohomology.Sites.BaseChangeStalkProducts
import Nyll.EtaleCohomology.Sites.DirectImageBaseChange
import Nyll.EtaleCohomology.Sites.FinitePushforwardStalkSurjectivity
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Sites.Point.Conservative
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Finite direct image commutes with arbitrary base change

The actual canonical base-change transformation induces an isomorphism on
every algebraically closed geometric stalk: its product diagram has the
proved finite direct-image stalk isomorphisms and the actual inverse-image
unit isomorphisms on its other sides. Algebraic closures of residue fields
provide a conservative family of points on the original small étale site.

This proves Stacks Project 59.55.3 for arbitrary commutative module
coefficients and arbitrary base-change morphisms. The finite morphism need
not be flat or finitely presented.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology

private theorem isIso_of_productDiagram {C : Type*} [Category* C]
    {A B D E Z : C} (a : A ≅ B) (b : B ⟶ D) (c : D ⟶ Z)
    (d : A ⟶ E) (e : E ≅ Z) (hc : IsIso c) (hd : IsIso d)
    (h : a.hom ≫ b ≫ c = d ≫ e.hom) : IsIso b := by
  have hcomp : IsIso (a.hom ≫ b ≫ c) := h.symm ▸ (inferInstance : IsIso (d ≫ e.hom))
  have hbc : IsIso (b ≫ c) := IsIso.of_isIso_comp_left a.hom (b ≫ c)
  exact IsIso.of_isIso_comp_right b c

variable {X Y Y' : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (g : Y' ⟶ Y)
  (R : Type u) [CommRing R]

/-- The canonical finite base-change map is an isomorphism at every
algebraically closed geometric point of the new base. -/
theorem finiteDirectImageBaseChange_stalk_isIso
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ Y')
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    IsIso ((Scheme.pointSmallEtale t).sheafFiber.map
      ((etaleDirectImageBaseChange f g (pullback.snd f g) (pullback.fst f g)
        pullback.condition.symm R).app F)) := by
  exact isIso_of_productDiagram
    (pullbackUnitGeometricStalkIso R g t ((etalePushforward f R).obj F)) _
    (etalePushforwardStalkComparison (pullback.snd f g) t
      ((etalePullback (pullback.fst f g) R).obj F))
    (etalePushforwardStalkComparison f (t ≫ g) F)
    (baseChangeStalkProductIso f g t R F).symm
    (etalePushforwardStalkComparison_isIso (pullback.snd f g) t
      ((etalePullback (pullback.fst f g) R).obj F))
    (etalePushforwardStalkComparison_isIso f (t ≫ g) F)
    (etaleDirectImageBaseChange_stalk_product f g t R F)

/-- Stacks Project 59.55.3: the canonical finite direct-image base-change
map is an isomorphism for every sheaf of modules. -/
theorem finiteDirectImageBaseChange_app_isIso
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    IsIso ((etaleDirectImageBaseChange f g (pullback.snd f g) (pullback.fst f g)
      pullback.condition.symm R).app F) := by
  let K (y : Y') : Type u := AlgebraicClosure (Y'.residueField y)
  let s (y : Y') : Spec (.of (K y)) ⟶ Y' :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y'.residueField y) (K y))) ≫
      Y'.fromSpecResidueField y
  have hs : ⋃ y, Set.range (s y) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    refine Set.mem_iUnion.mpr ⟨y, default, ?_⟩
    exact (Scheme.Hom.comp_apply _ _ _).trans (Y'.fromSpecResidueField_apply y _)
  have hpoints := Scheme.isConservative_pointSmallEtale s hs
  apply ((hpoints.jointlyReflectIsomorphisms (ModuleCat.{u} R)).isIso_iff _).mpr
  rintro ⟨_, ⟨y⟩⟩
  change IsIso ((Scheme.pointSmallEtale (s y)).sheafFiber.map
    ((etaleDirectImageBaseChange f g (pullback.snd f g) (pullback.fst f g)
      pullback.condition.symm R).app F))
  exact finiteDirectImageBaseChange_stalk_isIso f g R (s y) F

/-- Finite direct-image base change is an isomorphism of the actual sheaf
functors, naturally in the coefficient sheaf. -/
instance finiteDirectImageBaseChange_isIso :
    IsIso (etaleDirectImageBaseChange f g (pullback.snd f g) (pullback.fst f g)
      pullback.condition.symm R) := by
  have (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
      IsIso ((etaleDirectImageBaseChange f g (pullback.snd f g) (pullback.fst f g)
        pullback.condition.symm R).app F) := finiteDirectImageBaseChange_app_isIso f g R F
  exact NatIso.isIso_of_isIso_app _

end EtaleCohomology
