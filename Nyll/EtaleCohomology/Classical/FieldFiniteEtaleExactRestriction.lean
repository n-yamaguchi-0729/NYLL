/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.FieldFiniteEtaleBasis
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective

/-!
# Exact restriction to the finite etale site of a field

The proved geometric basis equivalence transports the abelian and
Grothendieck structures to the finite etale site. Restriction preserves
actual Ext groups in every degree, including the original coefficient
and constant-integer objects. This is an exact-category comparison, not
an assumption about a cohomology theory.
-/

noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Limits Abelian

namespace EtaleCohomology

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts

instance fieldFiniteEtaleSheaves_abelian (K : Type u) [Field K] :
    Abelian (Sheaf (fieldFiniteEtaleTopology K) AddCommGrpCat.{u}) :=
  abelianOfEquivalence (fieldFiniteEtaleSheafEquivalence K AddCommGrpCat.{u}).functor

instance fieldFiniteEtaleSheaves_grothendieck (K : Type u) [Field K] :
    IsGrothendieckAbelian.{u}
      (Sheaf (fieldFiniteEtaleTopology K) AddCommGrpCat.{u}) :=
  IsGrothendieckAbelian.of_equivalence
    (fieldFiniteEtaleSheafEquivalence K AddCommGrpCat.{u}).symm

/-- Restriction of an actual small etale abelian sheaf to the actual
finite etale objects of the field. -/
abbrev fieldFiniteEtaleAbelianRestriction (K : Type u) [Field K] :
    Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf (fieldFiniteEtaleTopology K) AddCommGrpCat.{u} :=
  (fieldFiniteEtaleSheafEquivalence K AddCommGrpCat.{u}).inverse

instance fieldFiniteEtaleAbelianRestriction_additive (K : Type u) [Field K] :
    (fieldFiniteEtaleAbelianRestriction K).Additive where
  map_add {F G} g h := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    rfl

/-- Actual Ext groups in all degrees agree with their restrictions to
the proved finite etale basis. The equivalence is the original exact
functor map on Ext, so it retains coefficient and extension data. -/
def fieldFiniteEtaleExtEquiv (K : Type u) [Field K]
    (F G : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    Ext.{u} F G n ≃+
      Ext.{u} ((fieldFiniteEtaleAbelianRestriction K).obj F)
        ((fieldFiniteEtaleAbelianRestriction K).obj G) n :=
  AddEquiv.ofBijective ((fieldFiniteEtaleAbelianRestriction K).mapExtAddHom F G n)
    ((fieldFiniteEtaleAbelianRestriction K).mapExt_bijective_of_preservesInjectiveObjects F G n)

end EtaleCohomology
