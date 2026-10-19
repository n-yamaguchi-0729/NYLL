/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
import Nyll.EtaleCohomology.Classical.Etale
import Nyll.EtaleCohomology.Classical.ModuleCohomology
import Nyll.EtaleCohomology.Sites.FinitePushforwardExact
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Finite direct image and classical étale cohomology

The geometric exactness theorem for finite direct image supplies an exact
adjunction with actual inverse image. Its action on the constant integer
sheaf gives a natural comparison `Hⁿ(X, q_*F) ≃ Hⁿ(Y, F)` in every degree.
The comparison is linear for module coefficients.

Exactness also makes all positive right derived functors of the actual
direct-image functor zero. The proof maps an injective resolution and uses
its exactness in positive degrees. This proves part (2) of Stacks Project
59.55.2 and its cohomological consequences (https://stacks.math.columbia.edu/tag/03QP).
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Abelian Opposite

namespace EtaleCohomology

/-- Actual direct image is additive for arbitrary module coefficients. -/
instance etalePushforward_additive {X Y : Scheme.{u}} (q : Y ⟶ X)
    (R : Type u) [CommRing R] : (etalePushforward q R).Additive := by
  let : PreservesBinaryBiproducts (etalePushforward q R) :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

variable {X Y : Scheme.{u}} (q : Y ⟶ X) [IsFinite q]

/-- Finite direct image is exact on the abelian sheaves used by `Sheaf.H`. -/
instance etaleAbelianPushforwardFinite_preservesHomology :
    (etaleAbelianPushforward q).PreservesHomology := by
  have : (etaleAbelianPushforward q).PreservesEpimorphisms :=
    finitePushforward_preservesEpimorphisms q
  exact Functor.preservesHomology_of_preservesEpis_and_kernels _

instance etaleAbelianPushforwardFinite_preservesFiniteColimits :
    PreservesFiniteColimits (etaleAbelianPushforward q) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

/-- Finite direct image does not change classical abelian étale cohomology. -/
def etaleAbelianCohomologyFinitePushforwardEquiv
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H.{u} ((etaleAbelianPushforward q).obj F) n ≃+ Sheaf.H.{u} F n :=
  (etaleAbelianPullbackPushforwardAdjunction q).extEquiv.symm.trans
    ((((extFunctor n).mapIso
      ((etaleAbelianPullbackConstantIso q).app
        (AddCommGrpCat.of (ULift ℤ))).symm.op).app F).addCommGroupIsoToAddEquiv)

lemma etaleAbelianCohomologyFinitePushforwardEquiv_apply
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ)
    (x : ((etaleAbelianPushforward q).obj F).H n) :
    etaleAbelianCohomologyFinitePushforwardEquiv q F n x =
      (Ext.mk₀ ((etaleAbelianPullbackConstantIso q).app
        (AddCommGrpCat.of (ULift ℤ))).inv).comp
          ((etaleAbelianPullbackPushforwardAdjunction q).extEquiv.symm x) (zero_add n) := rfl

/-- Naturality in the original abelian coefficient sheaf. -/
lemma etaleAbelianCohomologyFinitePushforwardEquiv_naturality
    {F G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}} (φ : F ⟶ G) (n : ℕ)
    (x : ((etaleAbelianPushforward q).obj F).H n) :
    etaleAbelianCohomologyFinitePushforwardEquiv q G n
        (Sheaf.H.map ((etaleAbelianPushforward q).map φ) n x) =
      Sheaf.H.map φ n (etaleAbelianCohomologyFinitePushforwardEquiv q F n x) := by
  rw [etaleAbelianCohomologyFinitePushforwardEquiv_apply,
    etaleAbelianCohomologyFinitePushforwardEquiv_apply, Sheaf.H.map_apply,
    Sheaf.H.map_apply, Adjunction.extEquiv_symm_naturality_right₀,
    Ext.comp_assoc_of_third_deg_zero]

private theorem isZero_rightDerived_succ_of_exact
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasInjectiveResolutions C] (G : C ⥤ D) [G.Additive] [G.PreservesHomology]
    (F : C) (n : ℕ) : IsZero ((G.rightDerived (n + 1)).obj F) := by
  let I := injectiveResolution F
  refine IsZero.of_iso ?_ (I.isoRightDerivedObj G (n + 1))
  apply HomologicalComplex.ExactAt.isZero_homology
  exact ShortComplex.Exact.map (I.cocomplex_exactAt_succ n) G

/-- Every positive right derived finite direct image of an abelian sheaf is zero. -/
theorem etaleAbelianPushforwardFinite_rightDerived_succ_isZero
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    IsZero (((etaleAbelianPushforward q).rightDerived (n + 1)).obj F) :=
  isZero_rightDerived_succ_of_exact (etaleAbelianPushforward q) F n

variable (R : Type u) [CommRing R]

/-- The finite direct-image comparison with the original coefficient module. -/
def etaleCohomologyFinitePushforwardEquiv
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R)) (n : ℕ) :
    etaleCohomology X R ((etalePushforward q R).obj F) n ≃ₗ[R]
      etaleCohomology Y R F n :=
  AddEquiv.toLinearEquiv
    (R := R)
    (M := etaleCohomology X R ((etalePushforward q R).obj F) n)
    (M₂ := etaleCohomology Y R F n)
    (etaleAbelianCohomologyFinitePushforwardEquiv q
      (Classical.forgetCoefficients.{u + 1, u, u, u}.obj F) n)
    (fun r x => etaleAbelianCohomologyFinitePushforwardEquiv_naturality q
      (Classical.coefficientAction.{u + 1, u, u, u} F r) n x)

/-- Naturality of the coefficient-linear finite direct-image comparison. -/
lemma etaleCohomologyFinitePushforwardEquiv_naturality
    {F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R)} (φ : F ⟶ G) (n : ℕ)
    (x : etaleCohomology X R ((etalePushforward q R).obj F) n) :
    etaleCohomologyFinitePushforwardEquiv q R G n
        (Classical.cohomologyMap.{u + 1, u, u, u, u} ((etalePushforward q R).map φ) n x) =
      Classical.cohomologyMap.{u + 1, u, u, u, u} φ n
        (etaleCohomologyFinitePushforwardEquiv q R F n x) :=
  etaleAbelianCohomologyFinitePushforwardEquiv_naturality q
    (Classical.forgetCoefficients.{u + 1, u, u, u}.map φ) n x

/-- Positive right derived finite direct image vanishes with arbitrary
commutative module coefficients. -/
theorem etalePushforwardFinite_rightDerived_succ_isZero
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R)) (n : ℕ) :
    IsZero (((etalePushforward q R).rightDerived (n + 1)).obj F) :=
  isZero_rightDerived_succ_of_exact (etalePushforward q R) F n

end EtaleCohomology
