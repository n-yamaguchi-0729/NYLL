/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Classical.Etale
import Nyll.EtaleCohomology.Classical.ModuleCohomology
import Nyll.EtaleCohomology.Sites.FiniteHenselianSections
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Cohomology of finite algebras over a strictly local ring

The actual global-section lifting theorem makes the constant integer
sheaf projective. Hence all positive-degree étale cohomology vanishes for
every abelian sheaf, and for arbitrary module coefficients, on the spectrum
of any finite algebra over a strictly Henselian ring.

This is the finite strictly local case used in Stacks Project 59.55.2.
The finite algebra need not be reduced, local, flat, or finitely presented.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

variable (R B : Type u) [CommRing R] [HenselianLocalRing R]
  [IsSepClosed (IsLocalRing.ResidueField R)]
  [CommRing B] [Algebra R B] [Module.Finite R B]

include R

private theorem finiteHenselian_abelianGlobalSections_preservesEpimorphisms :
    ((sheafSections (Spec (.of B)).smallEtaleTopology AddCommGrpCat.{u}).obj
      (op (Scheme.Etale.mk (𝟙 (Spec (.of B)))))).PreservesEpimorphisms where
  preserves η _ := (AddCommGrpCat.epi_iff_surjective _).mpr
    (sheaf_epi_globalSections_surjective_of_finite_over_strictlyHenselian R B η)

/-- Actual global sections on a finite algebra of a strictly Henselian
ring preserve homology, and therefore exact sequences. -/
theorem abelianGlobalSections_preservesHomology_of_finite_over_strictlyHenselian :
    ((sheafSections (Spec (.of B)).smallEtaleTopology AddCommGrpCat.{u}).obj
      (op (Scheme.Etale.mk (𝟙 (Spec (.of B)))))).PreservesHomology := by
  let Γ := (sheafSections (Spec (.of B)).smallEtaleTopology AddCommGrpCat.{u}).obj
    (op (Scheme.Etale.mk (𝟙 (Spec (.of B)))))
  have : Γ.PreservesEpimorphisms :=
    finiteHenselian_abelianGlobalSections_preservesEpimorphisms R B
  have : Γ.IsRightAdjoint :=
    (constantSheafAdj (Spec (.of B)).smallEtaleTopology AddCommGrpCat.{u}
      (MorphismProperty.Over.mkIdTerminal
        (show MorphismProperty Scheme.{u} from @Etale) (Spec (.of B)))).isRightAdjoint
  exact Functor.preservesHomology_of_preservesEpis_and_kernels Γ

/-- The actual constant integer sheaf is projective on a finite scheme
over a strictly local spectrum. -/
theorem etaleConstantInteger_projective_of_finite_over_strictlyHenselian :
    Projective ((constantSheaf (Spec (.of B)).smallEtaleTopology
      AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) := by
  have hZ : Projective (AddCommGrpCat.of (ULift.{u} ℤ)) :=
    (Projective.projective_iff_preservesEpimorphisms_coyoneda_obj _).mpr
      (Functor.PreservesEpimorphisms.of_iso AddCommGrpCat.coyonedaObjIsoForget.symm)
  have : ((sheafSections (Spec (.of B)).smallEtaleTopology AddCommGrpCat.{u}).obj
      (op (Scheme.Etale.mk (𝟙 (Spec (.of B)))))).PreservesEpimorphisms :=
    finiteHenselian_abelianGlobalSections_preservesEpimorphisms R B
  exact (constantSheafAdj (Spec (.of B)).smallEtaleTopology AddCommGrpCat.{u}
    (MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) (Spec (.of B)))).map_projective _ hZ

/-- Every abelian sheaf on the spectrum of a finite algebra over a
strictly Henselian ring has zero cohomology in every positive degree. -/
theorem etaleAbelianCohomology_succ_subsingleton_of_finite_over_strictlyHenselian
    (F : Sheaf (Spec (.of B)).smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    Subsingleton (Sheaf.H.{u} F (n + 1)) := by
  have : Projective ((constantSheaf (Spec (.of B)).smallEtaleTopology
      AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) :=
    etaleConstantInteger_projective_of_finite_over_strictlyHenselian R B
  exact subsingleton_of_forall_eq 0 (fun x => Abelian.Ext.eq_zero_of_projective x)

/-- The same positive-degree vanishing holds for the existing classical
étale cohomology with any commutative coefficient ring. -/
theorem etaleCohomology_succ_isZero_of_finite_over_strictlyHenselian
    (Λ : Type u) [CommRing Λ]
    (F : Sheaf (Spec (.of B)).smallEtaleTopology (ModuleCat.{u} Λ)) (n : ℕ) :
    IsZero (etaleCohomology (Spec (.of B)) Λ F (n + 1)) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  change Subsingleton (Sheaf.H.{u}
    (Classical.forgetCoefficients.{u + 1, u, u, u}.obj F) (n + 1))
  exact etaleAbelianCohomology_succ_subsingleton_of_finite_over_strictlyHenselian R B
    (Classical.forgetCoefficients.{u + 1, u, u, u}.obj F) n

end EtaleCohomology
