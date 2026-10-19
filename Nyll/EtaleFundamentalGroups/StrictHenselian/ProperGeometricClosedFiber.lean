/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperHenselianFullyFaithful
import Nyll.EtaleFundamentalGroups.GeometricFiber.ProperFieldBaseChange
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkHenselian
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkResidue
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkSpecializationLift
import Nyll.EtaleFundamentalGroups.StrictHenselian.ProperClosedFiberComparison
import Nyll.SchemeTheory.FiniteEtale.BaseChange.PullbackComposition
import Nyll.SchemeTheory.Pi1.Affine.Over
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The geometric closed fiber in the actual strict local total space

For a proper family, restriction from its strict local model to the originally
specified geometric closed fiber is fully faithful on finite étale covers.
The morphism is the composite of the actual residue-field comparison and the
actual closed-fiber inclusion. Its coefficient projection is the original
geometric-stalk evaluation, and its defining square is cartesian.

The proof uses henselian lifting of finite étale morphisms and the proved
proper comparison for extensions of separably closed fields. It requires
neither flatness nor Noetherianity. Essential surjectivity is a separate part
of Stacks Project, Lemma 58.9.1, https://stacks.math.columbia.edu/tag/0A48.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace EtaleFundamentalGroups.StrictHenselian

universe u

attribute [local instance] AlgebraicGeometry.FiniteEtale.finiteEtaleOverCategoryCoherence
  AlgebraicGeometry.FiniteEtale.finiteEtaleHasPullbacksAlongCoherence
  AlgebraicGeometry.FiniteEtale.finiteEtaleStableUnderBaseChangeAlongCoherence

variable {X S : Scheme.{u}} {Ω : Type u} [Field Ω]
  (s : Spec (CommRingCat.of Ω) ⟶ S) (f : X ⟶ S)

/-- The originally specified geometric closed fiber maps to the actual
strict local total space through the actual residue field. -/
def localGeometricFiberInclusion :
    Limits.pullback f s ⟶ Limits.pullback f (localGeometricStalkToScheme s) :=
  localGeometricClosedFiberMap s f ≫ localGeometricClosedFiberInclusion s f

/-- The geometric closed-fiber inclusion preserves the original total-space
projection. -/
theorem localGeometricFiberInclusion_fst :
    localGeometricFiberInclusion s f ≫
      Limits.pullback.fst f (localGeometricStalkToScheme s) =
        Limits.pullback.fst f s := by
  have hclosed : localGeometricClosedFiberInclusion s f ≫
      Limits.pullback.fst f (localGeometricStalkToScheme s) =
        Limits.pullback.fst f (localGeometricResiduePoint s) :=
    Limits.pullback.lift_fst _ _ _
  exact (Category.assoc _ _ _).trans
    ((congrArg (localGeometricClosedFiberMap s f ≫ ·) hclosed).trans
      (localGeometricClosedFiberMap_fst s f))

/-- The coefficient map of the inclusion is the evaluation at the original
geometric point, with the original strict local ring. -/
theorem localGeometricFiberInclusion_snd :
    localGeometricFiberInclusion s f ≫
      Limits.pullback.snd f (localGeometricStalkToScheme s) =
        Limits.pullback.snd f s ≫ Spec.map (geometricStalkEvaluation
          (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom))) := by
  let p := Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom)
  let r := Spec.map (CommRingCat.ofHom (IsLocalRing.residue (geometricStalk p)))
  let e := Spec.map (CommRingCat.ofHom (geometricStalkResidueEmbedding p))
  have hclosed : localGeometricClosedFiberInclusion s f ≫
      Limits.pullback.snd f (localGeometricStalkToScheme s) =
        Limits.pullback.snd f (localGeometricResiduePoint s) ≫ r :=
    Limits.pullback.lift_snd _ _ _
  have hfield : localGeometricClosedFiberMap s f ≫
      Limits.pullback.snd f (localGeometricResiduePoint s) =
        Limits.pullback.snd f s ≫ e :=
    AlgebraicGeometry.FiniteEtale.fieldBaseChangeMap_snd f
      (localGeometricResiduePoint s) s (geometricStalkResidueEmbedding p)
      (localGeometricResiduePoint_triangle s).symm
  have heval : e ≫ r = Spec.map (geometricStalkEvaluation p) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun q => Spec.map (CommRingCat.ofHom q))
      (IsLocalRing.ResidueField.lift_comp_residue (geometricStalkEvaluation p).hom)
  change (localGeometricClosedFiberMap s f ≫
    localGeometricClosedFiberInclusion s f) ≫ _ = _
  rw [Category.assoc, hclosed, ← Category.assoc, hfield, Category.assoc, heval]

/-- The specified geometric closed fiber is the cartesian fiber of the
strict local model along its original evaluation homomorphism. -/
theorem localGeometricFiberInclusion_isPullback :
    IsPullback (localGeometricFiberInclusion s f) (Limits.pullback.snd f s)
      (Limits.pullback.snd f (localGeometricStalkToScheme s))
      (Spec.map (geometricStalkEvaluation
        (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom)))) := by
  have heval : Spec.map (geometricStalkEvaluation
      (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom))) ≫
        localGeometricStalkToScheme s = s := by
    simpa only [CommRingCat.ofHom_hom] using localGeometricStalkToScheme_evaluation s
  apply IsPullback.of_right (p := localGeometricFiberInclusion_snd s f)
    (t := IsPullback.of_hasPullback f (localGeometricStalkToScheme s))
  rw [localGeometricFiberInclusion_fst, heval]
  exact IsPullback.of_hasPullback f s

variable [IsProper f]

/-- Restriction to the actual strict local closed fiber is fully faithful
for a proper family, over its constructed henselian local ring. -/
def pullbackFullyFaithful_localGeometricClosedFiberInclusion :
    (AlgebraicGeometry.FiniteEtale.pullback
      (localGeometricClosedFiberInclusion s f)).FullyFaithful := by
  let p := Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo s).hom)
  let H : CommRingCat.{u} := geometricStalk p
  have hHenselian : HenselianLocalRing H := geometricStalk_henselianLocalRing p
  let g : Limits.pullback f (localGeometricStalkToScheme s) ⟶
      Spec (CommRingCat.of H) := Limits.pullback.snd f (localGeometricStalkToScheme s)
  let r := Spec.map (CommRingCat.ofHom (IsLocalRing.residue H))
  let i := localGeometricClosedFiberInclusion s f
  let h := localGeometricClosedFiberInclusion_isPullback s f
  let e : Limits.pullback f (localGeometricResiduePoint s) ≅ Limits.pullback g r :=
    h.isoPullback
  let FF := FiniteEtale.pullbackFullyFaithful_closedFiber_of_isProper_of_henselianLocalRing
    (R := H) g
  have hFull : (AlgebraicGeometry.FiniteEtale.pullback (Limits.pullback.fst g r)).Full :=
    FF.full
  have hFaithful :
      (AlgebraicGeometry.FiniteEtale.pullback (Limits.pullback.fst g r)).Faithful :=
    FF.faithful
  let E : FiniteEtale (Limits.pullback g r) ≌
      FiniteEtale (Limits.pullback f (localGeometricResiduePoint s)) :=
    MorphismProperty.Over.pullbackIso (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ e.symm
  have hE : (AlgebraicGeometry.FiniteEtale.pullback e.hom).IsEquivalence :=
    E.isEquivalence_functor
  let c : AlgebraicGeometry.FiniteEtale.pullback i ≅
      AlgebraicGeometry.FiniteEtale.pullback (Limits.pullback.fst g r) ⋙
        AlgebraicGeometry.FiniteEtale.pullback e.hom :=
    MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
      e.hom (Limits.pullback.fst g r) i h.isoPullback_hom_fst.symm
  have hFullI : (AlgebraicGeometry.FiniteEtale.pullback i).Full :=
    Functor.Full.of_iso c.symm
  have hFaithfulI : (AlgebraicGeometry.FiniteEtale.pullback i).Faithful :=
    Functor.Faithful.of_iso c.symm
  exact Functor.FullyFaithful.ofFullyFaithful (AlgebraicGeometry.FiniteEtale.pullback i)

/-- Restriction from the strict local total space to the originally specified
geometric closed fiber is fully faithful on finite étale covers. -/
def pullbackFullyFaithful_localGeometricFiberInclusion [IsSepClosed Ω] :
    (AlgebraicGeometry.FiniteEtale.pullback (localGeometricFiberInclusion s f)).FullyFaithful := by
  let i := localGeometricClosedFiberInclusion s f
  let e := localGeometricClosedFiberMap s f
  let FF := pullbackFullyFaithful_localGeometricClosedFiberInclusion s f
  have hFull : (AlgebraicGeometry.FiniteEtale.pullback i).Full := FF.full
  have hFaithful : (AlgebraicGeometry.FiniteEtale.pullback i).Faithful := FF.faithful
  have hField : (AlgebraicGeometry.FiniteEtale.pullback e).IsEquivalence :=
    pullback_localGeometricClosedFiberMap_isEquivalence s f
  let c : AlgebraicGeometry.FiniteEtale.pullback (localGeometricFiberInclusion s f) ≅
      AlgebraicGeometry.FiniteEtale.pullback i ⋙ AlgebraicGeometry.FiniteEtale.pullback e :=
    MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
      e i (localGeometricFiberInclusion s f) rfl
  have hFullG :
      (AlgebraicGeometry.FiniteEtale.pullback (localGeometricFiberInclusion s f)).Full :=
    Functor.Full.of_iso c.symm
  have hFaithfulG :
      (AlgebraicGeometry.FiniteEtale.pullback (localGeometricFiberInclusion s f)).Faithful :=
    Functor.Faithful.of_iso c.symm
  exact Functor.FullyFaithful.ofFullyFaithful
    (AlgebraicGeometry.FiniteEtale.pullback (localGeometricFiberInclusion s f))

end EtaleFundamentalGroups.StrictHenselian
