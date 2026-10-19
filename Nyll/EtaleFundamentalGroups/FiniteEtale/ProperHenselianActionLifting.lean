/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperHenselianFullyFaithful
import Nyll.SchemeTheory.FiniteEtale.BaseChange.PullbackComposition
import Nyll.SchemeTheory.Pi1.Affine.Over
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Lifting overlap comparisons over a proper henselian family

Suppose a finite étale cover `W` over `Y` is actually given, together with an
isomorphism from its closed-fiber restriction to the pullback of an actual
cover `V` of the closed fiber of `X`. For two maps from a proper `R`-scheme
`Z` to `Y` over `X`, we construct an isomorphism between the two pullbacks of
`W`. Its restriction is the comparison obtained from the original `V` and
the original closed-fiber isomorphism.

The construction uses the proved full faithfulness over an arbitrary
henselian local ring. The lifted comparisons satisfy identity and composition
laws on each proper `Z`. In particular, taking `Z = Y ×[X] Y` constructs the
double-overlap isomorphism when `Y` and `X` are related by a proper morphism
and `X` is proper over `R`.

This supplies the lifting of actual comparison data used in proper descent.
It does not construct `W` or assert effectivity of a proper descent datum.
The full comparison is Stacks Project, Lemma 58.9.1:
https://stacks.math.columbia.edu/tag/0A48.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FiniteEtale.ProperHenselianActionLifting

universe u

attribute [local instance] finiteEtaleOverCategoryCoherence
  finiteEtaleHasPullbacksAlongCoherence finiteEtaleStableUnderBaseChangeAlongCoherence

section Restriction

variable {X X₀ Y Z : Scheme.{u}}
  (i : X₀ ⟶ X) (p : Y ⟶ X) (g : Z ⟶ X)

/-- The map on the actual base changes induced by a map over `X`. -/
def restrictionLift (u : Z ⟶ Y) (hu : u ≫ p = g) :
    Limits.pullback g i ⟶ Limits.pullback p i :=
  Limits.pullback.lift (Limits.pullback.fst g i ≫ u) (Limits.pullback.snd g i)
    (by rw [Category.assoc, hu]; exact Limits.pullback.condition)

/-- The restricted map preserves the projection to the original cover base. -/
theorem restrictionLift_fst (u : Z ⟶ Y) (hu : u ≫ p = g) :
    restrictionLift i p g u hu ≫ Limits.pullback.fst p i =
      Limits.pullback.fst g i ≫ u :=
  Limits.pullback.lift_fst _ _ _

/-- The restricted map preserves the specified base change. -/
theorem restrictionLift_snd (u : Z ⟶ Y) (hu : u ≫ p = g) :
    restrictionLift i p g u hu ≫ Limits.pullback.snd p i =
      Limits.pullback.snd g i :=
  Limits.pullback.lift_snd _ _ _

variable (W : FiniteEtale Y) (V : FiniteEtale X₀)
  (e : (FiniteEtale.pullback (Limits.pullback.fst p i)).obj W ≅
    (FiniteEtale.pullback (Limits.pullback.snd p i)).obj V)

/-- The pullback of the given comparison identifies a restricted pullback of
`W` with the pullback of the original `V`, using the actual cartesian maps. -/
def restrictionIso (u : Z ⟶ Y) (hu : u ≫ p = g) :
    (FiniteEtale.pullback (Limits.pullback.fst g i)).obj
        ((FiniteEtale.pullback u).obj W) ≅
      (FiniteEtale.pullback (Limits.pullback.snd g i)).obj V := by
  let l := restrictionLift i p g u hu
  let c₁ : FiniteEtale.pullback (Limits.pullback.fst g i ≫ u) ≅
      FiniteEtale.pullback u ⋙ FiniteEtale.pullback (Limits.pullback.fst g i) :=
    MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
      (Limits.pullback.fst g i) u (Limits.pullback.fst g i ≫ u) rfl
  let c₂ : FiniteEtale.pullback (Limits.pullback.fst g i ≫ u) ≅
      FiniteEtale.pullback (Limits.pullback.fst p i) ⋙ FiniteEtale.pullback l :=
    MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
      l (Limits.pullback.fst p i) (Limits.pullback.fst g i ≫ u)
      (restrictionLift_fst i p g u hu).symm
  let c₃ : FiniteEtale.pullback (Limits.pullback.snd g i) ≅
      FiniteEtale.pullback (Limits.pullback.snd p i) ⋙ FiniteEtale.pullback l :=
    MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
      l (Limits.pullback.snd p i) (Limits.pullback.snd g i)
      (restrictionLift_snd i p g u hu).symm
  exact (c₁.app W).symm ≪≫ c₂.app W ≪≫
    (FiniteEtale.pullback l).mapIso e ≪≫ (c₃.app V).symm

end Restriction

section CategoricalComparison

variable {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
  (F : C ⥤ D) (FF : F.FullyFaithful)

private def comparisonPreimageIso (U V : C) (T : D)
    (a : F.obj U ≅ T) (b : F.obj V ≅ T) : U ≅ V :=
  FF.preimageIso (a ≪≫ b.symm)

private theorem comparisonPreimageIso_map (U V : C) (T : D)
    (a : F.obj U ≅ T) (b : F.obj V ≅ T) :
    F.map (comparisonPreimageIso F FF U V T a b).hom = a.hom ≫ b.inv :=
  FF.map_preimage (a.hom ≫ b.inv)

private theorem comparisonPreimageIso_refl (U : C) (T : D) (a : F.obj U ≅ T) :
    comparisonPreimageIso F FF U U T a a = Iso.refl U := by
  apply Iso.ext
  apply FF.map_injective
  rw [comparisonPreimageIso_map, Iso.refl_hom, CategoryTheory.Functor.map_id, Iso.hom_inv_id]

private theorem comparisonPreimageIso_trans (U V W : C) (T : D)
    (a : F.obj U ≅ T) (b : F.obj V ≅ T) (c : F.obj W ≅ T) :
    comparisonPreimageIso F FF U V T a b ≪≫ comparisonPreimageIso F FF V W T b c =
      comparisonPreimageIso F FF U W T a c := by
  apply Iso.ext
  apply FF.map_injective
  rw [Iso.trans_hom, CategoryTheory.Functor.map_comp, comparisonPreimageIso_map,
    comparisonPreimageIso_map, comparisonPreimageIso_map]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end CategoricalComparison

section Proper

variable {R : Type u} [CommRing R] [HenselianLocalRing R]
  {X Y Z : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

local notation "ι" => Limits.pullback.fst f
  (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))

/-- Full faithfulness on the actual iterated closed fiber follows from the
proper henselian theorem and its concrete cartesian comparison. -/
def closedFiberPullbackFullyFaithful (g : Z ⟶ X) [IsProper (g ≫ f)] :
    (FiniteEtale.pullback (Limits.pullback.fst g ι)).FullyFaithful := by
  let r := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  let h := (IsPullback.of_hasPullback g ι).paste_vert (IsPullback.of_hasPullback f r)
  let c : Limits.pullback g ι ≅ Limits.pullback (g ≫ f) r := h.isoPullback
  let E : FiniteEtale (Limits.pullback (g ≫ f) r) ≌ FiniteEtale (Limits.pullback g ι) :=
    MorphismProperty.Over.pullbackIso (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ c.symm
  have hE : (FiniteEtale.pullback c.hom).IsEquivalence := E.isEquivalence_functor
  let FF := pullbackFullyFaithful_closedFiber_of_isProper_of_henselianLocalRing (g ≫ f)
  let e : FiniteEtale.pullback (Limits.pullback.fst g ι) ≅
      FiniteEtale.pullback (Limits.pullback.fst (g ≫ f) r) ⋙
        FiniteEtale.pullback c.hom :=
    MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
      c.hom (Limits.pullback.fst (g ≫ f) r) (Limits.pullback.fst g ι)
      h.isoPullback_hom_fst.symm
  exact (FF.comp
    (Functor.FullyFaithful.ofFullyFaithful (FiniteEtale.pullback c.hom))).ofIso e.symm

variable (p : Y ⟶ X) (g : Z ⟶ X) [IsProper (g ≫ f)] (W : FiniteEtale Y)

/-- The original closed-fiber comparison uniquely lifts to the two actual
pullbacks of `W` on the proper scheme `Z`. The original closed-fiber objects
are shared in the statement before the comparison is supplied. -/
def liftedIso :
    let r : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶
        Spec (CommRingCat.of R) :=
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
    let X₀ : Scheme.{u} := Limits.pullback f r
    let i : X₀ ⟶ X := Limits.pullback.fst f r
    let Y₀ : Scheme.{u} := Limits.pullback p i
    let P : FiniteEtale Y ⥤ FiniteEtale Y₀ :=
      FiniteEtale.pullback (Limits.pullback.fst p i)
    let Q : FiniteEtale X₀ ⥤ FiniteEtale Y₀ :=
      FiniteEtale.pullback (Limits.pullback.snd p i)
    let U : (Z ⟶ Y) → FiniteEtale Z := fun u => (FiniteEtale.pullback u).obj W
    ∀ (V : FiniteEtale X₀) (_e : P.obj W ≅ Q.obj V)
      (u : Z ⟶ Y) (_hu : u ≫ p = g) (v : Z ⟶ Y) (_hv : v ≫ p = g), U u ≅ U v := by
  intro r X₀ i Y₀ P Q U V e u hu v hv
  let Z₀ : Scheme.{u} := Limits.pullback g i
  let F : FiniteEtale Z ⥤ FiniteEtale Z₀ :=
    FiniteEtale.pullback (Limits.pullback.fst g i)
  let FF : F.FullyFaithful :=
    closedFiberPullbackFullyFaithful (R := R) (X := X) (Z := Z) f g
  let T : FiniteEtale Z₀ := (FiniteEtale.pullback (Limits.pullback.snd g i)).obj V
  let a : F.obj (U u) ≅ T :=
    restrictionIso (X := X) (X₀ := X₀) (Y := Y) (Z := Z) i p g W V e u hu
  let b : F.obj (U v) ≅ T :=
    restrictionIso (X := X) (X₀ := X₀) (Y := Y) (Z := Z) i p g W V e v hv
  exact comparisonPreimageIso F FF (U u) (U v) T a b

/-- Restriction of the lifted map is the comparison from the specified
closed-fiber isomorphism, with the original cover `V` retained. -/
theorem liftedIso_hom_restrict :
    let r : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶
        Spec (CommRingCat.of R) :=
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
    let X₀ : Scheme.{u} := Limits.pullback f r
    let i : X₀ ⟶ X := Limits.pullback.fst f r
    let Y₀ : Scheme.{u} := Limits.pullback p i
    let Z₀ : Scheme.{u} := Limits.pullback g i
    let F : FiniteEtale Z ⥤ FiniteEtale Z₀ :=
      FiniteEtale.pullback (Limits.pullback.fst g i)
    let P : FiniteEtale Y ⥤ FiniteEtale Y₀ :=
      FiniteEtale.pullback (Limits.pullback.fst p i)
    let Q : FiniteEtale X₀ ⥤ FiniteEtale Y₀ :=
      FiniteEtale.pullback (Limits.pullback.snd p i)
    let U : (Z ⟶ Y) → FiniteEtale Z := fun u => (FiniteEtale.pullback u).obj W
    ∀ V : FiniteEtale X₀,
      let T : FiniteEtale Z₀ := (FiniteEtale.pullback (Limits.pullback.snd g i)).obj V
      ∀ (e : P.obj W ≅ Q.obj V)
        (u : Z ⟶ Y) (hu : u ≫ p = g) (v : Z ⟶ Y) (hv : v ≫ p = g),
        let a : F.obj (U u) ≅ T :=
          restrictionIso (X := X) (X₀ := X₀) (Y := Y) (Z := Z) i p g W V e u hu
        let b : F.obj (U v) ≅ T :=
          restrictionIso (X := X) (X₀ := X₀) (Y := Y) (Z := Z) i p g W V e v hv
        F.map (liftedIso (R := R) f p g W V e u hu v hv).hom = a.hom ≫ b.inv := by
  intro r X₀ i Y₀ Z₀ F P Q U V T e u hu v hv a b
  let FF : F.FullyFaithful :=
    closedFiberPullbackFullyFaithful (R := R) (X := X) (Z := Z) f g
  exact comparisonPreimageIso_map F FF (U u) (U v) T a b

/-- Both directions of the lifted isomorphism recover the comparison
constructed from the actual closed-fiber data. -/
theorem liftedIso_restrict :
    let r : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶
        Spec (CommRingCat.of R) :=
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
    let X₀ : Scheme.{u} := Limits.pullback f r
    let i : X₀ ⟶ X := Limits.pullback.fst f r
    let Y₀ : Scheme.{u} := Limits.pullback p i
    let Z₀ : Scheme.{u} := Limits.pullback g i
    let F : FiniteEtale Z ⥤ FiniteEtale Z₀ :=
      FiniteEtale.pullback (Limits.pullback.fst g i)
    let P : FiniteEtale Y ⥤ FiniteEtale Y₀ :=
      FiniteEtale.pullback (Limits.pullback.fst p i)
    let Q : FiniteEtale X₀ ⥤ FiniteEtale Y₀ :=
      FiniteEtale.pullback (Limits.pullback.snd p i)
    let U : (Z ⟶ Y) → FiniteEtale Z := fun u => (FiniteEtale.pullback u).obj W
    ∀ V : FiniteEtale X₀,
      let T : FiniteEtale Z₀ := (FiniteEtale.pullback (Limits.pullback.snd g i)).obj V
      ∀ (e : P.obj W ≅ Q.obj V)
        (u : Z ⟶ Y) (hu : u ≫ p = g) (v : Z ⟶ Y) (hv : v ≫ p = g),
        let a : F.obj (U u) ≅ T :=
          restrictionIso (X := X) (X₀ := X₀) (Y := Y) (Z := Z) i p g W V e u hu
        let b : F.obj (U v) ≅ T :=
          restrictionIso (X := X) (X₀ := X₀) (Y := Y) (Z := Z) i p g W V e v hv
        F.mapIso (liftedIso (R := R) f p g W V e u hu v hv) = a ≪≫ b.symm := by
  intro r X₀ i Y₀ Z₀ F P Q U V T e u hu v hv a b
  let FF : F.FullyFaithful :=
    closedFiberPullbackFullyFaithful (R := R) (X := X) (Z := Z) f g
  apply Iso.ext
  exact comparisonPreimageIso_map F FF (U u) (U v) T a b

/-- A lift is determined by its restriction to the original closed fiber. -/
theorem liftedIso_unique :
    let r : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶
        Spec (CommRingCat.of R) :=
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
    let X₀ : Scheme.{u} := Limits.pullback f r
    let i : X₀ ⟶ X := Limits.pullback.fst f r
    let Y₀ : Scheme.{u} := Limits.pullback p i
    let Z₀ : Scheme.{u} := Limits.pullback g i
    let F : FiniteEtale Z ⥤ FiniteEtale Z₀ :=
      FiniteEtale.pullback (Limits.pullback.fst g i)
    let P : FiniteEtale Y ⥤ FiniteEtale Y₀ :=
      FiniteEtale.pullback (Limits.pullback.fst p i)
    let Q : FiniteEtale X₀ ⥤ FiniteEtale Y₀ :=
      FiniteEtale.pullback (Limits.pullback.snd p i)
    let U : (Z ⟶ Y) → FiniteEtale Z := fun u => (FiniteEtale.pullback u).obj W
    ∀ V : FiniteEtale X₀,
      let T : FiniteEtale Z₀ := (FiniteEtale.pullback (Limits.pullback.snd g i)).obj V
      ∀ (e : P.obj W ≅ Q.obj V)
        (u : Z ⟶ Y) (hu : u ≫ p = g) (v : Z ⟶ Y) (hv : v ≫ p = g),
        let a : F.obj (U u) ≅ T :=
          restrictionIso (X := X) (X₀ := X₀) (Y := Y) (Z := Z) i p g W V e u hu
        let b : F.obj (U v) ≅ T :=
          restrictionIso (X := X) (X₀ := X₀) (Y := Y) (Z := Z) i p g W V e v hv
        ∀ c : U u ≅ U v, F.map c.hom = a.hom ≫ b.inv →
          c = liftedIso (R := R) f p g W V e u hu v hv := by
  intro r X₀ i Y₀ Z₀ F P Q U V T e u hu v hv a b c hc
  let FF : F.FullyFaithful :=
    closedFiberPullbackFullyFaithful (R := R) (X := X) (Z := Z) f g
  apply Iso.ext
  apply FF.map_injective
  exact hc.trans (comparisonPreimageIso_map F FF (U u) (U v) T a b).symm

/-- Comparing a pullback with itself gives its identity isomorphism. -/
theorem liftedIso_refl :
    let r : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶
        Spec (CommRingCat.of R) :=
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
    let X₀ : Scheme.{u} := Limits.pullback f r
    let i : X₀ ⟶ X := Limits.pullback.fst f r
    let Y₀ : Scheme.{u} := Limits.pullback p i
    let P : FiniteEtale Y ⥤ FiniteEtale Y₀ :=
      FiniteEtale.pullback (Limits.pullback.fst p i)
    let Q : FiniteEtale X₀ ⥤ FiniteEtale Y₀ :=
      FiniteEtale.pullback (Limits.pullback.snd p i)
    let U : (Z ⟶ Y) → FiniteEtale Z := fun u => (FiniteEtale.pullback u).obj W
    ∀ (V : FiniteEtale X₀) (e : P.obj W ≅ Q.obj V)
      (u : Z ⟶ Y) (hu : u ≫ p = g),
      liftedIso (R := R) f p g W V e u hu u hu = Iso.refl (U u) := by
  intro r X₀ i Y₀ P Q U V e u hu
  let Z₀ : Scheme.{u} := Limits.pullback g i
  let F : FiniteEtale Z ⥤ FiniteEtale Z₀ :=
    FiniteEtale.pullback (Limits.pullback.fst g i)
  let FF : F.FullyFaithful :=
    closedFiberPullbackFullyFaithful (R := R) (X := X) (Z := Z) f g
  let T : FiniteEtale Z₀ := (FiniteEtale.pullback (Limits.pullback.snd g i)).obj V
  let a : F.obj (U u) ≅ T :=
    restrictionIso (X := X) (X₀ := X₀) (Y := Y) (Z := Z) i p g W V e u hu
  exact comparisonPreimageIso_refl F FF (U u) T a

/-- Three comparisons on the same proper scheme satisfy the composition
law by faithfulness of the actual closed-fiber restriction. -/
theorem liftedIso_trans :
    let r : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶
        Spec (CommRingCat.of R) :=
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
    let X₀ : Scheme.{u} := Limits.pullback f r
    let i : X₀ ⟶ X := Limits.pullback.fst f r
    let Y₀ : Scheme.{u} := Limits.pullback p i
    let P : FiniteEtale Y ⥤ FiniteEtale Y₀ :=
      FiniteEtale.pullback (Limits.pullback.fst p i)
    let Q : FiniteEtale X₀ ⥤ FiniteEtale Y₀ :=
      FiniteEtale.pullback (Limits.pullback.snd p i)
    ∀ (V : FiniteEtale X₀) (e : P.obj W ≅ Q.obj V)
      (u : Z ⟶ Y) (hu : u ≫ p = g) (v : Z ⟶ Y) (hv : v ≫ p = g)
      (w : Z ⟶ Y) (hw : w ≫ p = g),
      liftedIso (R := R) f p g W V e u hu v hv ≪≫
          liftedIso (R := R) f p g W V e v hv w hw =
        liftedIso (R := R) f p g W V e u hu w hw := by
  intro r X₀ i Y₀ P Q V e u hu v hv w hw
  let U : (Z ⟶ Y) → FiniteEtale Z := fun u => (FiniteEtale.pullback u).obj W
  let Z₀ : Scheme.{u} := Limits.pullback g i
  let F : FiniteEtale Z ⥤ FiniteEtale Z₀ :=
    FiniteEtale.pullback (Limits.pullback.fst g i)
  let FF : F.FullyFaithful :=
    closedFiberPullbackFullyFaithful (R := R) (X := X) (Z := Z) f g
  let T : FiniteEtale Z₀ := (FiniteEtale.pullback (Limits.pullback.snd g i)).obj V
  let a : F.obj (U u) ≅ T :=
    restrictionIso (X := X) (X₀ := X₀) (Y := Y) (Z := Z) i p g W V e u hu
  let b : F.obj (U v) ≅ T :=
    restrictionIso (X := X) (X₀ := X₀) (Y := Y) (Z := Z) i p g W V e v hv
  let c : F.obj (U w) ≅ T :=
    restrictionIso (X := X) (X₀ := X₀) (Y := Y) (Z := Z) i p g W V e w hw
  exact comparisonPreimageIso_trans F FF (U u) (U v) (U w) T a b c

end Proper

section DoubleOverlap

variable {R : Type u} [CommRing R] [HenselianLocalRing R]
  {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
  (p : Y ⟶ X) [IsProper p] (W : FiniteEtale Y)

/-- The two restrictions of the actual cover to the double overlap are
isomorphic, using proper henselian full faithfulness on that overlap. -/
def doubleOverlapIso :
    let r : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶
        Spec (CommRingCat.of R) :=
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
    let X₀ : Scheme.{u} := Limits.pullback f r
    let i : X₀ ⟶ X := Limits.pullback.fst f r
    let Y₀ : Scheme.{u} := Limits.pullback p i
    let P : FiniteEtale Y ⥤ FiniteEtale Y₀ :=
      FiniteEtale.pullback (Limits.pullback.fst p i)
    let Q : FiniteEtale X₀ ⥤ FiniteEtale Y₀ :=
      FiniteEtale.pullback (Limits.pullback.snd p i)
    ∀ (V : FiniteEtale X₀) (_e : P.obj W ≅ Q.obj V),
      (FiniteEtale.pullback (Limits.pullback.fst p p)).obj W ≅
        (FiniteEtale.pullback (Limits.pullback.snd p p)).obj W := by
  intro r X₀ i Y₀ P Q V e
  exact liftedIso (R := R) (X := X) (Y := Y) (Z := Limits.pullback p p)
    f p (Limits.pullback.fst p p ≫ p) W V e
    (Limits.pullback.fst p p) rfl (Limits.pullback.snd p p)
    Limits.pullback.condition.symm

/-- The double-overlap map recovers the comparison formed from the original
closed-fiber isomorphism and the original closed-fiber cover. -/
theorem doubleOverlapIso_restrict :
    let r : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶
        Spec (CommRingCat.of R) :=
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
    let X₀ : Scheme.{u} := Limits.pullback f r
    let i : X₀ ⟶ X := Limits.pullback.fst f r
    let Y₀ : Scheme.{u} := Limits.pullback p i
    let D : Scheme.{u} := Limits.pullback p p
    let g : D ⟶ X := Limits.pullback.fst p p ≫ p
    let Z₀ : Scheme.{u} := Limits.pullback g i
    let F : FiniteEtale D ⥤ FiniteEtale Z₀ :=
      FiniteEtale.pullback (Limits.pullback.fst g i)
    let P : FiniteEtale Y ⥤ FiniteEtale Y₀ :=
      FiniteEtale.pullback (Limits.pullback.fst p i)
    let Q : FiniteEtale X₀ ⥤ FiniteEtale Y₀ :=
      FiniteEtale.pullback (Limits.pullback.snd p i)
    let U : (D ⟶ Y) → FiniteEtale D := fun u => (FiniteEtale.pullback u).obj W
    ∀ V : FiniteEtale X₀,
      let T : FiniteEtale Z₀ := (FiniteEtale.pullback (Limits.pullback.snd g i)).obj V
      ∀ e : P.obj W ≅ Q.obj V,
        let a : F.obj (U (Limits.pullback.fst p p)) ≅ T :=
          restrictionIso (X := X) (X₀ := X₀) (Y := Y) (Z := D) i p g W V e
            (Limits.pullback.fst p p) rfl
        let b : F.obj (U (Limits.pullback.snd p p)) ≅ T :=
          restrictionIso (X := X) (X₀ := X₀) (Y := Y) (Z := D) i p g W V e
            (Limits.pullback.snd p p) Limits.pullback.condition.symm
        F.mapIso (doubleOverlapIso (R := R) f p W V e) = a ≪≫ b.symm := by
  intro r X₀ i Y₀ D g Z₀ F P Q U V T e a b
  exact liftedIso_restrict (R := R) (X := X) (Y := Y) (Z := D) f p g W V e
    (Limits.pullback.fst p p) rfl (Limits.pullback.snd p p)
    Limits.pullback.condition.symm

end DoubleOverlap

end AlgebraicGeometry.FiniteEtale.ProperHenselianActionLifting
