/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Sites.SetSheafFunctors
public import Nyll.EtaleCohomology.Sites.SetPullbackComposition
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Sites.Limits

/-!
# The actual equalizer sheaf of an étale descent overlap

Starting with a sheaf and its specified overlap isomorphism, construct the
two adjoint arrows and their equalizer downstairs. The counit gives the
actual comparison from its inverse image to the original sheaf. Its
compatibility with the specified overlap follows from the equalizer
condition and the existing inverse-image composition isomorphisms.

The construction needs neither properness nor the cocycle condition;
these are needed later to prove the comparison is an isomorphism. No
comparison isomorphism or effective-descent assertion is supplied here.

Reference: Stacks Project, Section 59.104 (0GEX), the equalizer construction
in Lemma 59.104.2 also used for proper descent in Lemma 59.104.3.
https://stacks.math.columbia.edu/tag/0GEX
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace EtaleCohomology.SetSheafDescent

/-- A composite comparison together with cancellation of its first isomorphism. -/
structure IsoWithCancellation
    {C : Type*} [Category C] {A B E H : C}
    (e₁ : A ≅ B) (e : A ≅ E) (e₂ : E ≅ H) where
  /-- The comparison between the remaining endpoints. -/
  iso : B ≅ H
  /-- Composing with the first isomorphism gives the other two comparisons. -/
  condition : e₁.hom ≫ iso.hom = e.hom ≫ e₂.hom

/-- Compose the inverse of the first isomorphism with the two remaining comparisons. -/
def isoWithCancellation
    {C : Type*} [Category C] {A B E H : C}
    (e₁ : A ≅ B) (e : A ≅ E) (e₂ : E ≅ H) : IsoWithCancellation e₁ e e₂ where
  iso := e₁.symm ≪≫ e ≪≫ e₂
  condition := by
    change e₁.hom ≫ e₁.inv ≫ (e.hom ≫ e₂.hom) = e.hom ≫ e₂.hom
    exact e₁.hom_inv_id_assoc _

variable {X Y : Scheme.{u}} (q : Y ⟶ X)

/-- The original overlap comparison with its composition cancellation identity. -/
def overlapComparisonData :
    IsoWithCancellation (etaleSetPullbackCompIso (pullback.fst q q) q)
      (eqToIso (congrArg (fun f => etaleSetPullback f)
        (pullback.condition (f := q) (g := q))))
      (etaleSetPullbackCompIso (pullback.snd q q) q) :=
  isoWithCancellation (etaleSetPullbackCompIso (pullback.fst q q) q)
    (eqToIso (congrArg (fun f => etaleSetPullback f)
      (pullback.condition (f := q) (g := q))))
    (etaleSetPullbackCompIso (pullback.snd q q) q)

/-- The two inverse images from the original base to its actual double
overlap agree by the pullback square and native composition comparisons. -/
def overlapComparison :
    etaleSetPullback q ⋙ etaleSetPullback (pullback.fst q q) ≅
      etaleSetPullback q ⋙ etaleSetPullback (pullback.snd q q) :=
  (overlapComparisonData q).iso

/-- The original overlap comparison retains the cancellation equation
of its defining three original isomorphisms. -/
theorem overlapComparison_hom_cancellation :
    (etaleSetPullbackCompIso (pullback.fst q q) q).hom ≫ (overlapComparison q).hom =
      (eqToIso (congrArg (fun f => etaleSetPullback f)
        (pullback.condition (f := q) (g := q)))).hom ≫
          (etaleSetPullbackCompIso (pullback.snd q q) q).hom :=
  (overlapComparisonData q).condition

variable (F : Sheaf Y.smallEtaleTopology (Type u))

/-- The first matching arrow is the transpose of inverse image of the
original counit along the first overlap projection. -/
def firstArrow :
    (etaleSetPushforward q).obj F ⟶
      (etaleSetPushforward q).obj
        ((etaleSetPushforward (pullback.fst q q)).obj
          ((etaleSetPullback (pullback.fst q q)).obj F)) :=
  ((etaleSetPullbackPushforwardAdjunction q).comp
    (etaleSetPullbackPushforwardAdjunction (pullback.fst q q))).homEquiv _ _
      ((etaleSetPullback (pullback.fst q q)).map
        ((etaleSetPullbackPushforwardAdjunction q).counit.app F))

variable (θ : (etaleSetPullback (pullback.fst q q)).obj F ≅
  (etaleSetPullback (pullback.snd q q)).obj F)

/-- The second matching arrow uses the second projection and the inverse
of the specified original overlap isomorphism. -/
def secondArrow :
    (etaleSetPushforward q).obj F ⟶
      (etaleSetPushforward q).obj
        ((etaleSetPushforward (pullback.fst q q)).obj
          ((etaleSetPullback (pullback.fst q q)).obj F)) :=
  ((etaleSetPullbackPushforwardAdjunction q).comp
    (etaleSetPullbackPushforwardAdjunction (pullback.fst q q))).homEquiv _ _
      ((overlapComparison q).hom.app ((etaleSetPushforward q).obj F) ≫
        (etaleSetPullback (pullback.snd q q)).map
          ((etaleSetPullbackPushforwardAdjunction q).counit.app F) ≫ θ.inv)

/-- The actual sheaf of matching sections downstairs. -/
def matchingSheaf : Sheaf X.smallEtaleTopology (Type u) :=
  equalizer (firstArrow q F) (secondArrow q F θ)

/-- Its actual inclusion into direct image of the original sheaf. -/
def inclusion : matchingSheaf q F θ ⟶ (etaleSetPushforward q).obj F :=
  equalizer.ι (firstArrow q F) (secondArrow q F θ)

/-- The canonical comparison from inverse image of the constructed
matching sheaf to the original sheaf. -/
def comparison : (etaleSetPullback q).obj (matchingSheaf q F θ) ⟶ F :=
  (etaleSetPullback q).map (inclusion q F θ) ≫
    (etaleSetPullbackPushforwardAdjunction q).counit.app F

/-- An arrow into direct image equalizes the two actual matching arrows
exactly when its adjoint comparison respects the original overlap. -/
theorem equalizes_iff {G : Sheaf X.smallEtaleTopology (Type u)}
    (b : G ⟶ (etaleSetPushforward q).obj F) :
    b ≫ firstArrow q F = b ≫ secondArrow q F θ ↔
      (etaleSetPullback (pullback.fst q q)).map
          ((etaleSetPullback q).map b ≫
            (etaleSetPullbackPushforwardAdjunction q).counit.app F) =
        (overlapComparison q).hom.app G ≫
          (etaleSetPullback (pullback.snd q q)).map
            ((etaleSetPullback q).map b ≫
              (etaleSetPullbackPushforwardAdjunction q).counit.app F) ≫ θ.inv := by
  let adj := (etaleSetPullbackPushforwardAdjunction q).comp
    (etaleSetPullbackPushforwardAdjunction (pullback.fst q q))
  rw [← (adj.homEquiv G
    ((etaleSetPullback (pullback.fst q q)).obj F)).symm.injective.eq_iff]
  simp only [adj, firstArrow, secondArrow, Adjunction.homEquiv_naturality_left_symm,
    Equiv.symm_apply_apply, Functor.map_comp]
  change
    (etaleSetPullback q ⋙ etaleSetPullback (pullback.fst q q)).map b ≫
        (etaleSetPullback (pullback.fst q q)).map
          ((etaleSetPullbackPushforwardAdjunction q).counit.app F) =
      (etaleSetPullback q ⋙ etaleSetPullback (pullback.fst q q)).map b ≫
        (overlapComparison q).hom.app ((etaleSetPushforward q).obj F) ≫
          (etaleSetPullback (pullback.snd q q)).map
            ((etaleSetPullbackPushforwardAdjunction q).counit.app F) ≫ θ.inv ↔ _
  rw [← Category.assoc _ ((overlapComparison q).hom.app _) _,
    (overlapComparison q).hom.naturality, Category.assoc]
  simp only [Functor.comp_map, Category.assoc]

/-- The comparison of the actual equalizer sheaf recovers the specified
overlap action. This is an equality of the original sheaf morphisms. -/
theorem comparison_overlap :
    (etaleSetPullback (pullback.fst q q)).map (comparison q F θ) ≫ θ.hom =
      (overlapComparison q).hom.app (matchingSheaf q F θ) ≫
        (etaleSetPullback (pullback.snd q q)).map (comparison q F θ) := by
  have h := (equalizes_iff q F θ (inclusion q F θ)).mp
    (equalizer.condition (firstArrow q F) (secondArrow q F θ))
  change (etaleSetPullback (pullback.fst q q)).map (comparison q F θ) =
    (overlapComparison q).hom.app (matchingSheaf q F θ) ≫
      (etaleSetPullback (pullback.snd q q)).map (comparison q F θ) ≫ θ.inv at h
  rw [h, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Every original overlap-compatible arrow is represented by a unique
arrow to the actual equalizer sheaf downstairs. -/
theorem existsUnique_lift
    {G : Sheaf X.smallEtaleTopology (Type u)}
    (a : (etaleSetPullback q).obj G ⟶ F)
    (ha : (etaleSetPullback (pullback.fst q q)).map a ≫ θ.hom =
      (overlapComparison q).hom.app G ≫
        (etaleSetPullback (pullback.snd q q)).map a) :
    ∃! b : G ⟶ matchingSheaf q F θ,
      (etaleSetPullback q).map b ≫ comparison q F θ = a := by
  let adj := etaleSetPullbackPushforwardAdjunction q
  let a' : G ⟶ (etaleSetPushforward q).obj F := adj.homEquiv G F a
  have htranspose : (etaleSetPullback q).map a' ≫ adj.counit.app F = a := by
    exact (adj.homEquiv G F).symm_apply_apply a
  have heq : a' ≫ firstArrow q F = a' ≫ secondArrow q F θ := by
    apply (equalizes_iff q F θ a').mpr
    rw [htranspose]
    exact (cancel_mono θ.hom).mp (by
      rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      exact ha)
  let b : G ⟶ matchingSheaf q F θ := equalizer.lift a' heq
  have hb : b ≫ inclusion q F θ = a' := equalizer.lift_ι a' heq
  refine ⟨b, ?_, ?_⟩
  · change (etaleSetPullback q).map b ≫ comparison q F θ = a
    rw [comparison, ← Category.assoc, ← Functor.map_comp, hb]
    exact htranspose
  · intro c hc
    apply equalizer.hom_ext
    change c ≫ inclusion q F θ = b ≫ inclusion q F θ
    rw [hb]
    apply (adj.homEquiv G F).symm.injective
    rw [adj.homEquiv_counit, Functor.map_comp, Category.assoc]
    change (etaleSetPullback q).map c ≫ comparison q F θ =
      (adj.homEquiv G F).symm a'
    rw [hc]
    exact ((adj.homEquiv G F).symm_apply_apply a).symm

end EtaleCohomology.SetSheafDescent
