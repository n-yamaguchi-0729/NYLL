/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Descent.SetSheafDescentEqualizer
public import Nyll.EtaleCohomology.Sites.SetSheafFunctors
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Naturality of the actual matching sheaf and its comparison

An actual morphism of the original sheaves commuting with their specified
overlap maps induces a map of the constructed equalizer sheaves. The existing
universal property supplies this map; its comparison and inclusion retain
the original inverse-image and direct-image maps.

An isomorphism of coefficient sheaves therefore gives an isomorphism of
the actual matching sheaves. This permits a finite locally constant
coefficient sheaf to be replaced by an existing representer while preserving
the original descent comparison.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace EtaleCohomology.SetSheafDescent

variable {X Y : Scheme.{u}} (q : Y ⟶ X)
  {F G : Sheaf Y.smallEtaleTopology (Type u)}
  (θ : (etaleSetPullback (pullback.fst q q)).obj F ≅
    (etaleSetPullback (pullback.snd q q)).obj F)
  (ψ : (etaleSetPullback (pullback.fst q q)).obj G ≅
    (etaleSetPullback (pullback.snd q q)).obj G)
  (a : F ⟶ G)
  (ha : (etaleSetPullback (pullback.fst q q)).map a ≫ ψ.hom =
    θ.hom ≫ (etaleSetPullback (pullback.snd q q)).map a)

include ha in
/-- Compatible coefficient maps preserve the matching comparison on overlaps. -/
theorem comparison_postcomp_overlap :
    (etaleSetPullback (pullback.fst q q)).map (comparison q F θ ≫ a) ≫ ψ.hom =
      (overlapComparison q).hom.app (matchingSheaf q F θ) ≫
        (etaleSetPullback (pullback.snd q q)).map (comparison q F θ ≫ a) := by
  rw [Functor.map_comp, Category.assoc, ha, ← Category.assoc,
    comparison_overlap, Category.assoc, ← Functor.map_comp]

/-- A compatible original coefficient map induces a map of the actual
equalizer sheaves by the already proved descent universal property. -/
def map : matchingSheaf q F θ ⟶ matchingSheaf q G ψ :=
  Classical.choose (existsUnique_lift q G ψ (comparison q F θ ≫ a)
    (comparison_postcomp_overlap q θ ψ a ha))

/-- The original comparison is natural for the constructed coefficient map. -/
@[reassoc]
theorem map_comparison :
    (etaleSetPullback q).map (map q θ ψ a ha) ≫ comparison q G ψ =
      comparison q F θ ≫ a :=
  (Classical.choose_spec (existsUnique_lift q G ψ (comparison q F θ ≫ a)
    (comparison_postcomp_overlap q θ ψ a ha))).1

/-- The same map also retains the literal inclusions into the original
direct images; no alternative matching-sheaf model is introduced. -/
@[reassoc]
theorem map_inclusion :
    map q θ ψ a ha ≫ inclusion q G ψ =
      inclusion q F θ ≫ (etaleSetPushforward q).map a := by
  let adj := etaleSetPullbackPushforwardAdjunction q
  apply (adj.homEquiv (matchingSheaf q F θ) G).symm.injective
  rw [adj.homEquiv_counit, adj.homEquiv_counit,
    Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc]
  change (etaleSetPullback q).map (map q θ ψ a ha) ≫ comparison q G ψ =
    (etaleSetPullback q).map (inclusion q F θ) ≫
      (etaleSetPullback q).map ((etaleSetPushforward q).map a) ≫ adj.counit.app G
  have hn : (etaleSetPullback q).map ((etaleSetPushforward q).map a) ≫
      adj.counit.app G = adj.counit.app F ≫ a := adj.counit.naturality a
  rw [hn]
  exact (map_comparison q θ ψ a ha).trans (Category.assoc _ _ _)

variable {q θ ψ a ha}

/-- Inverting a coefficient isomorphism preserves its overlap compatibility. -/
theorem inverse_overlap (e : F ≅ G)
    (he : (etaleSetPullback (pullback.fst q q)).map e.hom ≫ ψ.hom =
      θ.hom ≫ (etaleSetPullback (pullback.snd q q)).map e.hom) :
    (etaleSetPullback (pullback.fst q q)).map e.inv ≫ θ.hom =
      ψ.hom ≫ (etaleSetPullback (pullback.snd q q)).map e.inv := by
  let E₁ := (etaleSetPullback (pullback.fst q q)).mapIso e
  let E₂ := (etaleSetPullback (pullback.snd q q)).mapIso e
  have he' : E₁.hom ≫ ψ.hom = θ.hom ≫ E₂.hom := he
  apply (cancel_epi E₁.hom).mp
  change E₁.hom ≫ (E₁.inv ≫ θ.hom) = E₁.hom ≫ (ψ.hom ≫ E₂.inv)
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, he', Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- A coefficient isomorphism compatible with the specified overlap
induces an isomorphism of the original equalizer sheaves. -/
def mapIso (e : F ≅ G)
    (he : (etaleSetPullback (pullback.fst q q)).map e.hom ≫ ψ.hom =
      θ.hom ≫ (etaleSetPullback (pullback.snd q q)).map e.hom) :
    matchingSheaf q F θ ≅ matchingSheaf q G ψ where
  hom := map q θ ψ e.hom he
  inv := map q ψ θ e.inv (inverse_overlap e he)
  hom_inv_id := by
    apply equalizer.hom_ext
    change (map q θ ψ e.hom he ≫ map q ψ θ e.inv (inverse_overlap e he)) ≫
        inclusion q F θ = (𝟙 (matchingSheaf q F θ)) ≫ inclusion q F θ
    rw [Category.assoc, map_inclusion, ← Category.assoc, map_inclusion,
      Category.assoc, ← Functor.map_comp, e.hom_inv_id,
      CategoryTheory.Functor.map_id,
      Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply equalizer.hom_ext
    change (map q ψ θ e.inv (inverse_overlap e he) ≫ map q θ ψ e.hom he) ≫
        inclusion q G ψ = (𝟙 (matchingSheaf q G ψ)) ≫ inclusion q G ψ
    rw [Category.assoc, map_inclusion, ← Category.assoc, map_inclusion,
      Category.assoc, ← Functor.map_comp, e.inv_hom_id,
      CategoryTheory.Functor.map_id,
      Category.comp_id, Category.id_comp]

/-- The coefficient and matching-sheaf isomorphisms intertwine the
literal comparison maps. This is the actual naturality square. -/
@[reassoc]
theorem mapIso_comparison (e : F ≅ G)
    (he : (etaleSetPullback (pullback.fst q q)).map e.hom ≫ ψ.hom =
      θ.hom ≫ (etaleSetPullback (pullback.snd q q)).map e.hom) :
    (etaleSetPullback q).map (mapIso e he).hom ≫ comparison q G ψ =
      comparison q F θ ≫ e.hom :=
  map_comparison q θ ψ e.hom he

end EtaleCohomology.SetSheafDescent
