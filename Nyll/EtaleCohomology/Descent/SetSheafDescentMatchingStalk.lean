/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Descent.SetSheafDescentEqualizer
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Sites.Point.Basic

/-!
# The original matching equalizer on actual stalks

A point's existing fiber functor preserves finite limits. The standard
preserved-equalizer comparison and standard Type equalizer identify the
stalk of the original matching sheaf with the original matching elements.
The comparison retains the image of the original equalizer inclusion.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace EtaleCohomology.SetSheafDescent

variable {X Y : Scheme.{u}} (q : Y ⟶ X)
  (F : Sheaf Y.smallEtaleTopology (Type u))
  (θ : (etaleSetPullback (pullback.fst q q)).obj F ≅
    (etaleSetPullback (pullback.snd q q)).obj F)
  (Φ : GrothendieckTopology.Point.{u} X.smallEtaleTopology)

/-- The original matching sheaf has exactly the original matching
stalk elements; the map is the actual stalk of its given inclusion. -/
theorem matchingSheaf_stalk_existsUnique
    (a : Φ.sheafFiber.obj ((etaleSetPushforward q).obj F))
    (ha : Φ.sheafFiber.map (firstArrow q F) a =
      Φ.sheafFiber.map (secondArrow q F θ) a) :
    ∃! b : Φ.sheafFiber.obj (matchingSheaf q F θ),
      Φ.sheafFiber.map (inclusion q F θ) b = a :=
  Types.unique_of_type_equalizer
    (Φ.sheafFiber.map (equalizer.ι (firstArrow q F) (secondArrow q F θ)))
    (by rw [← Functor.map_comp, ← Functor.map_comp, equalizer.condition])
    (isLimitOfHasEqualizerOfPreservesLimit Φ.sheafFiber
      (firstArrow q F) (secondArrow q F θ)) a ha

/-- The standard equalizer comparison identifies the original matching
stalk with the subtype defined by the two original matching arrows. -/
def matchingSheafStalkIso :
    Φ.sheafFiber.obj (matchingSheaf q F θ) ≅
      {a : Φ.sheafFiber.obj ((etaleSetPushforward q).obj F) //
        Φ.sheafFiber.map (firstArrow q F) a =
          Φ.sheafFiber.map (secondArrow q F θ) a} :=
  PreservesEqualizer.iso Φ.sheafFiber (firstArrow q F) (secondArrow q F θ) ≪≫
    Types.equalizerIso (Φ.sheafFiber.map (firstArrow q F))
      (Φ.sheafFiber.map (secondArrow q F θ))

/-- Forgetting the matching equation gives precisely the stalk of the
original inclusion, rather than a chosen identification of its image. -/
theorem matchingSheafStalkIso_hom_val :
    (matchingSheafStalkIso q F θ Φ).hom ≫ TypeCat.ofHom Subtype.val =
      Φ.sheafFiber.map (inclusion q F θ) := by
  let e := PreservesEqualizer.iso Φ.sheafFiber (firstArrow q F) (secondArrow q F θ)
  let d := Types.equalizerIso (Φ.sheafFiber.map (firstArrow q F))
    (Φ.sheafFiber.map (secondArrow q F θ))
  let v := TypeCat.ofHom (Subtype.val :
    {a : Φ.sheafFiber.obj ((etaleSetPushforward q).obj F) //
      Φ.sheafFiber.map (firstArrow q F) a =
        Φ.sheafFiber.map (secondArrow q F θ) a} → _)
  have hd : d.hom ≫ v = equalizer.ι (Φ.sheafFiber.map (firstArrow q F))
      (Φ.sheafFiber.map (secondArrow q F θ)) :=
    Types.equalizerIso_hom_comp_subtype _ _
  have he : e.hom ≫ equalizer.ι (Φ.sheafFiber.map (firstArrow q F))
      (Φ.sheafFiber.map (secondArrow q F θ)) = Φ.sheafFiber.map (inclusion q F θ) :=
    equalizerComparison_comp_π _ _ _
  change (e.hom ≫ d.hom) ≫ v = _
  exact (Category.assoc e.hom d.hom v).trans
    ((congrArg (fun k => e.hom ≫ k) hd).trans he)

end EtaleCohomology.SetSheafDescent
