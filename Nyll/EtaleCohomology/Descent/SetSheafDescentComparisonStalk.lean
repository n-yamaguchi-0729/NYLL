/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Descent.SetSheafDescentEqualizer
public import Nyll.EtaleCohomology.Sites.PullbackUnitGeometricStalks
public import Nyll.EtaleCohomology.Sites.PushforwardStalkComparison

/-!
# The original descent comparison on geometric stalks

The original adjunction unit and direct-image component carry the actual
descent comparison to restriction of the actual matching-sheaf inclusion.
The unit-component map is already known to be invertible for every scheme
morphism, so the latter map detects invertibility of the original comparison
on each geometric stalk.
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
  {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (CommRingCat.of Ω) ⟶ Y)

/-- The actual descent counit comparison becomes the original matching
inclusion followed by the actual direct-image stalk component. -/
theorem comparison_stalkComponent :
    ((Scheme.pointSmallEtale (s ≫ q)).sheafFiber.map
        ((etaleSetPullbackPushforwardAdjunction q).unit.app (matchingSheaf q F θ)) ≫
      etalePushforwardStalkComponent q (s ≫ q) ⟨s, rfl⟩
        ((etaleSetPullback q).obj (matchingSheaf q F θ))) ≫
        (Scheme.pointSmallEtale s).sheafFiber.map (comparison q F θ) =
      (Scheme.pointSmallEtale (s ≫ q)).sheafFiber.map (inclusion q F θ) ≫
        etalePushforwardStalkComponent q (s ≫ q) ⟨s, rfl⟩ F := by
  let Φ := Scheme.pointSmallEtale (s ≫ q)
  let Ψ := Scheme.pointSmallEtale s
  let H := matchingSheaf q F θ
  let a := comparison q F θ
  let i := inclusion q F θ
  let adj := etaleSetPullbackPushforwardAdjunction q
  have ht : adj.unit.app H ≫ (etaleSetPushforward q).map a = i :=
    (adj.unit_comp_map_eq_iff a i).mpr rfl
  have hn : Φ.sheafFiber.map ((etaleSetPushforward q).map a) ≫
      etalePushforwardStalkComponent q (s ≫ q) ⟨s, rfl⟩ F =
    etalePushforwardStalkComponent q (s ≫ q) ⟨s, rfl⟩ ((etaleSetPullback q).obj H) ≫
      Ψ.sheafFiber.map a :=
    etalePushforwardStalkComponent_naturality q (s ≫ q) ⟨s, rfl⟩ a
  have hm : Φ.sheafFiber.map (adj.unit.app H) ≫
      Φ.sheafFiber.map ((etaleSetPushforward q).map a) = Φ.sheafFiber.map i :=
    (Φ.sheafFiber.map_comp _ _).symm.trans (congrArg Φ.sheafFiber.map ht)
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => Φ.sheafFiber.map (adj.unit.app H) ≫ k) hn.symm).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun k => k ≫ etalePushforwardStalkComponent q (s ≫ q) ⟨s, rfl⟩ F) hm)))

/-- Invertibility of the original comparison at a geometric point is
exactly invertibility of the actual matching inclusion restricted to that
point. This uses the existing inverse-image unit stalk isomorphism. -/
theorem comparison_stalk_isIso_iff :
    IsIso ((Scheme.pointSmallEtale s).sheafFiber.map (comparison q F θ)) ↔
      IsIso ((Scheme.pointSmallEtale (s ≫ q)).sheafFiber.map (inclusion q F θ) ≫
        etalePushforwardStalkComponent q (s ≫ q) ⟨s, rfl⟩ F) := by
  let k := (Scheme.pointSmallEtale (s ≫ q)).sheafFiber.map
      ((etaleSetPullbackPushforwardAdjunction q).unit.app (matchingSheaf q F θ)) ≫
    etalePushforwardStalkComponent q (s ≫ q) ⟨s, rfl⟩
      ((etaleSetPullback q).obj (matchingSheaf q F θ))
  have hk : IsIso k := etalePullbackUnit_stalkComponent_isIso_generic q s (Type u)
    (etaleSetPullback q) (etaleSetPullbackPushforwardAdjunction q) (matchingSheaf q F θ)
  rw [← comparison_stalkComponent q F θ s]
  exact (isIso_comp_left_iff k
    ((Scheme.pointSmallEtale s).sheafFiber.map (comparison q F θ))).symm

end EtaleCohomology.SetSheafDescent
