/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalk
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Functoriality of the actual geometric stalk

A commuting square of field-valued points and scheme morphisms induces a
local ring map on the existing pointed étale colimits. Each neighborhood is
pulled back along the scheme morphism, with the point obtained from the
given field embedding. Descent of the maps on sections constructs the map;
the identity and composition laws follow from actual morphisms between
these pointed pullbacks.

The fields need not be separably closed. In particular this construction
applies to geometric points and to the strict local schemes used in
Stacks Project, Section 58.16, https://stacks.math.columbia.edu/tag/0BUP.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleFundamentalGroups.StrictHenselian

universe u

local instance (X : Scheme.{u}) :
    Category (MorphismProperty.Over (@Etale : MorphismProperty Scheme.{u}) ⊤ X) :=
  inferInstanceAs (Category X.Etale)

local instance {X Y : Scheme.{u}} (p : X ⟶ Y) :
    MorphismProperty.HasPullbacksAlong (@Etale : MorphismProperty Scheme.{u}) p :=
  ⟨fun _ _ => inferInstance⟩

local instance {X Y : Scheme.{u}} (p : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@Etale : MorphismProperty Scheme.{u}) p :=
  ⟨fun h hf => MorphismProperty.of_isPullback (P := @Etale) h hf⟩

variable {S T : Scheme.{u}} {Ω Ψ : Type u} [Field Ω] [Field Ψ]
  (f : S ⟶ T) (s : Spec (.of Ω) ⟶ S) (t : Spec (.of Ψ) ⟶ T)
  (ι : Ψ →+* Ω) (h : s ≫ f = Spec.map (CommRingCat.ofHom ι) ≫ t)

/-- The given field-valued point on an étale neighborhood lifts to its
actual pullback along the scheme morphism. -/
def pointedEtalePullback (W : T.Etale)
    (w : (Scheme.pointEtaleNeighborhoods t).fiber.obj W) :
    (Scheme.pointEtaleNeighborhoods s).fiber.obj
      ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W) := by
  let p : W.left ⟶ T := W.hom
  let wHom : Spec (.of Ψ) ⟶ W.left := w.left
  let i : Spec (.of Ω) ⟶ Spec (.of Ψ) := Spec.map (CommRingCat.ofHom ι)
  have hw : wHom ≫ p = t := Over.w w
  have hcomm : (i ≫ wHom) ≫ p = s ≫ f :=
    (Category.assoc i wHom p).trans
      ((congrArg (fun a : Spec (.of Ψ) ⟶ T => i ≫ a) hw).trans h.symm)
  change Over.mk s ⟶ Over.mk (pullback.snd p f)
  exact Over.homMk (pullback.lift (i ≫ wHom) s hcomm)
    (pullback.lift_snd _ _ _)

/-- Pointed pullback respects the maps between the original neighborhoods. -/
theorem pointedEtalePullback_naturality {W V : T.Etale} (g : W ⟶ V)
    (w : (Scheme.pointEtaleNeighborhoods t).fiber.obj W) :
    (Scheme.pointEtaleNeighborhoods s).fiber.map
        ((MorphismProperty.Over.pullback @Etale ⊤ f).map g)
        (pointedEtalePullback f s t ι h W w) =
      pointedEtalePullback f s t ι h V
        ((Scheme.pointEtaleNeighborhoods t).fiber.map g w) := by
  let P : S.Etale := (MorphismProperty.Over.pullback @Etale ⊤ f).obj W
  let Q : S.Etale := (MorphismProperty.Over.pullback @Etale ⊤ f).obj V
  let a : Spec (.of Ω) ⟶ P.left := (pointedEtalePullback f s t ι h W w).left
  let b : Spec (.of Ω) ⟶ Q.left :=
    (pointedEtalePullback f s t ι h V ((Scheme.pointEtaleNeighborhoods t).fiber.map g w)).left
  let q : P.left ⟶ Q.left := ((MorphismProperty.Over.pullback @Etale ⊤ f).map g).left
  let pW : P.left ⟶ W.left := pullback.fst W.hom f
  let pV : Q.left ⟶ V.left := pullback.fst V.hom f
  let rW : P.left ⟶ S := pullback.snd W.hom f
  let rV : Q.left ⟶ S := pullback.snd V.hom f
  let m : W.left ⟶ V.left := g.left
  let i : Spec (.of Ω) ⟶ Spec (.of Ψ) := Spec.map (CommRingCat.ofHom ι)
  let wHom : Spec (.of Ψ) ⟶ W.left := w.left
  have ha : a ≫ pW = i ≫ wHom := pullback.lift_fst _ _ _
  have hb : b ≫ pV = i ≫ (wHom ≫ m) := pullback.lift_fst _ _ _
  have hq : q ≫ pV = pW ≫ m := pullback.lift_fst _ _ _
  have ha' : a ≫ rW = s := pullback.lift_snd _ _ _
  have hb' : b ≫ rV = s := pullback.lift_snd _ _ _
  have hq' : q ≫ rV = rW := pullback.lift_snd _ _ _
  apply Over.OverMorphism.ext
  change a ≫ q = b
  apply pullback.hom_ext
  · change (a ≫ q) ≫ pV = b ≫ pV
    rw [Category.assoc, hq, ← Category.assoc, ha, Category.assoc, hb]
  · change (a ≫ q) ≫ rV = b ≫ rV
    rw [Category.assoc, hq', ha', hb']

private theorem geometricStalkPullbackCocone_naturality
    {W V : T.Etale} (g : W ⟶ V)
    (w : (Scheme.pointEtaleNeighborhoods t).fiber.obj W) :
    g.left.appTop ≫ (pullback.fst W.hom f).appTop ≫
        geometricStalkGerm s ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W)
          (pointedEtalePullback f s t ι h W w) =
      (pullback.fst V.hom f).appTop ≫
        geometricStalkGerm s ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V)
          (pointedEtalePullback f s t ι h V
            ((Scheme.pointEtaleNeighborhoods t).fiber.map g w)) := by
  let q := (MorphismProperty.Over.pullback @Etale ⊤ f).map g
  have hq : q.left ≫ pullback.fst V.hom f = pullback.fst W.hom f ≫ g.left :=
    pullback.lift_fst _ _ _
  have hγ := (Scheme.pointEtaleNeighborhoods s).toPresheafFiber_w q
    (pointedEtalePullback f s t ι h W w) (etaleSections S)
  change q.left.appTop ≫ geometricStalkGerm s _ _ = geometricStalkGerm s _ _ at hγ
  rw [pointedEtalePullback_naturality] at hγ
  let pW : ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W).left ⟶ W.left :=
    pullback.fst W.hom f
  let pV : ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V).left ⟶ V.left :=
    pullback.fst V.hom f
  let qHom : ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W).left ⟶
      ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V).left := q.left
  let m : W.left ⟶ V.left := g.left
  let γW : Γ(((MorphismProperty.Over.pullback @Etale ⊤ f).obj W).left, ⊤) ⟶
      geometricStalk s := geometricStalkGerm s _ (pointedEtalePullback f s t ι h W w)
  let γV : Γ(((MorphismProperty.Over.pullback @Etale ⊤ f).obj V).left, ⊤) ⟶
      geometricStalk s := geometricStalkGerm s _ (pointedEtalePullback f s t ι h V
        ((Scheme.pointEtaleNeighborhoods t).fiber.map g w))
  have hqHom : qHom ≫ pV = pW ≫ m := hq
  have hγHom : qHom.appTop ≫ γW = γV := hγ
  change m.appTop ≫ pW.appTop ≫ γW = pV.appTop ≫ γV
  rw [← Category.assoc, ← Scheme.Hom.comp_appTop, ← hqHom,
    Scheme.Hom.comp_appTop, Category.assoc, hγHom]

/-- A commuting square of field-valued points induces a map on their actual
pointed étale colimits, contravariantly in the underlying schemes. -/
def geometricStalkMap : geometricStalk t ⟶ geometricStalk s :=
  (Scheme.pointEtaleNeighborhoods t).presheafFiberDesc
    (fun W w => (pullback.fst W.hom f).appTop ≫
      geometricStalkGerm s ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W)
        (pointedEtalePullback f s t ι h W w))
    (fun _ _ g w => geometricStalkPullbackCocone_naturality f s t ι h g w)

/-- The induced map sends a represented germ to the section pulled back on
the actual pointed fiber product. -/
theorem geometricStalkGerm_map (W : T.Etale)
    (w : (Scheme.pointEtaleNeighborhoods t).fiber.obj W) :
    geometricStalkGerm t W w ≫ geometricStalkMap f s t ι h =
      (pullback.fst W.hom f).appTop ≫
        geometricStalkGerm s ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W)
          (pointedEtalePullback f s t ι h W w) :=
  (Scheme.pointEtaleNeighborhoods t).toPresheafFiber_presheafFiberDesc _ _ W w

/-- The map of stalks has exactly the prescribed effect on evaluation in
the two pointing fields. -/
theorem geometricStalkMap_evaluation :
    geometricStalkMap f s t ι h ≫ geometricStalkEvaluation s =
      geometricStalkEvaluation t ≫ CommRingCat.ofHom ι := by
  apply (Scheme.pointEtaleNeighborhoods t).presheafFiber_hom_ext
  intro W w
  let P : S.Etale := (MorphismProperty.Over.pullback @Etale ⊤ f).obj W
  let wp := pointedEtalePullback f s t ι h W w
  let p : P.left ⟶ W.left := pullback.fst W.hom f
  let a : Spec (.of Ω) ⟶ P.left := wp.left
  let wHom : Spec (.of Ψ) ⟶ W.left := w.left
  let i : Spec (.of Ω) ⟶ Spec (.of Ψ) := Spec.map (CommRingCat.ofHom ι)
  let γW : Γ(W.left, ⊤) ⟶ geometricStalk t := geometricStalkGerm t W w
  let γP : Γ(P.left, ⊤) ⟶ geometricStalk s := geometricStalkGerm s P wp
  let M : geometricStalk t ⟶ geometricStalk s := geometricStalkMap f s t ι h
  let εS : geometricStalk s ⟶ CommRingCat.of Ω := geometricStalkEvaluation s
  let εT : geometricStalk t ⟶ CommRingCat.of Ψ := geometricStalkEvaluation t
  let eΩ : Γ(Spec (.of Ω), ⊤) ⟶ CommRingCat.of Ω :=
    (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom
  let eΨ : Γ(Spec (.of Ψ), ⊤) ⟶ CommRingCat.of Ψ :=
    (Scheme.ΓSpecIso (CommRingCat.of Ψ)).hom
  have hMap : γW ≫ M = p.appTop ≫ γP := geometricStalkGerm_map f s t ι h W w
  have hEvalP : γP ≫ εS = a.appTop ≫ eΩ := geometricStalkGerm_evaluation s P wp
  have hEvalW : γW ≫ εT = wHom.appTop ≫ eΨ := geometricStalkGerm_evaluation t W w
  have ha : a ≫ p = i ≫ wHom := pullback.lift_fst _ _ _
  have hNat : i.appTop ≫ eΩ = eΨ ≫ CommRingCat.ofHom ι :=
    Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ι)
  change γW ≫ M ≫ εS = γW ≫ εT ≫ CommRingCat.ofHom ι
  rw [← Category.assoc, hMap, Category.assoc, hEvalP, ← Category.assoc,
    ← Scheme.Hom.comp_appTop, ha, Scheme.Hom.comp_appTop, Category.assoc,
    hNat, ← Category.assoc, ← hEvalW, Category.assoc]

/-- The induced ring map is local. This follows from the explicit
evaluation square and the unit criterion in the constructed stalks. -/
instance geometricStalkMap_isLocalHom : IsLocalHom (geometricStalkMap f s t ι h).hom where
  map_nonunit a ha := by
    apply geometricStalk_isUnit_of_evaluation_ne_zero t a
    intro hzero
    apply (ha.map (geometricStalkEvaluation s).hom).ne_zero
    have he := ConcreteCategory.congr_hom (geometricStalkMap_evaluation f s t ι h) a
    change geometricStalkEvaluation s (geometricStalkMap f s t ι h a) =
      ι (geometricStalkEvaluation t a) at he
    rw [he, hzero, map_zero]

/-- Pullback along the identity square gives the identity on the existing
geometric stalk. -/
theorem geometricStalkMap_id :
    geometricStalkMap (𝟙 S) s s (RingHom.id Ω)
      (by
        change s ≫ 𝟙 S = Spec.map (𝟙 (CommRingCat.of Ω)) ≫ s
        rw [Spec.map_id, Category.comp_id, Category.id_comp]) =
        𝟙 (geometricStalk s) := by
  have hId : s ≫ 𝟙 S = Spec.map (CommRingCat.ofHom (RingHom.id Ω)) ≫ s := by
    change s ≫ 𝟙 S = Spec.map (𝟙 (CommRingCat.of Ω)) ≫ s
    rw [Spec.map_id, Category.comp_id, Category.id_comp]
  let M : geometricStalk s ⟶ geometricStalk s :=
    geometricStalkMap (𝟙 S) s s (RingHom.id Ω) hId
  apply (Scheme.pointEtaleNeighborhoods s).presheafFiber_hom_ext
  intro W w
  let P : S.Etale := (MorphismProperty.Over.pullback @Etale ⊤ (𝟙 S)).obj W
  let wp := pointedEtalePullback (𝟙 S) s s (RingHom.id Ω) hId W w
  let p : P.left ⟶ W.left := pullback.fst W.hom (𝟙 S)
  let q : P ⟶ W := MorphismProperty.Over.homMk p
    ((pullback.condition (f := W.hom) (g := 𝟙 S)).trans (Category.comp_id _))
  have hw : (Scheme.pointEtaleNeighborhoods s).fiber.map q wp = w := by
    let a : Spec (.of Ω) ⟶ P.left := wp.left
    let wHom : Spec (.of Ω) ⟶ W.left := w.left
    have ha : a ≫ p = Spec.map (𝟙 (CommRingCat.of Ω)) ≫ wHom := pullback.lift_fst _ _ _
    apply Over.OverMorphism.ext
    change a ≫ p = wHom
    exact ha.trans ((congrArg (fun i : Spec (.of Ω) ⟶ Spec (.of Ω) => i ≫ wHom)
      (Spec.map_id (CommRingCat.of Ω))).trans (Category.id_comp _))
  let γW : Γ(W.left, ⊤) ⟶ geometricStalk s := geometricStalkGerm s W w
  let γP : Γ(P.left, ⊤) ⟶ geometricStalk s := geometricStalkGerm s P wp
  have hγ : p.appTop ≫ γP = γW :=
    ((Scheme.pointEtaleNeighborhoods s).toPresheafFiber_w q wp (etaleSections S)).trans
      (congrArg (geometricStalkGerm s W) hw)
  have hMap : γW ≫ M = p.appTop ≫ γP :=
    geometricStalkGerm_map (𝟙 S) s s (RingHom.id Ω) hId W w
  change γW ≫ M = γW ≫ 𝟙 _
  exact (hMap.trans hγ).trans (Category.comp_id γW).symm

/-- Successive maps of pointed schemes induce the composite of the actual
maps on their geometric stalks. The comparison uses the canonical map from
the iterated pointed fiber product to the single fiber product. -/
theorem geometricStalkMap_comp {V : Scheme.{u}} {Ξ : Type u} [Field Ξ]
    (g : T ⟶ V) (v : Spec (.of Ξ) ⟶ V) (κ : Ξ →+* Ψ)
    (k : t ≫ g = Spec.map (CommRingCat.ofHom κ) ≫ v) :
    geometricStalkMap g t v κ k ≫ geometricStalkMap f s t ι h =
      geometricStalkMap (f ≫ g) s v (ι.comp κ)
        (by rw [← Category.assoc, h, Category.assoc, k, ← Category.assoc,
          ← Spec.map_comp, ← CommRingCat.ofHom_comp]) := by
  apply (Scheme.pointEtaleNeighborhoods v).presheafFiber_hom_ext
  intro W w
  let P : T.Etale := (MorphismProperty.Over.pullback @Etale ⊤ g).obj W
  let wp := pointedEtalePullback g t v κ k W w
  let Q : S.Etale := (MorphismProperty.Over.pullback @Etale ⊤ f).obj P
  let wq := pointedEtalePullback f s t ι h P wp
  let R : S.Etale := (MorphismProperty.Over.pullback @Etale ⊤ (f ≫ g)).obj W
  have hfg : s ≫ (f ≫ g) = Spec.map (CommRingCat.ofHom (ι.comp κ)) ≫ v := by
    rw [← Category.assoc, h, Category.assoc, k, ← Category.assoc,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let wr := pointedEtalePullback (f ≫ g) s v (ι.comp κ) hfg W w
  let pP : Q.left ⟶ P.left := pullback.fst P.hom f
  let pW : P.left ⟶ W.left := pullback.fst W.hom g
  let rQ : Q.left ⟶ S := pullback.snd P.hom f
  let bW : W.left ⟶ V := W.hom
  let bP : P.left ⟶ T := P.hom
  have hP : pW ≫ bW = bP ≫ g := pullback.condition (f := W.hom) (g := g)
  have hQ : pP ≫ bP = rQ ≫ f := pullback.condition (f := P.hom) (g := f)
  have hcomm : (pP ≫ pW) ≫ bW = rQ ≫ (f ≫ g) := by
    rw [Category.assoc, hP, ← Category.assoc, hQ, Category.assoc]
  let q : Q ⟶ R := MorphismProperty.Over.homMk
    (pullback.lift (pP ≫ pW) rQ hcomm)
    (pullback.lift_snd _ _ _)
  let qHom : Q.left ⟶ R.left := q.left
  let pR : R.left ⟶ W.left := pullback.fst W.hom (f ≫ g)
  let rR : R.left ⟶ S := pullback.snd W.hom (f ≫ g)
  have hqfst : qHom ≫ pR = pP ≫ pW := pullback.lift_fst _ _ _
  have hqsnd : qHom ≫ rR = rQ := pullback.lift_snd _ _ _
  have hw : (Scheme.pointEtaleNeighborhoods s).fiber.map q wq = wr := by
    let aP : Spec (.of Ψ) ⟶ P.left := wp.left
    let aQ : Spec (.of Ω) ⟶ Q.left := wq.left
    let aR : Spec (.of Ω) ⟶ R.left := wr.left
    let wHom : Spec (.of Ξ) ⟶ W.left := w.left
    let i : Spec (.of Ω) ⟶ Spec (.of Ψ) := Spec.map (CommRingCat.ofHom ι)
    let j : Spec (.of Ψ) ⟶ Spec (.of Ξ) := Spec.map (CommRingCat.ofHom κ)
    let ij : Spec (.of Ω) ⟶ Spec (.of Ξ) := Spec.map (CommRingCat.ofHom (ι.comp κ))
    have haQ : aQ ≫ pP = i ≫ aP := pullback.lift_fst _ _ _
    have haP : aP ≫ pW = j ≫ wHom := pullback.lift_fst _ _ _
    have haR : aR ≫ pR = ij ≫ wHom := pullback.lift_fst _ _ _
    have haQ' : aQ ≫ rQ = s := pullback.lift_snd _ _ _
    have haR' : aR ≫ rR = s := pullback.lift_snd _ _ _
    have hij : i ≫ j = ij :=
      (Spec.map_comp (CommRingCat.ofHom κ) (CommRingCat.ofHom ι)).symm
    apply Over.OverMorphism.ext
    change aQ ≫ qHom = aR
    apply pullback.hom_ext
    · change (aQ ≫ qHom) ≫ pR = aR ≫ pR
      rw [Category.assoc, hqfst, ← Category.assoc, haQ, Category.assoc,
        haP, ← Category.assoc, hij, haR]
    · change (aQ ≫ qHom) ≫ rR = aR ≫ rR
      rw [Category.assoc, hqsnd, haQ', haR']
  let γW : Γ(W.left, ⊤) ⟶ geometricStalk v := geometricStalkGerm v W w
  let γP : Γ(P.left, ⊤) ⟶ geometricStalk t := geometricStalkGerm t P wp
  let γQ : Γ(Q.left, ⊤) ⟶ geometricStalk s := geometricStalkGerm s Q wq
  let γR : Γ(R.left, ⊤) ⟶ geometricStalk s := geometricStalkGerm s R wr
  let Mg : geometricStalk v ⟶ geometricStalk t := geometricStalkMap g t v κ k
  let Mf : geometricStalk t ⟶ geometricStalk s := geometricStalkMap f s t ι h
  let Mfg : geometricStalk v ⟶ geometricStalk s :=
    geometricStalkMap (f ≫ g) s v (ι.comp κ) hfg
  have hγ : qHom.appTop ≫ γQ = γR :=
    ((Scheme.pointEtaleNeighborhoods s).toPresheafFiber_w q wq (etaleSections S)).trans
      (congrArg (geometricStalkGerm s R) hw)
  have hgermG : γW ≫ Mg = pW.appTop ≫ γP := geometricStalkGerm_map g t v κ k W w
  have hgermF : γP ≫ Mf = pP.appTop ≫ γQ := geometricStalkGerm_map f s t ι h P wp
  have hgermFG : γW ≫ Mfg = pR.appTop ≫ γR :=
    geometricStalkGerm_map (f ≫ g) s v (ι.comp κ) hfg W w
  change γW ≫ Mg ≫ Mf = γW ≫ Mfg
  rw [← Category.assoc, hgermG, Category.assoc, hgermF, hgermFG]
  rw [← Category.assoc, ← Scheme.Hom.comp_appTop, ← hqfst,
    Scheme.Hom.comp_appTop, Category.assoc, hγ]

end EtaleFundamentalGroups.StrictHenselian
