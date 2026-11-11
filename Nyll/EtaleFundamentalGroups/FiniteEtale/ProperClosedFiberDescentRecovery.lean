/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperHenselianActionPullback
public import Nyll.EtaleFundamentalGroups.FiniteEtale.CanonicalDescent

/-!
# Compatibility of the original closed-fiber comparison

The comparison on the restricted cover is obtained from the original
comparison and actual pullback-pasting maps. Its overlap equation follows
from the original restricted overlap equation, evaluated on pullback cones.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.FiniteEtale.ProperHenselianActionLifting

attribute [local instance] finiteEtaleOverCategoryCoherence
  finiteEtaleHasPullbacksAlongCoherence finiteEtaleStableUnderBaseChangeAlongCoherence

variable {X X₀ Y : Scheme.{u}}

/-- The actual comparison between the two pullbacks around the base-change square. -/
def pullbackSquareIso (i : X₀ ⟶ X) (q : Y ⟶ X) (Z : FiniteEtale X) :
    (FiniteEtale.pullback (pullback.snd q i)).obj ((FiniteEtale.pullback i).obj Z) ≅
      (FiniteEtale.pullback (pullback.fst q i)).obj ((FiniteEtale.pullback q).obj Z) :=
  ((MorphismProperty.Over.pullbackComp
    (P := @IsFiniteEtale) (Q := ⊤) (pullback.snd q i) i
      (pullback.fst q i ≫ q) pullback.condition).app Z).symm ≪≫
    (MorphismProperty.Over.pullbackComp
      (P := @IsFiniteEtale) (Q := ⊤) (pullback.fst q i) q).app Z

/-- The square comparison preserves the projection to the original covering scheme. -/
theorem pullbackSquareIso_hom_left_fst_fst
    (i : X₀ ⟶ X) (q : Y ⟶ X) (Z : FiniteEtale X) :
    (pullbackSquareIso i q Z).hom.left ≫
        pullback.fst ((FiniteEtale.pullback q).obj Z).hom (pullback.fst q i) ≫
          pullback.fst Z.hom q =
      pullback.fst ((FiniteEtale.pullback i).obj Z).hom (pullback.snd q i) ≫
        pullback.fst Z.hom i := by
  let z : Z.left ⟶ X := Z.hom
  let j : Limits.pullback q i ⟶ Y := pullback.fst q i
  let q₀ : Limits.pullback q i ⟶ X₀ := pullback.snd q i
  let zq : Limits.pullback z q ⟶ Y := pullback.snd z q
  let zi : Limits.pullback z i ⟶ X₀ := pullback.snd z i
  let A := (MorphismProperty.Over.pullbackComp
    (P := @IsFiniteEtale) (Q := ⊤) q₀ i (j ≫ q) pullback.condition).app Z
  let B := (MorphismProperty.Over.pullbackComp
    (P := @IsFiniteEtale) (Q := ⊤) j q).app Z
  let f : Limits.pullback zi q₀ ⟶ Limits.pullback z (j ≫ q) := A.inv.left
  let g : Limits.pullback z (j ≫ q) ⟶ Limits.pullback zq j := B.hom.left
  let r : Limits.pullback z (j ≫ q) ⟶ Z.left := pullback.fst z (j ≫ q)
  let rz : Limits.pullback z q ⟶ Z.left := pullback.fst z q
  let ri : Limits.pullback z i ⟶ Z.left := pullback.fst z i
  let rq : Limits.pullback zq j ⟶ Limits.pullback z q := pullback.fst zq j
  let r₀ : Limits.pullback zi q₀ ⟶ Limits.pullback z i := pullback.fst zi q₀
  have hg : g ≫ rq ≫ rz = r :=
    pullbackComp_hom_app_left_fst_fst j q (j ≫ q) rfl Z
  have hf : f ≫ r = r₀ ≫ ri :=
    pullbackComp_inv_app_left_fst q₀ i (j ≫ q) pullback.condition Z
  change (f ≫ g) ≫ rq ≫ rz = r₀ ≫ ri
  exact (Category.assoc f g (rq ≫ rz)).trans
    ((congrArg (fun k => f ≫ k) hg).trans hf)

/-- The actual closed-fiber comparison furnished by the descended cover. -/
def closedFiberRecoveryIso (i : X₀ ⟶ X) (q : Y ⟶ X)
    (Z : FiniteEtale X) (W : FiniteEtale Y) (V : FiniteEtale X₀)
    (ρ : (FiniteEtale.pullback q).obj Z ≅ W)
    (e : (FiniteEtale.pullback (pullback.fst q i)).obj W ≅
      (FiniteEtale.pullback (pullback.snd q i)).obj V) :
    (FiniteEtale.pullback (pullback.snd q i)).obj ((FiniteEtale.pullback i).obj Z) ≅
      (FiniteEtale.pullback (pullback.snd q i)).obj V :=
  pullbackSquareIso i q Z ≪≫
    (FiniteEtale.pullback (pullback.fst q i)).mapIso ρ ≪≫ e

/-- Evaluate the original restriction equation on an actual pullback
cone. This retains the specified comparison with the original cover. -/
theorem restrictionIso_overlap_cone
    (i : X₀ ⟶ X) (q : Y ⟶ X) (W : FiniteEtale Y) (V : FiniteEtale X₀)
    (e : (FiniteEtale.pullback (pullback.fst q i)).obj W ≅
      (FiniteEtale.pullback (pullback.snd q i)).obj V)
    (θ : (FiniteEtale.pullback (pullback.fst q q)).obj W ≅
      (FiniteEtale.pullback (pullback.snd q q)).obj W)
    (hθ :
      (FiniteEtale.pullback (pullback.fst (pullback.fst q q ≫ q) i)).map θ.hom ≫
          (restrictionIso i q (pullback.fst q q ≫ q) W V e
            (pullback.snd q q) pullback.condition.symm).hom =
        (restrictionIso i q (pullback.fst q q ≫ q) W V e
          (pullback.fst q q) rfl).hom)
    {T : Scheme.{u}} (t : T ⟶ Limits.pullback (pullback.fst q q ≫ q) i)
    (u : T ⟶ ((FiniteEtale.pullback (pullback.fst q q)).obj W).left)
    (v : T ⟶ ((FiniteEtale.pullback (pullback.snd q q)).obj W).left)
    (hu : u ≫ ((FiniteEtale.pullback (pullback.fst q q)).obj W).hom =
      t ≫ pullback.fst (pullback.fst q q ≫ q) i)
    (hv : v ≫ ((FiniteEtale.pullback (pullback.snd q q)).obj W).hom =
      t ≫ pullback.fst (pullback.fst q q ≫ q) i)
    (huv : u ≫ θ.hom.left = v) :
    (pullback.lift u t hu) ≫
        coverRestrictionLift i q (pullback.fst q q ≫ q) W.hom
          (pullback.fst q q) rfl ≫ e.hom.left ≫
            pullback.fst V.hom (pullback.snd q i) =
      (pullback.lift v t hv) ≫
        coverRestrictionLift i q (pullback.fst q q ≫ q) W.hom
          (pullback.snd q q) pullback.condition.symm ≫ e.hom.left ≫
            pullback.fst V.hom (pullback.snd q i) := by
  let g : Limits.pullback q q ⟶ X := pullback.fst q q ≫ q
  let j : Limits.pullback g i ⟶ Limits.pullback q q := pullback.fst g i
  let a : Limits.pullback q q ⟶ Y := pullback.fst q q
  let b : Limits.pullback q q ⟶ Y := pullback.snd q q
  let w : W.left ⟶ Y := W.hom
  let vbase : V.left ⟶ X₀ := V.hom
  let wa : Limits.pullback w a ⟶ Limits.pullback q q := pullback.snd w a
  let wb : Limits.pullback w b ⟶ Limits.pullback q q := pullback.snd w b
  let u' : T ⟶ Limits.pullback w a := u
  let v' : T ⟶ Limits.pullback w b := v
  let δ : Limits.pullback w a ⟶ Limits.pullback w b := θ.hom.left
  let δ₀ : Limits.pullback wa j ⟶ Limits.pullback wb j :=
    ((FiniteEtale.pullback j).map θ.hom).left
  let ru : Limits.pullback wa j ⟶ Limits.pullback vbase (pullback.snd g i) :=
    (restrictionIso i q g W V e a rfl).hom.left
  let rv : Limits.pullback wb j ⟶ Limits.pullback vbase (pullback.snd g i) :=
    (restrictionIso i q g W V e b pullback.condition.symm).hom.left
  let u₀ : T ⟶ Limits.pullback wa j := pullback.lift u' t hu
  let v₀ : T ⟶ Limits.pullback wb j := pullback.lift v' t hv
  have hδf : δ₀ ≫ pullback.fst wb j = pullback.fst wa j ≫ δ :=
    pullback.lift_fst _ _ _
  have hδs : δ₀ ≫ pullback.snd wb j = pullback.snd wa j :=
    pullback.lift_snd _ _ _
  have huv' : u' ≫ δ = v' := huv
  have hu₀f : u₀ ≫ pullback.fst wa j = u' := pullback.lift_fst _ _ _
  have hv₀f : v₀ ≫ pullback.fst wb j = v' := pullback.lift_fst _ _ _
  have hu₀s : u₀ ≫ pullback.snd wa j = t := pullback.lift_snd _ _ _
  have hv₀s : v₀ ≫ pullback.snd wb j = t := pullback.lift_snd _ _ _
  have huv₀ : u₀ ≫ δ₀ = v₀ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hδf, ← Category.assoc, hu₀f, huv', hv₀f]
    · rw [Category.assoc, hδs, hu₀s, hv₀s]
  have hh : u₀ ≫ ru = v₀ ≫ rv := by
    have he := congrArg (fun k => u₀ ≫ k.left) hθ
    change u₀ ≫ (δ₀ ≫ rv) = u₀ ≫ ru at he
    exact he.symm.trans ((Category.assoc _ _ _).symm.trans
      (congrArg (fun k => k ≫ rv) huv₀))
  let cu := coverRestrictionLift i q g w a rfl
  let cv := coverRestrictionLift i q g w b pullback.condition.symm
  let e₀ : Limits.pullback w (pullback.fst q i) ⟶
      Limits.pullback vbase (pullback.snd q i) := e.hom.left
  let rz : Limits.pullback vbase (pullback.snd g i) ⟶ V.left :=
    pullback.fst vbase (pullback.snd g i)
  let rp : Limits.pullback vbase (pullback.snd q i) ⟶ V.left :=
    pullback.fst vbase (pullback.snd q i)
  have hupr : ru ≫ rz = cu ≫ e₀ ≫ rp :=
    restrictionIso_hom_left_fst i q g a rfl W V e
  have hvpr : rv ≫ rz = cv ≫ e₀ ≫ rp :=
    restrictionIso_hom_left_fst i q g b pullback.condition.symm W V e
  change u₀ ≫ cu ≫ e₀ ≫ rp = v₀ ≫ cv ≫ e₀ ≫ rp
  calc
    _ = u₀ ≫ ru ≫ rz := congrArg (fun k => u₀ ≫ k) hupr.symm
    _ = v₀ ≫ rv ≫ rz := (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ rz) hh).trans (Category.assoc _ _ _))
    _ = _ := congrArg (fun k => v₀ ≫ k) hvpr

/-- Maps to an iterated pullback are determined by the original cover
projection and the outer base projection. -/
private theorem iteratedPullback_hom_ext
    {S T : Scheme.{u}} (q : Y ⟶ X) (Z : FiniteEtale X) (b : T ⟶ Y)
    {f g : S ⟶ ((FiniteEtale.pullback b).obj ((FiniteEtale.pullback q).obj Z)).left}
    (hZ : f ≫ pullback.fst ((FiniteEtale.pullback q).obj Z).hom b ≫
        pullback.fst Z.hom q =
      g ≫ pullback.fst ((FiniteEtale.pullback q).obj Z).hom b ≫ pullback.fst Z.hom q)
    (hT : f ≫ ((FiniteEtale.pullback b).obj ((FiniteEtale.pullback q).obj Z)).hom =
      g ≫ ((FiniteEtale.pullback b).obj ((FiniteEtale.pullback q).obj Z)).hom) : f = g := by
  let z : Z.left ⟶ X := Z.hom
  let w : Limits.pullback z q ⟶ Y := pullback.snd z q
  let rb : Limits.pullback w b ⟶ Limits.pullback z q := pullback.fst w b
  let sb : Limits.pullback w b ⟶ T := pullback.snd w b
  let rz : Limits.pullback z q ⟶ Z.left := pullback.fst z q
  let f₀ : S ⟶ Limits.pullback w b := f
  let g₀ : S ⟶ Limits.pullback w b := g
  have hc : rb ≫ w = sb ≫ b := pullback.condition
  have hz : f₀ ≫ rb ≫ rz = g₀ ≫ rb ≫ rz := hZ
  have ht : f₀ ≫ sb = g₀ ≫ sb := hT
  change f₀ = g₀
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · exact (Category.assoc f₀ rb rz).trans (hz.trans (Category.assoc g₀ rb rz).symm)
    · change (f₀ ≫ rb) ≫ w = (g₀ ≫ rb) ≫ w
      calc
        _ = f₀ ≫ (rb ≫ w) := Category.assoc f₀ rb w
        _ = f₀ ≫ (sb ≫ b) := congrArg (fun k => f₀ ≫ k) hc
        _ = (f₀ ≫ sb) ≫ b := (Category.assoc f₀ sb b).symm
        _ = (g₀ ≫ sb) ≫ b := congrArg (fun k => k ≫ b) ht
        _ = g₀ ≫ (sb ≫ b) := Category.assoc g₀ sb b
        _ = g₀ ≫ (rb ≫ w) := congrArg (fun k => g₀ ≫ k) hc.symm
        _ = _ := (Category.assoc g₀ rb w).symm
  · exact ht

/-- The actual recovery comparison agrees on any two lifts of the same
point of the original restricted covering scheme. All compatibilities
are derived from the native overlap and its original restriction equation. -/
theorem closedFiberRecoveryIso_projection_eq
    (i : X₀ ⟶ X) (q : Y ⟶ X)
    (Z : FiniteEtale X) (W : FiniteEtale Y) (V : FiniteEtale X₀)
    (ρ : (FiniteEtale.pullback q).obj Z ≅ W)
    (e : (FiniteEtale.pullback (pullback.fst q i)).obj W ≅
      (FiniteEtale.pullback (pullback.snd q i)).obj V)
    (θ : (FiniteEtale.pullback (pullback.fst q q)).obj W ≅
      (FiniteEtale.pullback (pullback.snd q q)).obj W)
    (hρ : (FiniteEtale.pullback (pullback.fst q q)).map ρ.hom ≫ θ.hom =
      (canonicalPullbackDescentIso q Z).hom ≫
        (FiniteEtale.pullback (pullback.snd q q)).map ρ.hom)
    (hθ :
      (FiniteEtale.pullback (pullback.fst (pullback.fst q q ≫ q) i)).map θ.hom ≫
          (restrictionIso i q (pullback.fst q q ≫ q) W V e
            (pullback.snd q q) pullback.condition.symm).hom =
        (restrictionIso i q (pullback.fst q q ≫ q) W V e
          (pullback.fst q q) rfl).hom)
    {T : Scheme.{u}}
    (s t : T ⟶ ((FiniteEtale.pullback (pullback.snd q i)).obj
      ((FiniteEtale.pullback i).obj Z)).left)
    (hst : s ≫ pullback.fst ((FiniteEtale.pullback i).obj Z).hom (pullback.snd q i) =
      t ≫ pullback.fst ((FiniteEtale.pullback i).obj Z).hom (pullback.snd q i)) :
    s ≫ (closedFiberRecoveryIso i q Z W V ρ e).hom.left ≫
        pullback.fst V.hom (pullback.snd q i) =
      t ≫ (closedFiberRecoveryIso i q Z W V ρ e).hom.left ≫
        pullback.fst V.hom (pullback.snd q i) := by
  let j : Limits.pullback q i ⟶ Y := pullback.fst q i
  let q₀ : Limits.pullback q i ⟶ X₀ := pullback.snd q i
  let z : Z.left ⟶ X := Z.hom
  let zi : Limits.pullback z i ⟶ X₀ := pullback.snd z i
  let zq : Limits.pullback z q ⟶ Y := pullback.snd z q
  let a₀ : Limits.pullback zi q₀ ⟶ Limits.pullback q i := pullback.snd zi q₀
  let b₀ : Limits.pullback zq j ⟶ Limits.pullback q i := pullback.snd zq j
  let r₀ : Limits.pullback zi q₀ ⟶ Limits.pullback z i := pullback.fst zi q₀
  let ri : Limits.pullback z i ⟶ Z.left := pullback.fst z i
  let rz : Limits.pullback z q ⟶ Z.left := pullback.fst z q
  let rq : Limits.pullback zq j ⟶ Limits.pullback z q := pullback.fst zq j
  let s₀ : T ⟶ Limits.pullback zi q₀ := s
  let t₀ : T ⟶ Limits.pullback zi q₀ := t
  let B := pullbackSquareIso i q Z
  let β : Limits.pullback zi q₀ ⟶ Limits.pullback zq j := B.hom.left
  let ys : T ⟶ Limits.pullback q i := s₀ ≫ a₀
  let yt : T ⟶ Limits.pullback q i := t₀ ≫ a₀
  let zs : T ⟶ Limits.pullback z q := s₀ ≫ β ≫ rq
  let zt : T ⟶ Limits.pullback z q := t₀ ≫ β ≫ rq
  have hc₀ : r₀ ≫ zi = a₀ ≫ q₀ := pullback.condition
  have hcq : rq ≫ zq = b₀ ≫ j := pullback.condition
  have hβ : β ≫ b₀ = a₀ := B.hom.w
  have hβz : β ≫ rq ≫ rz = r₀ ≫ ri := pullbackSquareIso_hom_left_fst_fst i q Z
  have hst₀ : s₀ ≫ r₀ = t₀ ≫ r₀ := hst
  have hys : ys ≫ q₀ = yt ≫ q₀ := by
    change (s₀ ≫ a₀) ≫ q₀ = (t₀ ≫ a₀) ≫ q₀
    calc
      _ = (s₀ ≫ r₀) ≫ zi := (Category.assoc _ _ _).trans
        ((congrArg (fun k => s₀ ≫ k) hc₀.symm).trans (Category.assoc _ _ _).symm)
      _ = (t₀ ≫ r₀) ≫ zi := congrArg (fun k => k ≫ zi) hst₀
      _ = _ := (Category.assoc _ _ _).trans
        ((congrArg (fun k => t₀ ≫ k) hc₀).trans (Category.assoc _ _ _).symm)
  have hbase (v : T ⟶ Limits.pullback zi q₀) :
      (v ≫ β ≫ rq) ≫ zq = (v ≫ a₀) ≫ j := by
    calc
      _ = v ≫ β ≫ (rq ≫ zq) := by simp only [Category.assoc]
      _ = v ≫ β ≫ (b₀ ≫ j) := congrArg (fun k => v ≫ β ≫ k) hcq
      _ = v ≫ (β ≫ b₀) ≫ j := by simp only [Category.assoc]
      _ = v ≫ a₀ ≫ j := congrArg (fun k => v ≫ k ≫ j) hβ
      _ = _ := (Category.assoc _ _ _).symm
  have hzs : zs ≫ zq = ys ≫ j := hbase s₀
  have hzt : zt ≫ zq = yt ≫ j := hbase t₀
  have hzproj (v : T ⟶ Limits.pullback zi q₀) :
      (v ≫ β ≫ rq) ≫ rz = (v ≫ r₀) ≫ ri := by
    calc
      _ = v ≫ (β ≫ rq ≫ rz) := by simp only [Category.assoc]
      _ = v ≫ (r₀ ≫ ri) := congrArg (fun k => v ≫ k) hβz
      _ = _ := (Category.assoc _ _ _).symm
  have hZ : zs ≫ rz = zt ≫ rz := (hzproj s₀).trans
    ((congrArg (fun k => k ≫ ri) hst₀).trans (hzproj t₀).symm)
  have hy : (ys ≫ j) ≫ q = (yt ≫ j) ≫ q := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hys,
      Category.assoc, ← pullback.condition, ← Category.assoc]
  let d : T ⟶ Limits.pullback q q := pullback.lift (ys ≫ j) (yt ≫ j) hy
  let a : Limits.pullback q q ⟶ Y := pullback.fst q q
  let b : Limits.pullback q q ⟶ Y := pullback.snd q q
  have hda : d ≫ a = ys ≫ j := pullback.lift_fst _ _ _
  have hdb : d ≫ b = yt ≫ j := pullback.lift_snd _ _ _
  let ns : T ⟶ Limits.pullback zq a :=
    pullback.lift zs d (hzs.trans hda.symm)
  let nt : T ⟶ Limits.pullback zq b :=
    pullback.lift zt d (hzt.trans hdb.symm)
  have hns : ns ≫ pullback.fst zq a = zs := pullback.lift_fst _ _ _
  have hnt : nt ≫ pullback.fst zq b = zt := pullback.lift_fst _ _ _
  let C := canonicalPullbackDescentIso q Z
  let γ : Limits.pullback zq a ⟶ Limits.pullback zq b := C.hom.left
  have hγ : γ ≫ pullback.fst zq b ≫ rz = pullback.fst zq a ≫ rz :=
    pullbackDescentComparison_hom_left_fst_fst q Z a b pullback.condition
  have hγb : γ ≫ pullback.snd zq b = pullback.snd zq a := C.hom.w
  have hnst : ns ≫ γ = nt := by
    apply iteratedPullback_hom_ext q Z b
    · change (ns ≫ γ) ≫ pullback.fst zq b ≫ rz = nt ≫ pullback.fst zq b ≫ rz
      rw [Category.assoc, hγ, ← Category.assoc, hns, hZ, ← hnt, Category.assoc]
    · change (ns ≫ γ) ≫ pullback.snd zq b = nt ≫ pullback.snd zq b
      rw [Category.assoc, hγb, pullback.lift_snd, pullback.lift_snd]
  let w : W.left ⟶ Y := W.hom
  let ρa : Limits.pullback zq a ⟶ Limits.pullback w a :=
    ((FiniteEtale.pullback a).map ρ.hom).left
  let ρb : Limits.pullback zq b ⟶ Limits.pullback w b :=
    ((FiniteEtale.pullback b).map ρ.hom).left
  let ρj : Limits.pullback zq j ⟶ Limits.pullback w j :=
    ((FiniteEtale.pullback j).map ρ.hom).left
  let δ : Limits.pullback w a ⟶ Limits.pullback w b := θ.hom.left
  let r : Limits.pullback z q ⟶ W.left := ρ.hom.left
  have hρa : ρa ≫ pullback.fst w a = pullback.fst zq a ≫ r :=
    pullback.lift_fst _ _ _
  have hρb : ρb ≫ pullback.fst w b = pullback.fst zq b ≫ r :=
    pullback.lift_fst _ _ _
  have hρj : ρj ≫ pullback.fst w j = rq ≫ r := pullback.lift_fst _ _ _
  have hρas : ρa ≫ pullback.snd w a = pullback.snd zq a :=
    ((FiniteEtale.pullback a).map ρ.hom).w
  have hρbs : ρb ≫ pullback.snd w b = pullback.snd zq b :=
    ((FiniteEtale.pullback b).map ρ.hom).w
  let us : T ⟶ Limits.pullback w a := ns ≫ ρa
  let ut : T ⟶ Limits.pullback w b := nt ≫ ρb
  have hust : us ≫ δ = ut := by
    have hh := congrArg (fun k => ns ≫ k.left) hρ
    change ns ≫ (ρa ≫ δ) = ns ≫ (γ ≫ ρb) at hh
    exact (Category.assoc _ _ _).trans (hh.trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun k => k ≫ ρb) hnst)))
  have hd : d ≫ (a ≫ q) = (ys ≫ q₀) ≫ i := by
    rw [← Category.assoc, hda, Category.assoc,
      pullback.condition, ← Category.assoc]
  let d₀ : T ⟶ Limits.pullback (a ≫ q) i := pullback.lift d (ys ≫ q₀) hd
  have hus : us ≫ pullback.snd w a = d₀ ≫ pullback.fst (a ≫ q) i := by
    change (ns ≫ ρa) ≫ pullback.snd w a = d₀ ≫ pullback.fst (a ≫ q) i
    rw [Category.assoc, hρas, pullback.lift_snd, pullback.lift_fst]
  have hut : ut ≫ pullback.snd w b = d₀ ≫ pullback.fst (a ≫ q) i := by
    change (nt ≫ ρb) ≫ pullback.snd w b = d₀ ≫ pullback.fst (a ≫ q) i
    rw [Category.assoc, hρbs, pullback.lift_snd, pullback.lift_fst]
  let rs : T ⟶ Limits.pullback w j := s₀ ≫ β ≫ ρj
  let rt : T ⟶ Limits.pullback w j := t₀ ≫ β ≫ ρj
  have husf : us ≫ pullback.fst w a = zs ≫ r := by
    change (ns ≫ ρa) ≫ pullback.fst w a = zs ≫ r
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => ns ≫ k) hρa).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ r) hns)))
  have hutf : ut ≫ pullback.fst w b = zt ≫ r := by
    change (nt ≫ ρb) ≫ pullback.fst w b = zt ≫ r
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => nt ≫ k) hρb).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ r) hnt)))
  have hrsf : rs ≫ pullback.fst w j = zs ≫ r := by
    change (s₀ ≫ β ≫ ρj) ≫ pullback.fst w j = (s₀ ≫ β ≫ rq) ≫ r
    simp only [Category.assoc, hρj]
  have hrtf : rt ≫ pullback.fst w j = zt ≫ r := by
    change (t₀ ≫ β ≫ ρj) ≫ pullback.fst w j = (t₀ ≫ β ≫ rq) ≫ r
    simp only [Category.assoc, hρj]
  have hrs : pullback.lift us d₀ hus ≫
      coverRestrictionLift i q (a ≫ q) w a rfl = rs := by
    apply pullback.hom_ext
    · rw [Category.assoc, coverRestrictionLift_fst, ← Category.assoc,
        pullback.lift_fst]
      exact husf.trans hrsf.symm
    · rw [Category.assoc, coverRestrictionLift_snd, ← Category.assoc,
        pullback.lift_snd]
      have hleg : d₀ ≫ restrictionLift i q (a ≫ q) a rfl = ys := by
        apply pullback.hom_ext
        · rw [Category.assoc, restrictionLift_fst, ← Category.assoc,
            pullback.lift_fst, hda]
        · rw [Category.assoc, restrictionLift_snd, pullback.lift_snd]
      rw [hleg]
      have hρj : ρj ≫ pullback.snd w j = b₀ :=
        ((FiniteEtale.pullback j).map ρ.hom).w
      change s₀ ≫ a₀ = (s₀ ≫ β ≫ ρj) ≫ pullback.snd w j
      rw [Category.assoc, Category.assoc, hρj, hβ]
  have hrt : pullback.lift ut d₀ hut ≫
      coverRestrictionLift i q (a ≫ q) w b pullback.condition.symm = rt := by
    apply pullback.hom_ext
    · rw [Category.assoc, coverRestrictionLift_fst, ← Category.assoc,
        pullback.lift_fst]
      exact hutf.trans hrtf.symm
    · rw [Category.assoc, coverRestrictionLift_snd, ← Category.assoc,
        pullback.lift_snd]
      have hleg : d₀ ≫ restrictionLift i q (a ≫ q) b pullback.condition.symm = yt := by
        apply pullback.hom_ext
        · rw [Category.assoc, restrictionLift_fst, ← Category.assoc,
            pullback.lift_fst, hdb]
        · rw [Category.assoc, restrictionLift_snd, pullback.lift_snd, hys]
      rw [hleg]
      have hρj : ρj ≫ pullback.snd w j = b₀ :=
        ((FiniteEtale.pullback j).map ρ.hom).w
      change t₀ ≫ a₀ = (t₀ ≫ β ≫ ρj) ≫ pullback.snd w j
      rw [Category.assoc, Category.assoc, hρj, hβ]
  have he := restrictionIso_overlap_cone i q W V e θ hθ d₀ us ut hus hut hust
  let v : V.left ⟶ X₀ := V.hom
  let e₀ : Limits.pullback w j ⟶ Limits.pullback v q₀ := e.hom.left
  change pullback.lift us d₀ hus ≫
      coverRestrictionLift i q (a ≫ q) w a rfl ≫ e₀ ≫ pullback.fst v q₀ =
    pullback.lift ut d₀ hut ≫
      coverRestrictionLift i q (a ≫ q) w b pullback.condition.symm ≫
        e₀ ≫ pullback.fst v q₀ at he
  rw [← Category.assoc (pullback.lift us d₀ hus), hrs,
    ← Category.assoc (pullback.lift ut d₀ hut), hrt] at he
  change s₀ ≫ ((β ≫ ρj) ≫ e₀) ≫ pullback.fst v q₀ =
    t₀ ≫ ((β ≫ ρj) ≫ e₀) ≫ pullback.fst v q₀
  simpa only [rs, rt, Category.assoc] using he

/-- The recovered comparison on the closed fiber respects the canonical
native descent data of the two original covers. -/
theorem closedFiberRecoveryIso_overlap
    (i : X₀ ⟶ X) (q : Y ⟶ X)
    (Z : FiniteEtale X) (W : FiniteEtale Y) (V : FiniteEtale X₀)
    (ρ : (FiniteEtale.pullback q).obj Z ≅ W)
    (e : (FiniteEtale.pullback (pullback.fst q i)).obj W ≅
      (FiniteEtale.pullback (pullback.snd q i)).obj V)
    (θ : (FiniteEtale.pullback (pullback.fst q q)).obj W ≅
      (FiniteEtale.pullback (pullback.snd q q)).obj W)
    (hρ : (FiniteEtale.pullback (pullback.fst q q)).map ρ.hom ≫ θ.hom =
      (canonicalPullbackDescentIso q Z).hom ≫
        (FiniteEtale.pullback (pullback.snd q q)).map ρ.hom)
    (hθ :
      (FiniteEtale.pullback (pullback.fst (pullback.fst q q ≫ q) i)).map θ.hom ≫
          (restrictionIso i q (pullback.fst q q ≫ q) W V e
            (pullback.snd q q) pullback.condition.symm).hom =
        (restrictionIso i q (pullback.fst q q ≫ q) W V e
          (pullback.fst q q) rfl).hom) :
    let q₀ := pullback.snd q i
    let Z₀ := (FiniteEtale.pullback i).obj Z
    let ρ₀ := closedFiberRecoveryIso i q Z W V ρ e
    (FiniteEtale.pullback (pullback.fst q₀ q₀)).map ρ₀.hom ≫
        (canonicalPullbackDescentIso q₀ V).hom =
      (canonicalPullbackDescentIso q₀ Z₀).hom ≫
        (FiniteEtale.pullback (pullback.snd q₀ q₀)).map ρ₀.hom := by
  intro q₀ Z₀ ρ₀
  let a := pullback.fst q₀ q₀
  let b := pullback.snd q₀ q₀
  let A := (FiniteEtale.pullback q₀).obj Z₀
  let B := (FiniteEtale.pullback q₀).obj V
  let C := canonicalPullbackDescentIso q₀ Z₀
  let D := canonicalPullbackDescentIso q₀ V
  let f := (FiniteEtale.pullback a).map ρ₀.hom ≫ D.hom
  let g := C.hom ≫ (FiniteEtale.pullback b).map ρ₀.hom
  have ha : ((FiniteEtale.pullback a).map ρ₀.hom).left ≫ pullback.fst B.hom a =
      pullback.fst A.hom a ≫ ρ₀.hom.left := pullback.lift_fst _ _ _
  have hb : ((FiniteEtale.pullback b).map ρ₀.hom).left ≫ pullback.fst B.hom b =
      pullback.fst A.hom b ≫ ρ₀.hom.left := pullback.lift_fst _ _ _
  have hC : C.hom.left ≫ pullback.fst A.hom b ≫ pullback.fst Z₀.hom q₀ =
      pullback.fst A.hom a ≫ pullback.fst Z₀.hom q₀ :=
    pullbackDescentComparison_hom_left_fst_fst q₀ Z₀ a b pullback.condition
  have hD : D.hom.left ≫ pullback.fst B.hom b ≫ pullback.fst V.hom q₀ =
      pullback.fst B.hom a ≫ pullback.fst V.hom q₀ :=
    pullbackDescentComparison_hom_left_fst_fst q₀ V a b pullback.condition
  have hst : pullback.fst A.hom a ≫ pullback.fst Z₀.hom q₀ =
      (C.hom.left ≫ pullback.fst A.hom b) ≫ pullback.fst Z₀.hom q₀ := by
    exact hC.symm.trans (Category.assoc _ _ _).symm
  have he := closedFiberRecoveryIso_projection_eq i q Z W V ρ e θ hρ hθ
    (pullback.fst A.hom a) (C.hom.left ≫ pullback.fst A.hom b) hst
  change f = g
  apply MorphismProperty.Over.Hom.ext
  apply iteratedPullback_hom_ext q₀ V b
  · let aw : A.left ⟶ Limits.pullback q i := A.hom
    let bw : B.left ⟶ Limits.pullback q i := B.hom
    let pa : Limits.pullback aw a ⟶ A.left := pullback.fst aw a
    let pb : Limits.pullback aw b ⟶ A.left := pullback.fst aw b
    let qa : Limits.pullback bw a ⟶ B.left := pullback.fst bw a
    let qb : Limits.pullback bw b ⟶ B.left := pullback.fst bw b
    let v : B.left ⟶ V.left := pullback.fst V.hom q₀
    let c : Limits.pullback aw a ⟶ Limits.pullback aw b := C.hom.left
    let d : Limits.pullback bw a ⟶ Limits.pullback bw b := D.hom.left
    let ra : Limits.pullback aw a ⟶ Limits.pullback bw a :=
      ((FiniteEtale.pullback a).map ρ₀.hom).left
    let rb : Limits.pullback aw b ⟶ Limits.pullback bw b :=
      ((FiniteEtale.pullback b).map ρ₀.hom).left
    let r : A.left ⟶ B.left := ρ₀.hom.left
    have hda : d ≫ qb ≫ v = qa ≫ v := hD
    have hra : ra ≫ qa = pa ≫ r := ha
    have hrb : rb ≫ qb = pb ≫ r := hb
    have her : pa ≫ r ≫ v = (c ≫ pb) ≫ r ≫ v := he
    change (ra ≫ d) ≫ qb ≫ v = (c ≫ rb) ≫ qb ≫ v
    calc
      _ = ra ≫ (d ≫ qb ≫ v) := Category.assoc _ _ _
      _ = ra ≫ qa ≫ v := congrArg (fun k => ra ≫ k) hda
      _ = (pa ≫ r) ≫ v := (Category.assoc _ _ _).symm.trans
        (congrArg (fun k => k ≫ v) hra)
      _ = (c ≫ pb) ≫ r ≫ v := (Category.assoc _ _ _).trans her
      _ = c ≫ (pb ≫ r) ≫ v := by simp only [Category.assoc]
      _ = c ≫ (rb ≫ qb) ≫ v := congrArg (fun k => c ≫ k ≫ v) hrb.symm
      _ = _ := by simp only [Category.assoc]
  · exact f.w.trans g.w.symm

end AlgebraicGeometry.FiniteEtale.ProperHenselianActionLifting
