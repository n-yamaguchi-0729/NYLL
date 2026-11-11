/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.FiniteEtale.BaseChange.PullbackIdentity
public import Mathlib.AlgebraicGeometry.RelativeGluing
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic

/-!
# Gluing local extensions of one finite étale cover

Full faithfulness of restriction constructs the unique transition maps
between local extensions. Their uniqueness proves identity and composition.
The resulting cartesian diagram glues by relative scheme gluing, and its
chart over the original open recovers the original finite étale cover.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FiniteEtale

universe u

attribute [local instance] finiteEtaleOverCategoryCoherence
  finiteEtaleHasPullbacksAlongCoherence finiteEtaleStableUnderBaseChangeAlongCoherence

private theorem hom_ext_of_cartesian_restriction
    {U N : Scheme.{u}} (r : U ⟶ N) (FF : (pullback r).FullyFaithful)
    (A B : FiniteEtale N) {T : Scheme.{u}} (q : T ⟶ U) (j : T ⟶ A.left)
    (hj : IsPullback j q A.hom r) (a b : A ⟶ B)
    (h : j ≫ a.left = j ≫ b.left) : a = b := by
  let A₀ : Scheme := A.left
  let B₀ : Scheme := B.left
  let fA : A₀ ⟶ N := A.hom
  let fB : B₀ ⟶ N := B.hom
  let a₀ : A₀ ⟶ B₀ := a.left
  let b₀ : A₀ ⟶ B₀ := b.left
  let a₁ : Limits.pullback fA r ⟶ Limits.pullback fB r := ((pullback r).map a).left
  let b₁ : Limits.pullback fA r ⟶ Limits.pullback fB r := ((pullback r).map b).left
  let e : T ≅ Limits.pullback fA r := hj.isoPullback
  have he : e.hom ≫ Limits.pullback.fst fA r = j := hj.isoPullback_hom_fst
  have ha : a₁ ≫ Limits.pullback.fst fB r = Limits.pullback.fst fA r ≫ a₀ :=
    Limits.pullback.lift_fst _ _ _
  have hb : b₁ ≫ Limits.pullback.fst fB r = Limits.pullback.fst fA r ≫ b₀ :=
    Limits.pullback.lift_fst _ _ _
  have has : a₁ ≫ Limits.pullback.snd fB r = Limits.pullback.snd fA r :=
    Limits.pullback.lift_snd _ _ _
  have hbs : b₁ ≫ Limits.pullback.snd fB r = Limits.pullback.snd fA r :=
    Limits.pullback.lift_snd _ _ _
  apply FF.map_injective
  apply MorphismProperty.Over.Hom.ext
  change a₁ = b₁
  apply (cancel_epi e.hom).mp
  apply Limits.pullback.hom_ext
  · rw [Category.assoc, ha, ← Category.assoc, he,
      Category.assoc, hb, ← Category.assoc, he]
    exact h
  · rw [Category.assoc, has, Category.assoc, hbs]

/-- The transition between two actual local extensions is constructed
from full faithfulness. Its Cartesian square and its uniqueness retain
the specified maps from the original cover. -/
theorem exists_unique_cartesian_extension_map
    {U N M : Scheme.{u}} (r : U ⟶ N) (v : N ⟶ M) (s : U ⟶ M)
    (hrs : r ≫ v = s) (FF : (pullback r).FullyFaithful)
    (A : FiniteEtale N) (B : FiniteEtale M)
    {T : Scheme.{u}} (q : T ⟶ U) (i : T ⟶ A.left) (j : T ⟶ B.left)
    (hi : IsPullback i q A.hom r) (hj : IsPullback j q B.hom s) :
    ∃ h : A.left ⟶ B.left,
      IsPullback h A.hom B.hom v ∧ i ≫ h = j ∧
      ∀ k : A.left ⟶ B.left,
        k ≫ B.hom = A.hom ≫ v → i ≫ k = j → k = h := by
  let A₀ : Scheme := A.left
  let B₀ : Scheme := B.left
  let fA : A₀ ⟶ N := A.hom
  let fB : B₀ ⟶ M := B.hom
  let C₀ : Scheme := Limits.pullback fB v
  let fC : C₀ ⟶ N := Limits.pullback.snd fB v
  let C : FiniteEtale N := (pullback v).obj B
  have hiw : i ≫ fA = q ≫ r := hi.w
  have hjw : j ≫ fB = q ≫ s := hj.w
  let j' : T ⟶ C₀ := Limits.pullback.lift j (q ≫ r)
    (by rw [hjw, ← hrs, Category.assoc])
  have hj'snd : j' ≫ fC = q ≫ r := Limits.pullback.lift_snd _ _ _
  have hj'fst : j' ≫ Limits.pullback.fst fB v = j :=
    Limits.pullback.lift_fst _ _ _
  have hj' : IsPullback j' q fC r := by
    apply IsPullback.of_right _ hj'snd (IsPullback.of_hasPullback fB v)
    rw [hj'fst, hrs]
    exact hj
  let ei : T ≅ Limits.pullback fA r := hi.isoPullback
  let ej : T ≅ Limits.pullback fC r := hj'.isoPullback
  have hei : ei.hom ≫ Limits.pullback.fst fA r = i := hi.isoPullback_hom_fst
  have heis : ei.inv ≫ q = Limits.pullback.snd fA r := hi.isoPullback_inv_snd
  have hej : ej.hom ≫ Limits.pullback.fst fC r = j' := hj'.isoPullback_hom_fst
  have hejs : ej.hom ≫ Limits.pullback.snd fC r = q := hj'.isoPullback_hom_snd
  let e₀ : Limits.pullback fA r ≅ Limits.pullback fC r := ei.symm ≪≫ ej
  have he₀ : e₀.hom ≫ Limits.pullback.snd fC r = Limits.pullback.snd fA r := by
    change (ei.inv ≫ ej.hom) ≫ Limits.pullback.snd fC r = _
    rw [Category.assoc, hejs, heis]
  let e : (pullback r).obj A ≅ (pullback r).obj C :=
    MorphismProperty.Over.isoMk e₀ he₀
  let a : A ≅ C := FF.preimageIso e
  have ha : (pullback r).map a.hom = e.hom := FF.map_preimage e.hom
  let a₀ : A₀ ≅ C₀ := (FiniteEtale.forget N ⋙ Over.forget N).mapIso a
  let a₁ : Limits.pullback fA r ⟶ Limits.pullback fC r := ((pullback r).map a.hom).left
  have ha₁ : a₁ = e₀.hom := congrArg
    (fun z : (pullback r).obj A ⟶ (pullback r).obj C =>
      (z.left : Limits.pullback fA r ⟶ Limits.pullback fC r)) ha
  have hmap : a₁ ≫ Limits.pullback.fst fC r =
      Limits.pullback.fst fA r ≫ a₀.hom := Limits.pullback.lift_fst _ _ _
  have haw : a₀.hom ≫ fC = fA := a.hom.w
  have hia : i ≫ a₀.hom = j' := by
    calc
      i ≫ a₀.hom = ei.hom ≫ a₁ ≫ Limits.pullback.fst fC r := by
        rw [hmap, ← Category.assoc, hei]
      _ = ei.hom ≫ e₀.hom ≫ Limits.pullback.fst fC r := by rw [ha₁]
      _ = j' := by
        change ei.hom ≫ (ei.inv ≫ ej.hom) ≫ Limits.pullback.fst fC r = j'
        rw [Category.assoc, Iso.hom_inv_id_assoc, hej]
  let h : A₀ ⟶ B₀ := a₀.hom ≫ Limits.pullback.fst fB v
  have hh : IsPullback h fA fB v := by
    apply IsPullback.of_iso_pullback _ a₀ rfl haw
    constructor
    change (a₀.hom ≫ Limits.pullback.fst fB v) ≫ fB = fA ≫ v
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, haw]
  have hih : i ≫ h = j := by
    change i ≫ (a₀.hom ≫ Limits.pullback.fst fB v) = j
    rw [← Category.assoc, hia, hj'fst]
  refine ⟨h, hh, hih, fun k hk hki => ?_⟩
  let k₀ : A₀ ⟶ C₀ := Limits.pullback.lift k fA hk
  have hkfst : k₀ ≫ Limits.pullback.fst fB v = k := Limits.pullback.lift_fst _ _ _
  have hksnd : k₀ ≫ fC = fA := Limits.pullback.lift_snd _ _ _
  let k' : A ⟶ C := MorphismProperty.Over.homMk k₀ hksnd
  have hik : i ≫ k₀ = j' := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, hkfst, hki, hj'fst]
    · rw [Category.assoc, hksnd, hiw, hj'snd]
  have heq : k' = a.hom :=
    hom_ext_of_cartesian_restriction r FF A C q i hi k' a.hom (hik.trans hia.symm)
  have heq₀ : k₀ = a₀.hom := congrArg (fun z : A ⟶ C => (z.left : A₀ ⟶ C₀)) heq
  calc
    k = k₀ ≫ Limits.pullback.fst fB v := hkfst.symm
    _ = a₀.hom ≫ Limits.pullback.fst fB v := by rw [heq₀]
    _ = h := rfl

/-- Local actual extensions on opens containing the original open glue
globally. Full faithfulness constructs their Cartesian transition maps
and proves their compatibility; no descent datum is an additional input. -/
theorem exists_extension_of_locally_exists_of_restriction_fullyFaithful
    {X : Scheme.{u}} (U : X.Opens) (Y : FiniteEtale U.toScheme)
    (FF : ∀ (N : X.Opens) (hUN : U ≤ N),
      (pullback (X.homOfLE hUN)).FullyFaithful)
    (hlocal : ∀ z : X, ∃ (N : X.Opens) (hUN : U ≤ N), z ∈ N ∧
      ∃ Z : FiniteEtale N.toScheme,
        Nonempty ((pullback (X.homOfLE hUN)).obj Z ≅ Y)) :
    ∃ Z : FiniteEtale X, Nonempty ((pullback U.ι).obj Z ≅ Y) := by
  let P (N : X.Opens) : Prop := ∃ (hUN : U ≤ N) (Z : FiniteEtale N.toScheme),
    Nonempty ((pullback (X.homOfLE hUN)).obj Z ≅ Y)
  have hU : P U := by
    refine ⟨le_rfl, Y, ⟨?_⟩⟩
    rw [Scheme.homOfLE_rfl]
    exact (pullbackIdIso U.toScheme).app Y
  have hrestrict (N M : X.Opens) (hN : P N) (hUM : U ≤ M) (hMN : M ≤ N) : P M := by
    obtain ⟨hUN, Z, ⟨e⟩⟩ := hN
    let c : pullback (X.homOfLE hUN) ≅
        pullback (X.homOfLE hMN) ⋙ pullback (X.homOfLE hUM) :=
      MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
        (X.homOfLE hUM) (X.homOfLE hMN) (X.homOfLE hUN)
        (X.homOfLE_homOfLE hUM hMN).symm
    exact ⟨hUM, (pullback (X.homOfLE hMN)).obj Z, ⟨(c.app Z).symm ≪≫ e⟩⟩
  let J : Type u := {N : X.Opens // P N}
  have hmodels : ∀ i : J, ∃ (hUN : U ≤ i.1) (Z : FiniteEtale i.1.toScheme),
      Nonempty ((pullback (X.homOfLE hUN)).obj Z ≅ Y) := fun i => i.2
  choose hUN W he using hmodels
  let e (i : J) : (pullback (X.homOfLE (hUN i))).obj (W i) ≅ Y :=
    Classical.choice (he i)
  let 𝒰 : X.OpenCover :=
    { I₀ := J
      X := fun i => i.1.toScheme
      f := fun i => i.1.ι
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨fun z => ?_, fun i => inferInstance⟩
        obtain ⟨N, hUN, hz, Z, hZ⟩ := hlocal z
        exact ⟨⟨N, ⟨hUN, Z, hZ⟩⟩, ⟨z, hz⟩, rfl⟩ }
  let hDirected : 𝒰.LocallyDirected :=
    { trans := fun {i j} hij => X.homOfLE (leOfHom hij)
      trans_id := fun i => X.homOfLE_rfl i.1
      trans_comp := fun hij hjk =>
        (X.homOfLE_homOfLE (leOfHom hij) (leOfHom hjk)).symm
      w := fun hij => X.homOfLE_ι (leOfHom hij)
      directed := by
        intro i j x
        let k : J := ⟨i.1 ⊓ j.1,
          hrestrict i.1 (i.1 ⊓ j.1) i.2 (le_inf (hUN i) (hUN j)) inf_le_left⟩
        let hp := isPullback_opens_inf i.1 j.1
        have hki : k ≤ i := (inf_le_left : i.1 ⊓ j.1 ≤ i.1)
        have hkj : k ≤ j := (inf_le_right : i.1 ⊓ j.1 ≤ j.1)
        refine ⟨k, homOfLE hki, homOfLE hkj, hp.isoPullback.inv x, ?_⟩
        have hlift : Limits.pullback.lift
            (X.homOfLE (inf_le_left : i.1 ⊓ j.1 ≤ i.1))
            (X.homOfLE (inf_le_right : i.1 ⊓ j.1 ≤ j.1)) hp.w =
              hp.isoPullback.hom := by
          apply Limits.pullback.hom_ext
          · rw [Limits.pullback.lift_fst, hp.isoPullback_hom_fst]
          · rw [Limits.pullback.lift_snd, hp.isoPullback_hom_snd]
        change (Limits.pullback.lift
          (X.homOfLE (inf_le_left : i.1 ⊓ j.1 ≤ i.1))
          (X.homOfLE (inf_le_right : i.1 ⊓ j.1 ≤ j.1)) _) (hp.isoPullback.inv x) = x
        rw [hlift, ← Scheme.Hom.comp_apply, Iso.inv_hom_id]
        rfl }
  let qY : Y.left ⟶ U.toScheme := Y.hom
  let p (i : J) : (W i).left ⟶ i.1.toScheme := (W i).hom
  let e₀ (i : J) : Y.left ≅ Limits.pullback (p i) (X.homOfLE (hUN i)) :=
    (FiniteEtale.forget U.toScheme ⋙ Over.forget U.toScheme).mapIso (e i).symm
  have he₀ (i : J) : (e₀ i).hom ≫ Limits.pullback.snd (p i) (X.homOfLE (hUN i)) = qY :=
    (e i).inv.w
  let y (i : J) : Y.left ⟶ (W i).left :=
    (e₀ i).hom ≫ Limits.pullback.fst (p i) (X.homOfLE (hUN i))
  have hy (i : J) : IsPullback (y i) qY (p i) (X.homOfLE (hUN i)) := by
    apply IsPullback.of_iso_pullback _ (e₀ i) rfl (he₀ i)
    constructor
    change ((e₀ i).hom ≫ Limits.pullback.fst (p i) (X.homOfLE (hUN i))) ≫ p i =
      qY ≫ X.homOfLE (hUN i)
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, he₀ i]
  have hmaps (i j : J) (hij : i ⟶ j) :
      ∃ t : (W i).left ⟶ (W j).left,
        IsPullback t (p i) (p j) (X.homOfLE (leOfHom hij)) ∧
        y i ≫ t = y j ∧
        ∀ k : (W i).left ⟶ (W j).left,
          k ≫ p j = p i ≫ X.homOfLE (leOfHom hij) →
          y i ≫ k = y j → k = t :=
    exists_unique_cartesian_extension_map (X.homOfLE (hUN i))
      (X.homOfLE (leOfHom hij)) (X.homOfLE (hUN j))
      (X.homOfLE_homOfLE (hUN i) (leOfHom hij)) (FF i.1 (hUN i))
      (W i) (W j) qY (y i) (y j) (hy i) (hy j)
  let t {i j : J} (hij : i ⟶ j) : (W i).left ⟶ (W j).left :=
    Classical.choose (hmaps i j hij)
  have ht {i j : J} (hij : i ⟶ j) :
      IsPullback (t hij) (p i) (p j) (X.homOfLE (leOfHom hij)) :=
    (Classical.choose_spec (hmaps i j hij)).1
  have hty {i j : J} (hij : i ⟶ j) : y i ≫ t hij = y j :=
    (Classical.choose_spec (hmaps i j hij)).2.1
  have htunique {i j : J} (hij : i ⟶ j) (k : (W i).left ⟶ (W j).left)
      (hk : k ≫ p j = p i ≫ X.homOfLE (leOfHom hij))
      (hky : y i ≫ k = y j) : k = t hij :=
    (Classical.choose_spec (hmaps i j hij)).2.2 k hk hky
  let D : J ⥤ Scheme.{u} :=
    { obj := fun i => (W i).left
      map := fun hij => t hij
      map_id := fun i => by
        symm
        apply htunique (𝟙 i) (𝟙 (W i).left)
        · rw [Category.id_comp, Scheme.homOfLE_rfl, Category.comp_id]
        · exact Category.comp_id _
      map_comp := fun hij hjk => by
        symm
        apply htunique (hij ≫ hjk) (t hij ≫ t hjk)
        · rw [Category.assoc, (ht hjk).w, ← Category.assoc, (ht hij).w,
            Category.assoc, X.homOfLE_homOfLE]
        · rw [← Category.assoc, hty hij, hty hjk] }
  let d : 𝒰.RelativeGluingData :=
    { functor := D
      natTrans :=
        { app := fun i => p i
          naturality := fun _ _ hij => (ht hij).w }
      equifibered := fun _ _ hij => ht hij }
  have hLocal : IsZariskiLocalAtTarget (@IsFiniteEtale : MorphismProperty Scheme.{u}) :=
    ((HasAffineProperty.iff
      (P := (@IsFiniteEtale : MorphismProperty Scheme.{u}))
      (Q := affineAnd RingHom.FiniteEtale)).mp inferInstance).1
  let : MorphismProperty.RespectsIso (@IsFiniteEtale : MorphismProperty Scheme.{u}) :=
    hLocal.toRespects
  have hFinite : IsFiniteEtale d.toBase := by
    apply IsZariskiLocalAtTarget.of_openCover (P := @IsFiniteEtale) 𝒰
    intro i
    change IsFiniteEtale (Limits.pullback.snd d.toBase (𝒰.f i))
    let ei := (d.isPullback_natTrans_ι_toBase i).flip.isoPullback
    have hei : ei.hom ≫ Limits.pullback.snd d.toBase (𝒰.f i) = p i :=
      (d.isPullback_natTrans_ι_toBase i).flip.isoPullback_hom_snd
    apply (MorphismProperty.cancel_left_of_respectsIso
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) ei.hom
      (Limits.pullback.snd d.toBase (𝒰.f i))).mp
    exact hei.symm ▸ (W i).prop
  let Z : FiniteEtale X := FiniteEtale.mk d.toBase
  let iU : J := ⟨U, hU⟩
  let er : (pullback U.ι).obj Z ≅ W iU :=
    MorphismProperty.Over.isoMk (d.isPullback_natTrans_ι_toBase iU).flip.isoPullback.symm
      (d.isPullback_natTrans_ι_toBase iU).flip.isoPullback_inv_snd
  have eU : (pullback (𝟙 U.toScheme)).obj (W iU) ≅ Y := by
    simpa only [Scheme.homOfLE_rfl] using e iU
  exact ⟨Z, ⟨er ≪≫ ((pullbackIdIso U.toScheme).app (W iU)).symm ≪≫ eU⟩⟩

end AlgebraicGeometry.FiniteEtale
