/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.FiniteEtale.InverseLimitModel
public import Nyll.SchemeTheory.FiniteEtale.InverseLimitIsomorphism
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Nyll.SchemeTheory.CategoryTheory.FiniteActionGraphs

/-!
# Simultaneous actual models for finitely many finite étale covers

Object descent first gives individual actual stages. A common cofiltered
stage and the native pullback comparison recover every original cover
simultaneously, including the empty family.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory Limits

namespace AlgebraicGeometry.FiniteEtale

/-- Every finite family of covers of an actual qcqs inverse limit has
models at one original stage, with recovery along its actual projection. -/
theorem exists_inverse_limit_models_finite_family
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (h : i ⟶ j), IsAffineHom (D.map h)]
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    {α : Type v} [Finite α] (V : α → FiniteEtale c.pt) :
    ∃ (i : I) (W : α → FiniteEtale (D.obj i)),
      ∀ a : α, Nonempty ((FiniteEtale.pullback (c.π.app i)).obj (W a) ≅ V a) := by
  classical
  have : Fintype α := Fintype.ofFinite α
  choose j M e using fun a : α => exists_inverse_limit_model D c hc (V a)
  obtain ⟨i, hi⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image j)
  have hj (a : α) : Nonempty (i ⟶ j a) :=
    hi (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)
  let h (a : α) : i ⟶ j a := (hj a).some
  refine ⟨i, fun a => (FiniteEtale.pullback (D.map (h a))).obj (M a), ?_⟩
  intro a
  exact ⟨((inverseLimitPullbackComparison D c (h a)).app (M a)).symm ≪≫
    (e a).some⟩


local instance finiteEtaleOverCategoryFiniteAction (X : Scheme.{u}) :
    Category (MorphismProperty.Over
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ X) := instCategory X

local instance finiteEtaleHasPullbacksAlongFiniteAction
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.HasPullbacksAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun _ _ ↦ inferInstance⟩

local instance finiteEtaleStableUnderBaseChangeAlongFiniteAction
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) h hf⟩
/-- A finite family of endomorphisms of an original cover descends at one
common stage. The recovery isomorphism intertwines every original map. -/
theorem exists_inverse_limit_model_endomorphisms
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (h : i ⟶ j), IsAffineHom (D.map h)]
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (W : FiniteEtale c.pt) {α : Type v} [Finite α] (a : α → (W ⟶ W)) :
    ∃ (i : I) (V : FiniteEtale (D.obj i))
      (e : (FiniteEtale.pullback (c.π.app i)).obj V ≅ W)
      (b : α → (V ⟶ V)), ∀ k : α,
      (FiniteEtale.pullback (c.π.app i)).map (b k) ≫ e.hom = e.hom ≫ a k := by
  classical
  let P (s : Finset α) : Prop :=
    ∃ (i : I) (V : FiniteEtale (D.obj i))
      (e : (FiniteEtale.pullback (c.π.app i)).obj V ≅ W)
      (b : α → (V ⟶ V)), ∀ k ∈ s,
      (FiniteEtale.pullback (c.π.app i)).map (b k) ≫ e.hom = e.hom ≫ a k
  have hP (s : Finset α) : P s := by
    induction s using Finset.induction_on with
    | empty =>
      obtain ⟨i, V, ⟨e⟩⟩ := exists_inverse_limit_model D c hc W
      exact ⟨i, V, e, fun _ => 𝟙 V, fun _ hk => False.elim (Finset.notMem_empty _ hk)⟩
    | @insert k s _ ih =>
      obtain ⟨i, V, e, b, hb⟩ := ih
      obtain ⟨j, hji, d, hd⟩ := exists_inverse_limit_stage_hom D c hc i V V
        (e.hom ≫ a k ≫ e.inv)
      let U := FiniteEtale.pullback (D.map hji)
      let F := FiniteEtale.pullback (c.π.app i)
      let F' := FiniteEtale.pullback (c.π.app j)
      let E := (inverseLimitPullbackComparison D c hji).app V
      let e' : F'.obj (U.obj V) ≅ W := E.symm ≪≫ e
      change E.hom ≫ F'.map d = (e.hom ≫ a k ≫ e.inv) ≫ E.hom at hd
      have hnew : F'.map d ≫ e'.hom = e'.hom ≫ a k := by
        apply (cancel_epi E.hom).mp
        change E.hom ≫ (F'.map d ≫ (E.inv ≫ e.hom)) =
          E.hom ≫ ((E.inv ≫ e.hom) ≫ a k)
        rw [← Category.assoc E.hom, hd]
        simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]
      have hold (l : α) (hl : l ∈ s) :
          F'.map (U.map (b l)) ≫ e'.hom = e'.hom ≫ a l := by
        have hn : F'.map (U.map (b l)) ≫ E.inv = E.inv ≫ F.map (b l) :=
          (inverseLimitPullbackComparison D c hji).inv.naturality (b l)
        change F'.map (U.map (b l)) ≫ (E.inv ≫ e.hom) =
          (E.inv ≫ e.hom) ≫ a l
        rw [← Category.assoc, hn, Category.assoc, hb l hl, Category.assoc]
      refine ⟨j, U.obj V, e', fun l => if l = k then d else U.map (b l), ?_⟩
      intro l hl
      by_cases hlk : l = k
      · subst l
        change F'.map (if k = k then d else U.map (b k)) ≫ e'.hom = e'.hom ≫ a k
        rw [ite_eq_left rfl]
        exact hnew
      · have hls : l ∈ s := (Finset.mem_insert.mp hl).resolve_left hlk
        change F'.map (if l = k then d else U.map (b l)) ≫ e'.hom = e'.hom ≫ a l
        rw [ite_eq_right hlk]
        exact hold l hls
  have : Fintype α := Fintype.ofFinite α
  obtain ⟨i, V, e, b, hb⟩ := hP Finset.univ
  exact ⟨i, V, e, b, fun k => hb k (Finset.mem_univ k)⟩

/-- A finite group action on an original finite étale cover descends with
all multiplication and identity equations to one actual stage. The generic
identification retains the specified group labels. -/
theorem exists_inverse_limit_model_finite_action
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (h : i ⟶ j), IsAffineHom (D.map h)]
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (W : FiniteEtale c.pt) {G : Type v} [Group G] [Finite G] (ρ : G →* Aut W) :
    ∃ (i : I) (V : FiniteEtale (D.obj i))
      (e : (FiniteEtale.pullback (c.π.app i)).obj V ≅ W)
      (ρV : G →* Aut V), ∀ g : G,
      (FiniteEtale.pullback (c.π.app i)).map (ρV g).asIso.hom ≫ e.hom =
        e.hom ≫ (ρ g).asIso.hom := by
  classical
  obtain ⟨i, V, e, b, hb⟩ := exists_inverse_limit_model_endomorphisms D c hc W
    (fun g : G => (ρ g).asIso.hom)
  let F := FiniteEtale.pullback (c.π.app i)
  let left : Option (G × G) → (V ⟶ V)
    | none => b 1
    | some (g, h) => b h ≫ b g
  let right : Option (G × G) → (V ⟶ V)
    | none => 𝟙 V
    | some (g, h) => b (g * h)
  have heq (t : Option (G × G)) : F.map (left t) = F.map (right t) := by
    apply (cancel_mono e.hom).mp
    cases t with
    | none =>
      change F.map (b 1) ≫ e.hom = F.map (𝟙 V) ≫ e.hom
      rw [hb, F.map_id, Category.id_comp, ρ.map_one]
      exact Category.comp_id e.hom
    | some t =>
      rcases t with ⟨g, h⟩
      change F.map (b h ≫ b g) ≫ e.hom = F.map (b (g * h)) ≫ e.hom
      calc
        F.map (b h ≫ b g) ≫ e.hom = e.hom ≫ (ρ h).asIso.hom ≫ (ρ g).asIso.hom := by
          rw [F.map_comp, Category.assoc, hb, ← Category.assoc, hb, Category.assoc]
        _ = e.hom ≫ (ρ (g * h)).asIso.hom := by rw [ρ.map_mul]; rfl
        _ = F.map (b (g * h)) ≫ e.hom := (hb (g * h)).symm
  obtain ⟨j, hji, hj⟩ := exists_inverse_limit_stage_map_eq_family D c hc i
    (fun _ : Option (G × G) => V) (fun _ => V) left right heq
  let U := FiniteEtale.pullback (D.map hji)
  let F' := FiniteEtale.pullback (c.π.app j)
  let E := (inverseLimitPullbackComparison D c hji).app V
  let e' : F'.obj (U.obj V) ≅ W := E.symm ≪≫ e
  let β : G →* End (U.obj V) :=
    { toFun := fun g => .of (U.map (b g))
      map_one' := by
        apply End.ext
        have H := hj none
        change U.map (b 1) = U.map (𝟙 V) at H
        exact H.trans (U.map_id V)
      map_mul' := fun g h => by
        apply End.ext
        have H := hj (some (g, h))
        change U.map (b h ≫ b g) = U.map (b (g * h)) at H
        exact H.symm.trans (U.map_comp (b h) (b g)) }
  let ρV : G →* Aut (U.obj V) :=
    (Aut.unitsEndEquivAut (U.obj V)).toMonoidHom.comp β.toHomUnits
  refine ⟨j, U.obj V, e', ρV, ?_⟩
  intro g
  change F'.map (U.map (b g)) ≫ (E.inv ≫ e.hom) =
    (E.inv ≫ e.hom) ≫ (ρ g).asIso.hom
  have hn : F'.map (U.map (b g)) ≫ E.inv = E.inv ≫ F.map (b g) :=
    (inverseLimitPullbackComparison D c hji).inv.naturality (b g)
  rw [← Category.assoc, hn, Category.assoc, hb, Category.assoc]

/-- The entire finite deck group of an original cover descends faithfully
with its labels. This asserts an action on the model, without asserting
connectedness or the Galois property of its special fibres. -/
theorem exists_inverse_limit_model_deck_action
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (h : i ⟶ j), IsAffineHom (D.map h)]
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (W : FiniteEtale c.pt) [Finite (Aut W)] :
    ∃ (i : I) (V : FiniteEtale (D.obj i))
      (e : (FiniteEtale.pullback (c.π.app i)).obj V ≅ W)
      (ρV : Aut W →* Aut V), Function.Injective ρV ∧ ∀ g : Aut W,
      (FiniteEtale.pullback (c.π.app i)).map (ρV g).asIso.hom ≫ e.hom =
        e.hom ≫ g.asIso.hom := by
  obtain ⟨i, V, e, ρV, hρV⟩ := exists_inverse_limit_model_finite_action D c hc W
    (MonoidHom.id (Aut W))
  simp only [MonoidHom.id_apply] at hρV
  refine ⟨i, V, e, ρV, ?_, hρV⟩
  intro g h hgh
  apply Aut.ext
  apply Iso.ext
  apply (cancel_epi e.hom).mp
  rw [← hρV g, ← hρV h, hgh]


local instance finiteEtaleHasFiniteLimitsTorsor (X : Scheme.{u}) :
    HasFiniteLimits (FiniteEtale X) :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

local instance finiteEtalePullbackPreservesFiniteLimitsTorsor
    {X Y : Scheme.{u}} (f : X ⟶ Y) : PreservesFiniteLimits (FiniteEtale.pullback f) := by
  apply AffineAnd.preservesFiniteLimits_pullback

/-- A finite action whose canonical graph pairing is invertible descends
with that same pairing invertible. This graph condition holds at the
stage itself, and therefore after every change of base. -/
theorem exists_inverse_limit_model_invertible_graph
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (h : i ⟶ j), IsAffineHom (D.map h)]
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (W : FiniteEtale c.pt) {G : Type v} [Group G] [Finite G] (ρ : G →* Aut W)
    [IsIso (graphFamilyMap (fun g : G => (ρ g).asIso.hom))] :
    ∃ (i : I) (V : FiniteEtale (D.obj i))
      (e : (FiniteEtale.pullback (c.π.app i)).obj V ≅ W)
      (ρV : G →* Aut V), IsIso (graphFamilyMap (fun g : G => (ρV g).asIso.hom)) ∧
      ∀ g : G, (FiniteEtale.pullback (c.π.app i)).map (ρV g).asIso.hom ≫ e.hom =
        e.hom ≫ (ρ g).asIso.hom := by
  obtain ⟨i, V, e, ρV, hρV⟩ := exists_inverse_limit_model_finite_action D c hc W ρ
  let F := FiniteEtale.pullback (c.π.app i)
  have hgraph : IsIso (graphFamilyMap (fun g : G => F.map (ρV g).asIso.hom)) :=
    graphFamilyMap_isIso_of_equivariant_iso
      (fun g : G => F.map (ρV g).asIso.hom) (fun g : G => (ρ g).asIso.hom) e hρV
  have : IsIso (F.map (graphFamilyMap (fun g : G => (ρV g).asIso.hom))) :=
    (graphFamilyMap_map_isIso_iff F (fun g : G => (ρV g).asIso.hom)).mpr hgraph
  obtain ⟨j, hji, hj⟩ := exists_inverse_limit_stage_isIso D c hc i
    (graphFamilyMap (fun g : G => (ρV g).asIso.hom))
  let U := FiniteEtale.pullback (D.map hji)
  let F' := FiniteEtale.pullback (c.π.app j)
  let E := (inverseLimitPullbackComparison D c hji).app V
  let e' : F'.obj (U.obj V) ≅ W := E.symm ≪≫ e
  let ρV' : G →* Aut (U.obj V) := (U.mapAut V).comp ρV
  have hgraph' : IsIso (graphFamilyMap (fun g : G => (ρV' g).asIso.hom)) :=
    (graphFamilyMap_map_isIso_iff U (fun g : G => (ρV g).asIso.hom)).mp hj
  refine ⟨j, U.obj V, e', ρV', hgraph', ?_⟩
  intro g
  change F'.map (U.map (ρV g).asIso.hom) ≫ (E.inv ≫ e.hom) =
    (E.inv ≫ e.hom) ≫ (ρ g).asIso.hom
  have hn : F'.map (U.map (ρV g).asIso.hom) ≫ E.inv = E.inv ≫ F.map (ρV g).asIso.hom :=
    (inverseLimitPullbackComparison D c hji).inv.naturality (ρV g).asIso.hom
  rw [← Category.assoc, hn, Category.assoc, hρV, Category.assoc]

/-- Finite action descent may be chosen to preserve the canonical graph
pairing whenever it is invertible on the original cover. -/
theorem exists_inverse_limit_model_finite_action_with_graph
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (h : i ⟶ j), IsAffineHom (D.map h)]
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (W : FiniteEtale c.pt) {G : Type v} [Group G] [Finite G] (ρ : G →* Aut W) :
    ∃ (i : I) (V : FiniteEtale (D.obj i))
      (e : (FiniteEtale.pullback (c.π.app i)).obj V ≅ W)
      (ρV : G →* Aut V),
      (IsIso (graphFamilyMap (fun g : G => (ρ g).asIso.hom)) →
        IsIso (graphFamilyMap (fun g : G => (ρV g).asIso.hom))) ∧
      ∀ g : G, (FiniteEtale.pullback (c.π.app i)).map (ρV g).asIso.hom ≫ e.hom =
        e.hom ≫ (ρ g).asIso.hom := by
  classical
  by_cases h : IsIso (graphFamilyMap (fun g : G => (ρ g).asIso.hom))
  · have : IsIso (graphFamilyMap (fun g : G => (ρ g).asIso.hom)) := h
    obtain ⟨i, V, e, ρV, hgraph, hρV⟩ := exists_inverse_limit_model_invertible_graph D c hc W ρ
    exact ⟨i, V, e, ρV, fun _ => hgraph, hρV⟩
  · obtain ⟨i, V, e, ρV, hρV⟩ := exists_inverse_limit_model_finite_action D c hc W ρ
    exact ⟨i, V, e, ρV, fun hgraph => (h hgraph).elim, hρV⟩

/-- A finite étale torsor retains its labelled graph pairing after every
scheme base change, including passage to a residue fibre. -/
theorem graphFamilyMap_pullback_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : FiniteEtale Y) {G : Type v} [Group G] [Finite G] (ρ : G →* Aut V)
    [IsIso (graphFamilyMap (fun g : G => (ρ g).asIso.hom))] :
    IsIso (graphFamilyMap (fun g : G =>
      (FiniteEtale.pullback f).map (ρ g).asIso.hom)) :=
  (graphFamilyMap_map_isIso_iff (FiniteEtale.pullback f)
    (fun g : G => (ρ g).asIso.hom)).mp inferInstance

/-- Surjectivity of a finite étale model over the inverse limit holds at
an actual later stage. The proof descends the open image of the cover. -/
theorem exists_inverse_limit_stage_surjective
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (h : i ⟶ j), IsAffineHom (D.map h)]
    [∀ i : I, CompactSpace (D.obj i)]
    (i : I) (V : FiniteEtale (D.obj i))
    [Surjective ((FiniteEtale.pullback (c.π.app i)).obj V).hom] :
    ∃ (j : I) (hji : j ⟶ i),
      Surjective ((FiniteEtale.pullback (D.map hji)).obj V).hom := by
  let O : (D.obj i).Opens := ⟨Set.range V.hom, V.hom.isOpenMap.isOpen_range⟩
  have hO : c.π.app i ⁻¹ᵁ O = ⊤ := by
    apply SetLike.coe_injective
    change (c.π.app i) ⁻¹' Set.range V.hom = Set.univ
    rw [← Scheme.Pullback.range_snd]
    exact Set.range_eq_univ.mpr ((FiniteEtale.pullback (c.π.app i)).obj V).hom.surjective
  obtain ⟨j, hji, hj⟩ := AlgebraicGeometry.exists_map_eq_top D c hc O hO
  refine ⟨j, hji, ⟨?_⟩⟩
  change Function.Surjective (Limits.pullback.snd V.hom (D.map hji))
  apply Set.range_eq_univ.mp
  rw [Scheme.Pullback.range_snd]
  exact congrArg (fun U : (D.obj j).Opens => (U : Set (D.obj j))) hj

/-- The finite action model can preserve both surjectivity and the
invertible graph pairing of the original cover. These two conditions give
an actual finite étale torsor rather than only an invertible graph map. -/
theorem exists_inverse_limit_model_finite_action_with_cover
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (h : i ⟶ j), IsAffineHom (D.map h)]
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (W : FiniteEtale c.pt) {G : Type v} [Group G] [Finite G] (ρ : G →* Aut W) :
    ∃ (i : I) (V : FiniteEtale (D.obj i))
      (e : (FiniteEtale.pullback (c.π.app i)).obj V ≅ W)
      (ρV : G →* Aut V), (Surjective W.hom → Surjective V.hom) ∧
      (IsIso (graphFamilyMap (fun g : G => (ρ g).asIso.hom)) →
        IsIso (graphFamilyMap (fun g : G => (ρV g).asIso.hom))) ∧
      ∀ g : G, (FiniteEtale.pullback (c.π.app i)).map (ρV g).asIso.hom ≫ e.hom =
        e.hom ≫ (ρ g).asIso.hom := by
  classical
  obtain ⟨i, V, e, ρV, hgraph, hρV⟩ :=
    exists_inverse_limit_model_finite_action_with_graph D c hc W ρ
  by_cases hs : Surjective W.hom
  · have : Surjective W.hom := hs
    have : IsIso e.hom.left := by
      change IsIso ((FiniteEtale.forget c.pt ⋙ CategoryTheory.Over.forget c.pt).map e.hom)
      infer_instance
    have : Surjective ((FiniteEtale.pullback (c.π.app i)).obj V).hom := by
      rw [← MorphismProperty.Over.w e.hom]
      infer_instance
    obtain ⟨j, hji, hj⟩ := exists_inverse_limit_stage_surjective D c hc i V
    let U := FiniteEtale.pullback (D.map hji)
    let F := FiniteEtale.pullback (c.π.app i)
    let F' := FiniteEtale.pullback (c.π.app j)
    let E := (inverseLimitPullbackComparison D c hji).app V
    let e' : F'.obj (U.obj V) ≅ W := E.symm ≪≫ e
    let ρV' : G →* Aut (U.obj V) := (U.mapAut V).comp ρV
    refine ⟨j, U.obj V, e', ρV', fun _ => hj, ?_, ?_⟩
    · intro h
      have : IsIso (graphFamilyMap (fun g : G => (ρV g).asIso.hom)) := hgraph h
      exact (graphFamilyMap_map_isIso_iff U
        (fun g : G => (ρV g).asIso.hom)).mp inferInstance
    · intro g
      change F'.map (U.map (ρV g).asIso.hom) ≫ (E.inv ≫ e.hom) =
        (E.inv ≫ e.hom) ≫ (ρ g).asIso.hom
      have hn : F'.map (U.map (ρV g).asIso.hom) ≫ E.inv = E.inv ≫ F.map (ρV g).asIso.hom :=
        (inverseLimitPullbackComparison D c hji).inv.naturality (ρV g).asIso.hom
      rw [← Category.assoc, hn, Category.assoc, hρV, Category.assoc]
  · exact ⟨i, V, e, ρV, fun h => (hs h).elim, hgraph, hρV⟩


end AlgebraicGeometry.FiniteEtale
