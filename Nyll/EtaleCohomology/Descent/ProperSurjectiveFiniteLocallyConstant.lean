/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Constructible.FiniteEtaleSheaf
public import Nyll.EtaleCohomology.Constructible.FiniteLocallyConstantSet
public import Nyll.EtaleCohomology.Constructible.Representability
public import Nyll.EtaleCohomology.Sites.SetPullbackExact
public import Nyll.EtaleCohomology.Sites.SetPullbackComposition
public import Nyll.EtaleCohomology.Sites.SetSheafFunctors
public import Nyll.EtaleCohomology.Sites.PointConstantFiber
public import Nyll.EtaleCohomology.Sites.PullbackSections
public import Nyll.EtaleCohomology.Sites.PullbackUnitGeometricStalks
public import Nyll.EtaleCohomology.Sites.PushforwardStalkComparison
public import Nyll.EtaleCohomology.Sites.SeparablyClosedFieldStalks
public import Nyll.EtaleFundamentalGroups.Cohomology.RepresenterPullback
public import Nyll.SchemeTheory.FiniteEtale.FiniteEtaleMorphismNeighborhood
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.CategoryTheory.Sites.Point.Conservative
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Finite germs and detection along the original surjective inverse image

Finite families of actual germs admit representatives on one pointed étale
neighborhood. The existing set-valued pullback stalk isomorphism then gives
isomorphism detection along an arbitrary surjection and finite stalks when
the actual inverse image is finite locally constant.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite

universe u v

namespace EtaleCohomology

/-- A finite family in the actual fiber has representatives at one common
pointed site object. The original germs, not an abstract finite model, are
recovered by the actual colimit arrows. -/
theorem exists_common_finite_germ_representatives
    {C : Type v} [Category.{u} C] [LocallySmall.{u} C]
    {J : GrothendieckTopology C} (Φ : J.Point.{u})
    (P : Cᵒᵖ ⥤ Type u) {A : Type u} [Finite A]
    (a : A → Φ.presheafFiber.obj P) :
    ∃ (U : C) (x : Φ.fiber.obj U) (b : A → P.obj (op U)),
      ∀ i, Φ.toPresheafFiber U x P (b i) = a i := by
  classical
  have : Fintype A := Fintype.ofFinite A
  choose U x b hb using fun i => Φ.toPresheafFiber_jointly_surjective (P := P) (a i)
  let e : A → Φ.fiber.Elements := fun i => Φ.fiber.elementsMk (U i) (x i)
  obtain ⟨V, hV⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image e)
  have hf (i : A) : Nonempty (V ⟶ e i) :=
    hV (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  let f (i : A) : V ⟶ e i := Classical.choice (hf i)
  refine ⟨V.obj, V.val, fun i => P.map (f i).hom.op (b i), ?_⟩
  intro i
  have h := ConcreteCategory.congr_hom
    (Φ.toPresheafFiber_w (f i).hom V.val P) (b i)
  change Φ.toPresheafFiber V.obj V.val P (P.map (f i).hom.op (b i)) =
    Φ.toPresheafFiber (U i) (Φ.fiber.map (f i).hom V.val) P (b i) at h
  rw [(f i).map_val] at h
  exact h.trans (hb i)

/-- The original inverse-image functor along a surjective scheme morphism
detects isomorphisms of arbitrary set-valued étale sheaves. -/
theorem etaleSetPullback_isIso_of_surjective
    {X Y : Scheme.{u}} (q : Y ⟶ X) [Surjective q]
    {F G : Sheaf X.smallEtaleTopology (Type u)} (a : F ⟶ G)
    [IsIso ((etaleSetPullback q).map a)] : IsIso a := by
  let Ω : Y → Type u := fun y => AlgebraicClosure (Y.residueField y)
  let s : ∀ y : Y, Spec (CommRingCat.of (Ω y)) ⟶ Y := fun y =>
    Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) (Ω y))) ≫
      Y.fromSpecResidueField y
  have hs (y : Y) : s y default = y := by
    rw [Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply y _
  let t : ∀ y : Y, Spec (CommRingCat.of (Ω y)) ⟶ X := fun y => s y ≫ q
  have hcover : ⋃ y : Y, Set.range (t y) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨y, rfl⟩ := q.surjective x
    refine Set.mem_iUnion.mpr ⟨y, default, ?_⟩
    exact (Scheme.Hom.comp_apply (s y) q default).trans (congrArg q (hs y))
  have hpoints := Scheme.isConservative_pointSmallEtale t hcover
  apply (hpoints.jointlyReflectIsomorphisms_type.isIso_iff a).mpr
  rintro ⟨_, ⟨y⟩⟩
  change IsIso ((Scheme.pointSmallEtale (s y ≫ q)).sheafFiber.map a)
  have hm : IsIso ((Scheme.pointSmallEtale (s y)).sheafFiber.map
      ((etaleSetPullback q).map a)) := inferInstance
  exact (NatIso.isIso_map_iff (etaleSetPullbackStalkIso q (s y)) a).mp hm

/-- A finite locally constant sheaf has finite actual geometric stalks,
through its existing finite étale representer and fiber comparison. -/
theorem finite_geometricStalk_of_isEtaleFiniteLocallyConstantSet
    {X : Scheme.{u}} (G : Sheaf X.smallEtaleTopology (Type u))
    (hG : IsEtaleFiniteLocallyConstantSet G)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (CommRingCat.of Ω) ⟶ X) :
    Finite ((Scheme.pointSmallEtale s).sheafFiber.obj G) := by
  obtain ⟨W, ⟨e⟩⟩ := hG.exists_finiteEtaleSheaf_iso
  let E := (Scheme.pointSmallEtale s).sheafFiber.mapIso e.symm ≪≫
    (finiteEtaleSheafFiberIso s).app W
  exact Finite.of_equiv ((FiniteEtale.fiber s).obj W) E.toEquiv.symm

/-- Finite local constancy of the original inverse image supplies finite
stalks downstairs at every composed geometric point, without a comparison
or finite-stalk hypothesis being inserted as extra data. -/
theorem finite_geometricStalk_of_isEtaleFiniteLocallyConstantSet_pullback
    {X Y : Scheme.{u}} (q : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology (Type u))
    (hG : IsEtaleFiniteLocallyConstantSet ((etaleSetPullback q).obj G))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (CommRingCat.of Ω) ⟶ Y) :
    Finite ((Scheme.pointSmallEtale (s ≫ q)).sheafFiber.obj G) := by
  have hfinite : Finite ((Scheme.pointSmallEtale s).sheafFiber.obj
      ((etaleSetPullback q).obj G)) :=
    finite_geometricStalk_of_isEtaleFiniteLocallyConstantSet _ hG s
  exact @Finite.of_equiv _ _ hfinite ((etaleSetPullbackStalkIso q s).app G).toEquiv

/-- For sheaves whose actual inverse images are finite locally constant,
invertibility on an original base change spreads to an open neighborhood.
The comparison on that neighborhood is the original sheaf morphism. -/
theorem exists_isIso_etaleSetPullback_open_of_isIso_baseChange
    {X Y T : Scheme.{u}} (q : Y ⟶ X) [UniversallyClosed q] [Surjective q]
    {F G : Sheaf X.smallEtaleTopology (Type u)} (α : F ⟶ G)
    (hF : IsEtaleFiniteLocallyConstantSet ((etaleSetPullback q).obj F))
    (hG : IsEtaleFiniteLocallyConstantSet ((etaleSetPullback q).obj G))
    (t : T ⟶ X) [IsIso ((etaleSetPullback t).map α)] (a : T) :
    ∃ U : X.Opens, t a ∈ U ∧ IsIso ((etaleSetPullback U.ι).map α) := by
  obtain ⟨V, ⟨eF⟩⟩ := hF.exists_finiteEtaleSheaf_iso
  obtain ⟨W, ⟨eG⟩⟩ := hG.exists_finiteEtaleSheaf_iso
  let m : V ⟶ W := (finiteEtaleSheafFullyFaithful Y).preimage
    (eF.hom ≫ (etaleSetPullback q).map α ≫ eG.inv)
  have hm : (finiteEtaleSheaf Y).map m =
      eF.hom ≫ (etaleSetPullback q).map α ≫ eG.inv :=
    (finiteEtaleSheafFullyFaithful Y).map_preimage _
  have hrep {S : Scheme.{u}} (r : S ⟶ Y) :
      IsIso ((FiniteEtale.pullback r).map m) ↔
        IsIso ((etaleSetPullback r).map ((etaleSetPullback q).map α)) := by
    have hcomp :
        IsIso ((FiniteEtale.pullback r).map m) ↔
          IsIso ((etaleSetPullback r).map ((finiteEtaleSheaf Y).map m)) := by
      constructor
      · intro hi
        have hmap : IsIso ((finiteEtaleSheaf S).map
            ((FiniteEtale.pullback r).map m)) := inferInstance
        exact (NatIso.isIso_map_iff
          (EtaleFundamentalGroups.Cohomology.finiteEtaleSheafPullbackIso r) m).mpr hmap
      · intro hi
        have hmap : IsIso ((finiteEtaleSheaf S).map
            ((FiniteEtale.pullback r).map m)) :=
          (NatIso.isIso_map_iff
            (EtaleFundamentalGroups.Cohomology.finiteEtaleSheafPullbackIso r) m).mp hi
        exact (finiteEtaleSheafFullyFaithful S).isIso_of_isIso_map _
    rw [hm] at hcomp
    simpa only [Functor.map_comp, isIso_comp_left_iff, isIso_comp_right_iff] using hcomp
  let r : pullback q t ⟶ Y := pullback.fst q t
  let p : pullback q t ⟶ T := pullback.snd q t
  have hp : IsIso ((etaleSetPullback p).map ((etaleSetPullback t).map α)) :=
    inferInstance
  have hpt : IsIso ((etaleSetPullback (p ≫ t)).map α) :=
    (NatIso.isIso_map_iff (etaleSetPullbackCompIso p t) α).mpr hp
  have hrq : IsIso ((etaleSetPullback (r ≫ q)).map α) := by
    have heq : r ≫ q = p ≫ t := pullback.condition
    rw [heq]
    exact hpt
  have hr : IsIso ((etaleSetPullback r).map ((etaleSetPullback q).map α)) :=
    (NatIso.isIso_map_iff (etaleSetPullbackCompIso r q) α).mp hrq
  have hm₀ : IsIso ((FiniteEtale.pullback (pullback.fst q t)).map m) :=
    (hrep r).mpr hr
  obtain ⟨U, ha, hU⟩ :=
    FiniteEtale.exists_isIso_pullback_open_of_isIso_pullback q t m a
  refine ⟨U, ha, ?_⟩
  let B : Y.Opens := q ⁻¹ᵁ U
  have hBU : IsIso ((etaleSetPullback B.ι).map ((etaleSetPullback q).map α)) :=
    (hrep B.ι).mp hU
  have hBq : IsIso ((etaleSetPullback (B.ι ≫ q)).map α) :=
    (NatIso.isIso_map_iff (etaleSetPullbackCompIso B.ι q) α).mpr hBU
  have hqU : IsIso ((etaleSetPullback ((q ∣_ U) ≫ U.ι)).map α) := by
    rw [morphismRestrict_ι]
    exact hBq
  have hpull : IsIso
      ((etaleSetPullback (q ∣_ U)).map ((etaleSetPullback U.ι).map α)) :=
    (NatIso.isIso_map_iff (etaleSetPullbackCompIso (q ∣_ U) U.ι) α).mp hqU
  have hsurj : Surjective (q ∣_ U) :=
    MorphismProperty.of_isPullback
      (P := show MorphismProperty Scheme.{u} from @Surjective)
      (isPullback_morphismRestrict q U).flip inferInstance
  exact etaleSetPullback_isIso_of_surjective (q ∣_ U) ((etaleSetPullback U.ι).map α)

private theorem geometricGerm_point_congr
    {X : Scheme.{u}} (G : Sheaf X.smallEtaleTopology (Type u))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    {s t : Spec (CommRingCat.of Ω) ⟶ X} (h : s = t) (U : X.Etale)
    (v : (Scheme.pointSmallEtale s).fiber.obj U)
    (w : (Scheme.pointSmallEtale t).fiber.obj U) (hvw : v.left = w.left) :
    (Scheme.pointSmallEtale s).toPresheafFiber U v G.obj ≫
        eqToHom (congrArg (fun k => (Scheme.pointSmallEtale k).sheafFiber.obj G) h) =
      (Scheme.pointSmallEtale t).toPresheafFiber U w G.obj := by
  cases h
  have he : v = w := Over.OverMorphism.ext hvw
  subst w
  exact Category.comp_id _

/-- A finite actual geometric stalk is represented on one pointed étale
neighborhood by a map from its finite constant sheaf which is invertible
at the chosen geometric point. The map is built from the original germs
using the actual inverse-image unit. -/
theorem exists_etale_constant_chart_at_finite_geometricStalk
    {X : Scheme.{u}} (G : Sheaf X.smallEtaleTopology (Type u))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (CommRingCat.of Ω) ⟶ X)
    [Finite ((Scheme.pointSmallEtale s).sheafFiber.obj G)] :
    ∃ (U : X.Etale) (v : (Scheme.pointSmallEtale s).fiber.obj U)
      (A : Type u) (_ : Finite A)
      (α : (constantSheaf U.left.smallEtaleTopology (Type u)).obj A ⟶
        (etaleSetPullback U.hom).obj G),
      IsIso ((Scheme.pointSmallEtale v.left).sheafFiber.map α) := by
  let A : Type u := (Scheme.pointSmallEtale s).sheafFiber.obj G
  obtain ⟨U, v, b, hb⟩ := exists_common_finite_germ_representatives
    (Scheme.pointSmallEtale s) G.obj (fun a : A => a)
  let q : U.left ⟶ X := U.hom
  let t : Spec (CommRingCat.of Ω) ⟶ U.left := v.left
  let T : U.left.Etale := Scheme.Etale.mk (𝟙 U.left)
  let a₀ : (Scheme.pointSmallEtale t).fiber.obj T :=
    Over.homMk t (Category.comp_id t)
  let L := etaleSetPullback q
  let H := L.obj G
  let adj := etaleSetPullbackPushforwardAdjunction q
  let hl : (𝟙 U.left) ≫ U.hom = T.hom ≫ q := rfl
  let σ : G.obj.obj (op U) ⟶ H.obj.obj (op T) :=
    (adj.unit.app G).hom.app (op U) ≫
      H.obj.map (etaleBaseChangeLift q (𝟙 U.left) hl).op
  let w : (Scheme.pointSmallEtale (t ≫ q)).fiber.obj U :=
    Over.homMk (t ≫ 𝟙 U.left)
      ((Category.assoc t (𝟙 U.left) q).trans
        (congrArg (fun k => t ≫ k) (Category.id_comp q)))
  let γ : G.obj.obj (op U) ⟶
      (Scheme.pointSmallEtale (t ≫ q)).sheafFiber.obj G :=
    (Scheme.pointSmallEtale (t ≫ q)).toPresheafFiber U w G.obj
  let γH : H.obj.obj (op T) ⟶ (Scheme.pointSmallEtale t).sheafFiber.obj H :=
    (Scheme.pointSmallEtale t).toPresheafFiber T a₀ H.obj
  let k : (Scheme.pointSmallEtale (t ≫ q)).sheafFiber.obj G ⟶
      (Scheme.pointSmallEtale t).sheafFiber.obj H :=
    (Scheme.pointSmallEtale (t ≫ q)).sheafFiber.map (adj.unit.app G) ≫
      etalePushforwardStalkComponent q (t ≫ q) ⟨t, rfl⟩ H
  have hk : IsIso k :=
    etalePullbackUnit_stalkComponent_isIso_generic q t (Type u) L adj G
  have hσ : σ ≫ γH = γ ≫ k := by
    exact etalePullbackSectionMap_toPresheafFiber_generic q t (Type u) L adj G
      (U := T) (V := U) (𝟙 U.left) hl a₀
  have hv : t ≫ q = s := v.w
  let e : (Scheme.pointSmallEtale (t ≫ q)).sheafFiber.obj G ≅ A :=
    eqToIso (congrArg (fun z => (Scheme.pointSmallEtale z).sheafFiber.obj G) hv)
  have he : γ ≫ e.hom = (Scheme.pointSmallEtale s).toPresheafFiber U v G.obj :=
    geometricGerm_point_congr G hv U w v (Category.comp_id t)
  let β : A ⟶ G.obj.obj (op U) := ↾b
  have hbγ : (β ≫ γ) ≫ e.hom = 𝟙 A := by
    refine (Category.assoc _ _ _).trans ((congrArg (fun z => β ≫ z) he).trans ?_)
    ext i
    exact hb i
  have hβγ : IsIso (β ≫ γ) := by
    have hi : IsIso (𝟙 A) := (Iso.refl A).isIso_hom
    have hcomp : IsIso ((β ≫ γ) ≫ e.hom) := hbγ.symm ▸ hi
    have heiso : IsIso e.hom := e.isIso_hom
    exact IsIso.of_isIso_comp_right _ e.hom
  let hT := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) U.left
  let cAdj := constantSheafAdj U.left.smallEtaleTopology (Type u) hT
  let C := (constantSheaf U.left.smallEtaleTopology (Type u)).obj A
  let α : C ⟶ H := (cAdj.homEquiv A H).symm (β ≫ σ)
  have hα : cAdj.unit.app A ≫ α.hom.app (op T) = β ≫ σ := by
    have hh := (cAdj.homEquiv A H).apply_symm_apply (β ≫ σ)
    rw [Adjunction.homEquiv_unit] at hh
    exact hh
  let γC : C.obj.obj (op T) ⟶ (Scheme.pointSmallEtale t).sheafFiber.obj C :=
    (Scheme.pointSmallEtale t).toPresheafFiber T a₀ C.obj
  have hc : IsIso (cAdj.unit.app A ≫ γC) :=
    (Scheme.pointSmallEtale t).constantSheaf_unit_germ_isIso (Type u) hT A a₀
  have hn : γC ≫ (Scheme.pointSmallEtale t).sheafFiber.map α =
      α.hom.app (op T) ≫ γH :=
    (Scheme.pointSmallEtale t).toPresheafFiber_naturality α.hom T a₀
  have hmap : (cAdj.unit.app A ≫ γC) ≫
      (Scheme.pointSmallEtale t).sheafFiber.map α = (β ≫ γ) ≫ k := by
    calc
      _ = cAdj.unit.app A ≫ (γC ≫
          (Scheme.pointSmallEtale t).sheafFiber.map α) := Category.assoc _ _ _
      _ = cAdj.unit.app A ≫ (α.hom.app (op T) ≫ γH) :=
        congrArg (fun z => cAdj.unit.app A ≫ z) hn
      _ = (cAdj.unit.app A ≫ α.hom.app (op T)) ≫ γH :=
        (Category.assoc _ _ _).symm
      _ = (β ≫ σ) ≫ γH := congrArg (fun z => z ≫ γH) hα
      _ = β ≫ (σ ≫ γH) := Category.assoc _ _ _
      _ = β ≫ (γ ≫ k) := congrArg (fun z => β ≫ z) hσ
      _ = (β ≫ γ) ≫ k := (Category.assoc _ _ _).symm
  have hright : IsIso ((β ≫ γ) ≫ k) := inferInstance
  have hαiso : IsIso ((Scheme.pointSmallEtale t).sheafFiber.map α) :=
    @IsIso.of_isIso_fac_left (Type u) _ A
      ((Scheme.pointSmallEtale t).sheafFiber.obj C)
      ((Scheme.pointSmallEtale t).sheafFiber.obj H)
      (cAdj.unit.app A ≫ γC) ((Scheme.pointSmallEtale t).sheafFiber.map α)
      ((β ≫ γ) ≫ k) hc hright hmap
  exact ⟨U, v, A,
    inferInstanceAs (Finite ((Scheme.pointSmallEtale s).sheafFiber.obj G)),
    α, hαiso⟩

private theorem geometricPullback_isIso_of_stalk
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (t : Spec (CommRingCat.of Ω) ⟶ X)
    {F G : Sheaf X.smallEtaleTopology (Type u)} (α : F ⟶ G)
    [IsIso ((Scheme.pointSmallEtale t).sheafFiber.map α)] :
    IsIso ((etaleSetPullback t).map α) := by
  let S := Spec (CommRingCat.of Ω)
  let Ψ := Scheme.pointSmallEtale (𝟙 S)
  let η := (etaleSetPullback t).map α
  have hcomp : IsIso ((Scheme.pointSmallEtale ((𝟙 S) ≫ t)).sheafFiber.map α) := by
    rw [Category.id_comp]
    infer_instance
  have hstalk : IsIso (Ψ.sheafFiber.map η) :=
    (NatIso.isIso_map_iff (etaleSetPullbackStalkIso t (𝟙 S)) α).mpr hcomp
  let γF := etaleIdentityGlobalSectionsGerm Ω (Type u) ((etaleSetPullback t).obj F)
  let γG := etaleIdentityGlobalSectionsGerm Ω (Type u) ((etaleSetPullback t).obj G)
  have hγF : IsIso γF := etaleIdentityGlobalSectionsGerm_isIso Ω (Type u) _
  have hγG : IsIso γG := etaleIdentityGlobalSectionsGerm_isIso Ω (Type u) _
  have hn : γF ≫ Ψ.sheafFiber.map η =
      η.hom.app (op (Scheme.Etale.mk (𝟙 S))) ≫ γG :=
    Ψ.toPresheafFiber_naturality η.hom (Scheme.Etale.mk (𝟙 S))
      (Over.homMk (𝟙 S) (Category.comp_id _))
  have hl : IsIso (γF ≫ Ψ.sheafFiber.map η) := inferInstance
  have hr : IsIso (η.hom.app (op (Scheme.Etale.mk (𝟙 S))) ≫ γG) := hn ▸ hl
  have hglobal : IsIso (η.hom.app (op (Scheme.Etale.mk (𝟙 S)))) :=
    IsIso.of_isIso_comp_right _ γG
  exact etaleHom_isIso_of_globalSections_of_isSepClosed Ω (Type u) η

/-- Finite local constancy upstairs gives actual finite constant charts
downstairs at every original point of a surjective universally closed
morphism. Proper surjections are a special case. -/
theorem exists_etale_constant_chart_of_surjective_universallyClosed_pullback
    {X Y : Scheme.{u}} (q : Y ⟶ X) [UniversallyClosed q] [Surjective q]
    (G : Sheaf X.smallEtaleTopology (Type u))
    (hG : IsEtaleFiniteLocallyConstantSet ((etaleSetPullback q).obj G))
    (x : X) :
    ∃ (U : X.Etale) (z : U.left), U.hom z = x ∧
      ∃ A : Type u, Finite A ∧
        Nonempty ((etaleSetPullback U.hom).obj G ≅
          (constantSheaf U.left.smallEtaleTopology (Type u)).obj A) := by
  obtain ⟨y, hy⟩ := q.surjective x
  let Ω := AlgebraicClosure (Y.residueField y)
  let s : Spec (CommRingCat.of Ω) ⟶ Y :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) Ω)) ≫
      Y.fromSpecResidueField y
  have hs : s default = y := by
    rw [Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply y _
  have hfinite : Finite ((Scheme.pointSmallEtale (s ≫ q)).sheafFiber.obj G) :=
    finite_geometricStalk_of_isEtaleFiniteLocallyConstantSet_pullback q G hG s
  obtain ⟨U, v, A, hA, α, hα⟩ :=
    exists_etale_constant_chart_at_finite_geometricStalk G (s ≫ q)
  let p : pullback q U.hom ⟶ U.left := pullback.snd q U.hom
  let r : pullback q U.hom ⟶ Y := pullback.fst q U.hom
  let e : (etaleSetPullback p).obj ((etaleSetPullback U.hom).obj G) ≅
      (etaleSetPullback r).obj ((etaleSetPullback q).obj G) :=
    ((etaleSetPullbackCompIso p U.hom).app G).symm ≪≫
      eqToIso (congrArg (fun k => (etaleSetPullback k).obj G)
        (pullback.condition (f := q) (g := U.hom)).symm) ≪≫
      (etaleSetPullbackCompIso r q).app G
  have hGP : IsEtaleFiniteLocallyConstantSet
      ((etaleSetPullback p).obj ((etaleSetPullback U.hom).obj G)) :=
    (hG.pullback r).of_iso e.symm
  have hCP : IsEtaleFiniteLocallyConstantSet
      ((etaleSetPullback p).obj
        ((constantSheaf U.left.smallEtaleTopology (Type u)).obj A)) :=
    (IsEtaleFiniteLocallyConstantSet.constant (X := U.left) A).pullback p
  let t : Spec (CommRingCat.of Ω) ⟶ U.left := v.left
  have hαpull : IsIso ((etaleSetPullback t).map α) :=
    @geometricPullback_isIso_of_stalk U.left Ω _ _ t _ _ α hα
  let a : Spec (CommRingCat.of Ω) := default
  obtain ⟨W, hvW, hW⟩ :=
    @exists_isIso_etaleSetPullback_open_of_isIso_baseChange U.left
      (pullback q U.hom) (Spec (CommRingCat.of Ω)) p _ _ _ _
      α hCP hGP t hαpull a
  let V : X.Etale := Scheme.Etale.mk (W.ι ≫ U.hom)
  let z : V.left := ⟨t a, hvW⟩
  have hz : V.hom z = x := by
    have hv : t ≫ U.hom = s ≫ q := v.w
    calc
      V.hom z = U.hom (t a) := Scheme.Hom.comp_apply W.ι U.hom z
      _ = (t ≫ U.hom) a := (Scheme.Hom.comp_apply _ _ _).symm
      _ = (s ≫ q) a := congrArg (fun k : Spec (CommRingCat.of Ω) ⟶ X => k a) hv
      _ = q (s a) := Scheme.Hom.comp_apply _ _ _
      _ = q y := congrArg q hs
      _ = x := hy
  refine ⟨V, z, hz, A, hA, ⟨?_⟩⟩
  exact (etaleSetPullbackCompIso W.ι U.hom).app G ≪≫
    (asIso ((etaleSetPullback W.ι).map α)).symm ≪≫
      (etaleSetPullbackConstantIso W.ι).app A

/-- Finite local constancy descends along the original inverse-image
functor of any surjective universally closed scheme morphism. In
particular, this applies to every proper surjection. -/
theorem IsEtaleFiniteLocallyConstantSet.of_surjective_universallyClosed_pullback
    {X Y : Scheme.{u}} (q : Y ⟶ X) [UniversallyClosed q] [Surjective q]
    {G : Sheaf X.smallEtaleTopology (Type u)}
    (hG : IsEtaleFiniteLocallyConstantSet ((etaleSetPullback q).obj G)) :
    IsEtaleFiniteLocallyConstantSet G := by
  classical
  choose U z hz A hA e using
    exists_etale_constant_chart_of_surjective_universallyClosed_pullback q G hG
  let 𝒰 : X.Cover.{u}
      (Scheme.precoverage (show MorphismProperty Scheme.{u} from @Etale)) :=
    Scheme.Cover.mkOfCovers X (fun x => (U x).left) (fun x => (U x).hom)
      (fun x => ⟨x, z x, hz x⟩) (fun x => (U x).prop)
  exact ⟨𝒰, fun x => ⟨A x, hA x, e x⟩⟩

end EtaleCohomology
