/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Adjoin.FG
public import Mathlib.Tactic.Ring
public import Nyll.AbelianVarieties.NeronModels.Endomorphisms
public import Nyll.AbelianVarieties.NeronModels.WeakModel
public import Nyll.SchemeTheory.LocalGeometry.DVRStalks
public import Nyll.SchemeTheory.Morphisms.PropernessCriteria
public import Nyll.SchemeTheory.BaseChange.PullbackIsomorphisms

/-!
# Finite families of models with prescribed generic fiber

Open generic-fiber charts are completed by gluing. Bounded coordinate subalgebras
then give a finite family of flat models catching all ramification-index-one points.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_isOpenImmersion_model_isIso_genericFibre_of_isOpenImmersion_chart.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.GenericFibreCompletion

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

namespace ChartCompletion

section Main

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K))
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R))
    (q : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsOpenImmersion q.1]

/-- The span gluing the original chart to the prescribed generic fiber. -/
noncomputable def F : WidePushoutShape Bool ⥤ Scheme.{u} :=
  WidePushoutShape.wideSpan (pullback f (specGenericFibreInclusion R K))
    (fun b : Bool => bif b then Y else XK)
    (fun b => match b with
      | true => pullback.fst f (specGenericFibreInclusion R K)
      | false => q.1)

scoped instance F_map_isOpenImmersion : ∀ {i j : WidePushoutShape Bool} (a : i ⟶ j),
    IsOpenImmersion ((F K gK f q).map a) := by
  rintro i j ⟨⟩
  · exact inferInstanceAs (IsOpenImmersion (𝟙 _))
  · rename_i b
    cases b
    · exact inferInstanceAs (IsOpenImmersion q.1)
    · exact inferInstanceAs (IsOpenImmersion (pullback.fst f (specGenericFibreInclusion R K)))

/-- The model obtained by attaching the full generic fiber. -/
noncomputable def Y' : Scheme.{u} := colimit (F K gK f q)

/-- The original chart embedded in the completed model. -/
noncomputable def j : Y ⟶ Y' K gK f q := colimit.ι (F K gK f q) (some true)
/-- The prescribed generic fiber embedded in the completed model. -/
noncomputable def jX : XK ⟶ Y' K gK f q := colimit.ι (F K gK f q) (some false)
/-- The common generic chart embedded in the completed model. -/
noncomputable def j0 : pullback f (specGenericFibreInclusion R K) ⟶ Y' K gK f q :=
    colimit.ι (F K gK f q) none

scoped instance : IsOpenImmersion (j K gK f q) :=
    inferInstanceAs (IsOpenImmersion (colimit.ι (F K gK f q) (some true)))
scoped instance : IsOpenImmersion (jX K gK f q) :=
    inferInstanceAs (IsOpenImmersion (colimit.ι (F K gK f q) (some false)))

theorem fst_j : pullback.fst f (specGenericFibreInclusion R K) ≫ j K gK f q = j0 K gK f q :=
  colimit.w (F K gK f q) (WidePushoutShape.Hom.init true)

theorem q_jX : q.1 ≫ jX K gK f q = j0 K gK f q :=
  colimit.w (F K gK f q) (WidePushoutShape.Hom.init false)

/-- The structure morphism of the completed model. -/
noncomputable def f' : Y' K gK f q ⟶ Spec (CommRingCat.of R) :=
  colimit.desc (F K gK f q)
    (WidePushoutShape.mkCocone
      (pullback.fst f (specGenericFibreInclusion R K) ≫ f)
      (fun b => match b with
        | true => f
        | false => gK ≫ specGenericFibreInclusion R K)
      (by
        rintro ⟨⟩
        · change q.1 ≫ gK ≫ specGenericFibreInclusion R K = pullback.fst f _ ≫ f
          rw [← Category.assoc, q.2, pullback.condition]
        · rfl))

theorem j_f' : j K gK f q ≫ f' K gK f q = f :=
  colimit.ι_desc _ _

theorem jX_f' : jX K gK f q ≫ f' K gK f q = gK ≫ specGenericFibreInclusion R K :=
  colimit.ι_desc _ _

theorem cover (y : ↥(Y' K gK f q)) :
    y ∈ Set.range (j K gK f q).base ∨ y ∈ Set.range (jX K gK f q).base := by
  obtain ⟨i, x, hx⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (F K gK f q) y
  rcases i with _ | _ | _
  · change ↥(pullback f (specGenericFibreInclusion R K) : Scheme.{u}) at x
    left
    refine ⟨(pullback.fst f (specGenericFibreInclusion R K)).base x, ?_⟩
    rw [← Scheme.Hom.comp_apply]
    rw [fst_j]; exact hx
  · right; exact ⟨x, hx⟩
  · left; exact ⟨x, hx⟩

local notation "ιK" => specGenericFibreInclusion R K

theorem j0_f' : j0 K gK f q ≫ f' K gK f q = pullback.fst f ιK ≫ f := by
  rw [← fst_j, Category.assoc, j_f']

theorem closedPoint_not_mem_range : IsLocalRing.closedPoint R ∉ Set.range
    (specGenericFibreInclusion R K).base := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  rw [range_specGenericFibreInclusion_eq_basicOpen R K hϖ]
  intro h
  have h' : ϖ ∉ (IsLocalRing.closedPoint R).asIdeal := (PrimeSpectrum.mem_basicOpen ϖ _).mp h
  exact h' ((IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit)

theorem lft [LocallyOfFiniteType gK] [LocallyOfFiniteType f] : LocallyOfFiniteType
    (f' K gK f q) := by
  have sourceLocal (P : MorphismProperty Scheme.{u})
      (Q : ∀ {A B : Type u} [CommRing A] [CommRing B], (A →+* B) → Prop)
      [HasRingHomProperty P Q] : IsZariskiLocalAtSource P := inferInstance
  have : IsZariskiLocalAtSource @LocallyOfFiniteType.{u} := sourceLocal _ RingHom.FiniteType
  let C : (Y' K gK f q).OpenCover := Scheme.IsLocallyDirected.openCover (F K gK f q)
  apply IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType.{u}) C
  rintro (_ | _ | _)
  · change LocallyOfFiniteType (j0 K gK f q ≫ f' K gK f q)
    rw [j0_f']; infer_instance
  · change LocallyOfFiniteType (jX K gK f q ≫ f' K gK f q)
    rw [jX_f']; infer_instance
  · change LocallyOfFiniteType (j K gK f q ≫ f' K gK f q)
    rw [j_f']; infer_instance

theorem smooth (hgK : Smooth gK) (hf : Smooth f) : Smooth (f' K gK f q) := by
  have sourceLocal (P : MorphismProperty Scheme.{u})
      (Q : ∀ {A B : Type u} [CommRing A] [CommRing B], (A →+* B) → Prop)
      [HasRingHomProperty P Q] : IsZariskiLocalAtSource P := inferInstance
  have : IsZariskiLocalAtSource @Smooth.{u} := sourceLocal _ RingHom.Smooth
  let C : (Y' K gK f q).OpenCover := Scheme.IsLocallyDirected.openCover (F K gK f q)
  apply IsZariskiLocalAtSource.of_openCover (P := @Smooth.{u}) C
  rintro (_ | _ | _)
  · change Smooth (j0 K gK f q ≫ f' K gK f q)
    rw [j0_f']; infer_instance
  · change Smooth (jX K gK f q ≫ f' K gK f q)
    rw [jX_f']; infer_instance
  · change Smooth (j K gK f q ≫ f' K gK f q)
    rw [j_f']; infer_instance

theorem qc [QuasiCompact gK] [QuasiCompact f] : QuasiCompact (f' K gK f q) := by
  have : CompactSpace ↥Y := QuasiCompact.compactSpace_of_compactSpace f
  have : CompactSpace ↥XK := QuasiCompact.compactSpace_of_compactSpace gK
  have : CompactSpace ↥(Y' K gK f q) := by
    constructor
    have h : Set.range (j K gK f q).base ∪ Set.range (jX K gK f q).base = Set.univ :=
      Set.eq_univ_of_forall fun y => cover K gK f q y
    rw [← h]
    exact (isCompact_range (j K gK f q).base.hom.continuous).union
      (isCompact_range (jX K gK f q).base.hom.continuous)
  infer_instance

theorem special (y : ↥(Y' K gK f q)) (hy : (f' K gK f q).base y = IsLocalRing.closedPoint R) :
    y ∈ Set.range (j K gK f q).base := by
  rcases cover K gK f q y with h | ⟨x, hx⟩
  · exact h
  · exfalso
    apply closedPoint_not_mem_range (R := R) K
    refine ⟨gK.base x, ?_⟩
    rw [← hy, ← hx, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, jX_f']

/-- The generic-fiber map induced by the attached generic chart. -/
noncomputable def eInv : XK ⟶ pullback (f' K gK f q) ιK :=
  pullback.lift (jX K gK f q) gK (jX_f' K gK f q)

theorem eInv_fst : eInv K gK f q ≫ pullback.fst (f' K gK f q) ιK = jX K gK f q :=
    pullback.lift_fst _ _ _
theorem eInv_snd : eInv K gK f q ≫ pullback.snd (f' K gK f q) ιK = gK := pullback.lift_snd _ _ _

scoped instance : IsOpenImmersion (eInv K gK f q) := by
  have : IsOpenImmersion (eInv K gK f q ≫ pullback.fst (f' K gK f q) ιK) := by
    rw [eInv_fst]; infer_instance
  exact IsOpenImmersion.of_comp _ (pullback.fst (f' K gK f q) ιK)

theorem eInv_surjective : Function.Surjective (eInv K gK f q).base := by
  intro z
  have key : ∀ x : ↥XK, (jX K gK f q).base x = (pullback.fst (f' K gK f q) ιK).base z →
      ∃ x' : ↥XK, (eInv K gK f q).base x' = z := by
    intro x hx
    refine ⟨x, (pullback.fst (f' K gK f q) ιK).isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, eInv_fst]
    exact hx
  rcases cover K gK f q ((pullback.fst (f' K gK f q) ιK).base z) with ⟨y, hy⟩ | ⟨x, hx⟩
  · have hyK : y ∈ Set.range (pullback.fst f ιK).base := by
      rw [Scheme.Pullback.range_fst]
      refine ⟨(pullback.snd (f' K gK f q) ιK).base z, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply, ← hy,
        ← Scheme.Hom.comp_apply, j_f']
    obtain ⟨w, rfl⟩ := hyK
    apply key (q.1.base w)
    rw [← hy, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, q_jX, fst_j]
  · exact key x hx

scoped instance : IsIso (eInv K gK f q) :=
  (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, ⟨eInv_surjective K gK f q⟩⟩

/-- The identification of the completed generic fiber with the prescribed one. -/
noncomputable def e : SchemeHomOver (pullback.snd (f' K gK f q) ιK) gK :=
  ⟨inv (eInv K gK f q), by rw [IsIso.inv_comp_eq, eInv_snd]⟩

scoped instance : IsIso (e K gK f q).1 := inferInstanceAs (IsIso (inv (eInv K gK f q)))

theorem comp_e :
    schemeHomOverComp (genericFibreRestrict R K (f' K gK f q) f ⟨j K gK f q,
        j_f' K gK f q⟩) (e K gK f q) = q := by
  apply Subtype.ext
  rw [schemeHomOverComp_coe]
  change (genericFibreRestrict R K (f' K gK f q) f ⟨j K gK f q,
      j_f' K gK f q⟩).1 ≫ inv (eInv K gK f q) = q.1
  rw [IsIso.comp_inv_eq]
  apply pullback.hom_ext
  · rw [Category.assoc, eInv_fst, q_jX, ← fst_j]
    exact pullback.lift_fst _ _ _
  · rw [Category.assoc, eInv_snd, q.2]
    exact pullback.lift_snd _ _ _

theorem isPullback : IsPullback (pullback.fst f ιK) q.1 (j K gK f q) (jX K gK f q) := by
  have hw : pullback.fst f ιK ≫ j K gK f q = q.1 ≫ jX K gK f q := by rw [fst_j, q_jX]
  let s : pullback f ιK ⟶ pullback (j K gK f q) (jX K gK f q) :=
      pullback.lift (pullback.fst f ιK) q.1 hw
  have hr : pullback.fst (j K gK f q) (jX K gK f q) ≫ f =
      (pullback.snd (j K gK f q) (jX K gK f q) ≫ gK) ≫ ιK := by
    rw [Category.assoc, ← jX_f' K gK f q, ← Category.assoc, ← pullback.condition,
        Category.assoc, j_f']
  let r : pullback (j K gK f q) (jX K gK f q) ⟶ pullback f ιK :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ gK) hr
  have hrq : r ≫ q.1 = pullback.snd (j K gK f q) (jX K gK f q) := by
    rw [← cancel_mono (jX K gK f q), Category.assoc, q_jX, ← fst_j, ← Category.assoc,
        pullback.lift_fst,
      pullback.condition]
  have hsr : s ≫ r = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.id_comp, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd,
        Category.id_comp, q.2]
  have hrs : r ≫ s = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.id_comp, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp, hrq]
  have : IsIso s := ⟨⟨r, hsr, hrs⟩⟩
  exact IsPullback.of_iso_pullback ⟨hw⟩ (asIso s) (pullback.lift_fst _ _ _)
      (pullback.lift_snd _ _ _)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [IsOpenImmersion q.1] in
theorem graph_isClosedImmersion [IsSeparated gK] (w : pullback.fst f ιK ≫ f = q.1 ≫ gK ≫ ιK) :
    IsClosedImmersion (pullback.lift (pullback.fst f ιK) q.1 w : pullback f ιK ⟶ pullback f (gK ≫
        ιK)) := by
  let Γ : pullback f ιK ⟶ pullback (q.1 ≫ gK) gK := pullback.lift (𝟙 _) q.1 (Category.id_comp _)
  have hΓ : IsClosedImmersion Γ := inferInstance
  let c : pullback (q.1 ≫ gK) gK ≅ pullback (pullback.snd f ιK) gK := pullback.congrHom q.2 rfl
  let G : pullback (pullback.snd f ιK) gK ≅ pullback f (gK ≫ ιK) :=
      pullbackLeftPullbackSndIso f ιK gK
  have heq : pullback.lift (pullback.fst f ιK) q.1 w = Γ ≫ c.hom ≫ G.hom := by
    apply pullback.hom_ext
    · simp only [Γ, c, G, Category.assoc, pullback.lift_fst, pullbackLeftPullbackSndIso_hom_fst,
        pullback.congrHom_hom, pullback.lift_fst_assoc, Category.comp_id, Category.id_comp]
    · simp only [Γ, c, G, Category.assoc, pullback.lift_snd, pullbackLeftPullbackSndIso_hom_snd,
        pullback.congrHom_hom, Category.comp_id]
  rw [heq]
  infer_instance

theorem sep [IsSeparated gK] [IsSeparated f] : IsSeparated (f' K gK f q) :=
  AlgebraicGeometry.isSeparated_of_isOpenImmersion_of_isPullback_of_isClosedImmersion_lift
    (f' K gK f q) (j K gK f q) (jX K gK f q) (Set.eq_univ_of_forall fun y => cover K gK f q y)
    f (gK ≫ ιK) (j_f' K gK f q) (jX_f' K gK f q)
    (pullback.fst f ιK) q.1 (isPullback K gK f q) (graph_isClosedImmersion K gK f q _)

end Main

end ChartCompletion

end AbelianVarieties.NOSProofs.GenericFibreCompletion

namespace NeronModelInfra

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AbelianVarieties.NOSProofs.GenericFibreCompletion.ChartCompletion

theorem exists_isOpenImmersion_model_isIso_genericFibre_of_isOpenImmersion_chart
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K))
    [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (q : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsOpenImmersion q.1] :
    ∃ (Y' : Scheme.{u}) (f' : Y' ⟶ Spec (CommRingCat.of R)) (j : Y ⟶ Y') (hj : j ≫ f' = f)
      (e : SchemeHomOver (pullback.snd f' (specGenericFibreInclusion R K)) gK),
      IsOpenImmersion j ∧ IsSeparated f' ∧ LocallyOfFiniteType f' ∧ QuasiCompact f' ∧ IsIso e.1 ∧
      (∀ y' : Y', f'.base y' = IsLocalRing.closedPoint R → y' ∈ Set.range j.base) ∧
      schemeHomOverComp (genericFibreRestrict R K f' f ⟨j, hj⟩) e = q ∧
      (Smooth gK → Smooth f → Smooth f') := by
  refine ⟨Y' K gK f q, f' K gK f q, j K gK f q, j_f' K gK f q, e K gK f q, inferInstance,
      sep K gK f q,
    lft K gK f q, qc K gK f q, inferInstance, special K gK f q, comp_e K gK f q,
        fun h₁ h₂ => smooth K gK f q h₁ h₂⟩

end NeronModelInfra
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_modelFamily_finite_catchesIndexOnePoints_of_isProper.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.BoundedModelFamilies

noncomputable section

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra

universe u

namespace BoundedModels

open SchemeTheory.Properness.ValuativeBounds.AlgebraicGeometry
open SchemeTheory.Properness.ValuativeBounds.AlgebraicGeometry.ProperBounded
  (evalHom ofHom_evalHom evalHom_apply eq_specMap_evalHom_comp_fromSpec top_le_preimage_of_mem)

open scoped nonZeroDivisors

section Algebra

variable {R : Type u} [CommRing R] [IsDomain R]
variable {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
variable {A : Type u} [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]

/-- The coordinate subalgebra generated by uniformly scaled generators. -/
def model (s : Set A) (c : R) : Subalgebra R A :=
  Algebra.adjoin R ((fun g => algebraMap R A c * g) '' s)

omit [IsDomain R] in
theorem model_fg {s : Set A} (hs : s.Finite) (c : R) : (model s c).FG :=
  Subalgebra.fg_def.mpr ⟨_, hs.image _, rfl⟩

omit [IsDomain R] in
theorem finiteType_model {s : Set A} (hs : s.Finite) (c : R) : Algebra.FiniteType R (model s c) :=
  (Subalgebra.fg_iff_finiteType _).mp (model_fg hs c)

omit [IsDomain R] in
theorem mul_mem_model {s : Set A} (c : R) {g : A} (hg : g ∈ s) : algebraMap R A c * g ∈ model s c :=
  Algebra.subset_adjoin ⟨g, hg, rfl⟩

omit [IsDomain R] [IsFractionRing R K] in
theorem algebraMap_isUnit_of_ne_zero [FaithfulSMul R K] {r : R} (hr : r ≠ 0) : IsUnit
    (algebraMap R A r) := by
  rw [IsScalarTower.algebraMap_apply R K A]
  exact ((FaithfulSMul.algebraMap_injective R K).ne_iff' (map_zero _) |>.mpr hr).isUnit.map _

theorem exists_mul_mem_model {s : Set A} (hs : Algebra.adjoin K s = ⊤) {c : R} (hc : c ≠ 0)
    (z : A) :
    ∃ r : R, r ≠ 0 ∧ algebraMap R A r * z ∈ model s c := by
  have hz : z ∈ Algebra.adjoin K s := by rw [hs]; exact Algebra.mem_top
  induction hz using Algebra.adjoin_induction with
  | mem x hx => exact ⟨c, hc, mul_mem_model c hx⟩
  | algebraMap k =>
    obtain ⟨n, d, hd0, rfl⟩ := IsFractionRing.div_surjective (A := R) k
    refine ⟨d, nonZeroDivisors.ne_zero hd0, ?_⟩
    by_cases hd : algebraMap R K d = 0
    · exact absurd hd (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd0)
    · have : algebraMap R A d * algebraMap K A (algebraMap R K n / algebraMap R K d) =
        algebraMap R A n := by
        rw [IsScalarTower.algebraMap_apply R K A, IsScalarTower.algebraMap_apply R K A, ← map_mul,
          mul_div_cancel₀ _ hd]
      rw [this]
      exact Subalgebra.algebraMap_mem _ n
  | add x y _ _ hx hy =>
    obtain ⟨r, hr, hx⟩ := hx
    obtain ⟨t, ht, hy⟩ := hy
    refine ⟨r * t, mul_ne_zero hr ht, ?_⟩
    have : algebraMap R A (r * t) * (x + y) =
        algebraMap R A t * (algebraMap R A r * x) + algebraMap R A r * (algebraMap R A t * y) := by
      rw [map_mul]; ring
    rw [this]
    exact add_mem (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ t) hx)
      (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ r) hy)
  | mul x y _ _ hx hy =>
    obtain ⟨r, hr, hx⟩ := hx
    obtain ⟨t, ht, hy⟩ := hy
    refine ⟨r * t, mul_ne_zero hr ht, ?_⟩
    have : algebraMap R A (r * t) * (x * y) = (algebraMap R A r * x) * (algebraMap R A t * y) := by
      rw [map_mul]; ring
    rw [this]
    exact Subalgebra.mul_mem _ hx hy

theorem isLocalization_model {s : Set A} (hs : Algebra.adjoin K s = ⊤) {c : R} (hc : c ≠ 0) :
    IsLocalization ((nonZeroDivisors R).map (algebraMap R (model s c))) A where
  map_units := by
    rintro ⟨_, r, hr, rfl⟩
    change IsUnit (algebraMap (model s c) A (algebraMap R (model s c) r))
    rw [← IsScalarTower.algebraMap_apply]
    exact algebraMap_isUnit_of_ne_zero (K := K) (nonZeroDivisors.ne_zero hr)
  surj := by
    intro z
    obtain ⟨r, hr, hz⟩ := exists_mul_mem_model (K := K) hs hc z
    refine ⟨⟨⟨_, hz⟩, ⟨algebraMap R (model s c) r, r, mem_nonZeroDivisors_of_ne_zero hr, rfl⟩⟩, ?_⟩
    change z * algebraMap (model s c) A (algebraMap R (model s c) r) = algebraMap R A r * z
    rw [← IsScalarTower.algebraMap_apply, mul_comm]
  exists_of_eq := by
    intro x y h
    exact ⟨1, by rw [Subtype.ext (show (x : A) = y from h)]⟩

include K in
theorem isTorsionFree_model (s : Set A) (c : R) : Module.IsTorsionFree R (model s c) := by
  have hA : Module.IsTorsionFree R A := by
    refine ⟨fun r hr => ?_⟩
    have hr0 : r ≠ 0 := by rintro rfl; exact not_isRegular_zero hr
    intro x y hxy
    have hu := algebraMap_isUnit_of_ne_zero (K := K) (A := A) hr0
    have : algebraMap R A r * x = algebraMap R A r * y := by simpa only [Algebra.smul_def] using hxy
    exact hu.mul_left_cancel this
  exact Function.Injective.moduleIsTorsionFree (model s c).val Subtype.val_injective
      (fun _ _ => rfl)

include K in
omit [IsDomain R] in
theorem flat_model [IsDedekindDomain R] (s : Set A) (c : R) : Module.Flat R (model s c) := by
  have : Module.IsTorsionFree R (model s c) := isTorsionFree_model (K := K) s c
  infer_instance

omit [IsDomain R] in
theorem exists_lift_model {s : Set A} (c : R)
    {R' K' : Type u} [CommRing R'] [CommRing K'] [Algebra R R'] [Algebra R' K'] [Algebra R K']
    [IsScalarTower R R' K'] (hinj : Function.Injective (algebraMap R' K'))
    (ψ : A →ₐ[R] K') (hψ : ∀ g ∈ s, ψ (algebraMap R A c * g) ∈ Set.range (algebraMap R' K')) :
    ∃ χ : model s c →ₐ[R] R', ∀ b : model s c, algebraMap R' K' (χ b) = ψ b := by
  let φ : R' →ₐ[R] K' := IsScalarTower.toAlgHom R R' K'
  let T : Subalgebra R K' := φ.range
  have hle : (model s c).map ψ ≤ T := by
    rw [model, AlgHom.map_adjoin]
    refine Algebra.adjoin_le ?_
    rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    obtain ⟨y, hy⟩ := hψ g hg
    exact ⟨y, hy⟩
  have hmem : ∀ b : model s c, ψ b ∈ Set.range (algebraMap R' K') := by
    intro b
    obtain ⟨y, hy⟩ := hle ⟨b, b.2, rfl⟩
    exact ⟨y, hy⟩
  let e : R' ≃ₐ[R] T := AlgEquiv.ofInjective φ hinj
  let ψT : model s c →ₐ[R] T := (ψ.comp (model s c).val).codRestrict T hmem
  refine ⟨e.symm.toAlgHom.comp ψT, ?_⟩
  intro b
  exact congrArg (fun z : T => (z : K')) (e.apply_symm_apply (ψT b))

end Algebra

section Coordinates

variable {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K]
variable {AK : Scheme.{u}} (gK : AK ⟶ Spec (CommRingCat.of K))

/-- The scalar map on sections induced by the structure morphism. -/
def algK (V : AK.Opens) : K →+* Γ(AK, V) :=
  (gK.appLE ⊤ V le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

theorem ofHom_algK (V : AK.Opens) :
    CommRingCat.ofHom (algK K gK V) = (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
        gK.appLE ⊤ V le_top :=
  rfl

/-- The coordinate ring indexed by its base fields and structure morphism. -/
def Coord (_R K : Type u) [Field K] {AK : Scheme.{u}} (_gK : AK ⟶ Spec (CommRingCat.of K))
    (V : AK.Opens) : Type u :=
  Γ(AK, V)

variable (V : AK.Opens)

scoped instance : CommRing (Coord R K gK V) := inferInstanceAs (CommRing Γ(AK, V))

scoped instance : Algebra K (Coord R K gK V) := (algK K gK V).toAlgebra

scoped instance : Algebra R (Coord R K gK V) := ((algK K gK V).comp (algebraMap R K)).toAlgebra

scoped instance : IsScalarTower R K (Coord R K gK V) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)

theorem fromSpec_comp_eq {V : AK.Opens} (hV : IsAffineOpen V) :
    hV.fromSpec ≫ gK = Spec.map (CommRingCat.ofHom (algK K gK V)) :=
  ProperBounded.fromSpec_comp_eq gK hV

theorem finiteType_algK [LocallyOfFiniteType gK] {V : AK.Opens} (hV : IsAffineOpen V) :
    (algK K gK V).FiniteType := by
  have h1 : (gK.appLE ⊤ V le_top).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType gK inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V,
        hV⟩ le_top
  exact h1.comp (RingHom.FiniteType.of_surjective _
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm.surjective)

variable {K gK}

theorem evalHom_comp_algK {L : Type u} [CommRing L] [Algebra K L] (a : Spec (CommRingCat.of L) ⟶ AK)
    (ha : a ≫ gK = Spec.map (CommRingCat.ofHom (algebraMap K L))) (V : AK.Opens) (h : ⊤ ≤ a ⁻¹ᵁ V) :
    (evalHom a V h).comp (algK K gK V) = algebraMap K L :=
  ProperBounded.evalHom_comp_algK
    gK (algebraMap K L) a ha V h

end Coordinates

section Family

variable {R : Type u} [CommRing R] [IsDomain R]
variable (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
variable {AK : Scheme.{u}} (gK : AK ⟶ Spec (CommRingCat.of K))
variable {ι : Type u} (U : ι → AK.Opens) (s : ∀ i, Finset Γ(AK, U i)) (c : R)

variable (R) in
/-- The chosen finite generators viewed in the indexed coordinate ring. -/
def gens (i : ι) : Set (Coord R K gK (U i)) := ((s i : Set Γ(AK, U i)) : Set Γ(AK, U i))

omit [CommRing R] [IsDomain R] [Algebra R K] [IsFractionRing R K] in
variable (R) in
theorem mem_gens_iff (i : ι) (g : Γ(AK, U i)) : (g : Coord R K gK
    (U i)) ∈ gens R K gK U s i ↔ g ∈ s i :=
  Finset.mem_coe

/-- The scaled coordinate subalgebra for a member of the family. -/
def modelRing (i : ι) : Subalgebra R (Coord R K gK (U i)) :=
  model (A := Coord R K gK (U i)) (gens R K gK U s i) c

/-- The affine model defined by a scaled coordinate subalgebra. -/
def memberX (i : ι) : Scheme.{u} := Spec (CommRingCat.of (modelRing K gK U s c i))

/-- The structure morphism of an affine model in the family. -/
def memberStr (i : ι) : memberX K gK U s c i ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (modelRing K gK U s c i)))

/-- The generic coordinate scheme mapped to its affine model. -/
def coordToMember (i : ι) : Spec Γ(AK, U i) ⟶ memberX K gK U s c i :=
  Spec.map (CommRingCat.ofHom (algebraMap (modelRing K gK U s c i) (Coord R K gK (U i))))

/-- The coordinate-scheme structure morphism over the fraction field. -/
def coordStr (i : ι) : Spec Γ(AK, U i) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algK K gK (U i)))

variable {K gK U s c}

theorem isPullback_member (hs : ∀ i, Algebra.adjoin K (gens R K gK U s i) = ⊤)
    (hc : c ≠ 0) (i : ι) :
    IsPullback (coordToMember K gK U s c i) (coordStr K gK U i)
      (memberStr K gK U s c i) (specGenericFibreInclusion R K) := by
  have : IsLocalization ((nonZeroDivisors R).map (algebraMap R (modelRing K gK U s c i)))
      (Coord R K gK (U i)) := isLocalization_model (K := K) (hs i) hc
  have H : (algebraMap K (Coord R K gK (U i))).comp (algebraMap R K) =
      (algebraMap (modelRing K gK U s c i) (Coord R K gK (U i))).comp
        (algebraMap R (modelRing K gK U s c i)) := by
    ext r
    exact (IsScalarTower.algebraMap_apply R (modelRing K gK U s c i) (Coord R K gK (U i)) r)
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isLocalization (algebraMap R (modelRing K gK U s c i))
      (algebraMap K (Coord R K gK (U i))) H (nonZeroDivisors R))

theorem mono_coordToMember (hs : ∀ i, Algebra.adjoin K (gens R K gK U s i) = ⊤)
    (hc : c ≠ 0) (i : ι) : Mono (coordToMember K gK U s c i) := by
  have : IsLocalization ((nonZeroDivisors R).map (algebraMap R (modelRing K gK U s c i)))
      (Coord R K gK (U i)) := isLocalization_model (K := K) (hs i) hc
  have : IsPreimmersion (coordToMember K gK U s c i) :=
    IsPreimmersion.of_isLocalization (S := Coord R K gK (U i))
      ((nonZeroDivisors R).map (algebraMap R (modelRing K gK U s c i)))
  infer_instance

variable (hU : ∀ i, IsAffineOpen (U i))
variable (hs : ∀ i, Algebra.adjoin K (gens R K gK U s i) = ⊤) (hc : c ≠ 0)

/-- The open generic-fiber chart of a member of the family. -/
def memberChart (i : ι) :
    SchemeHomOver (pullback.snd (memberStr K gK U s c i) (specGenericFibreInclusion R K)) gK :=
  ⟨(isPullback_member hs hc i).isoPullback.inv ≫ (hU i).fromSpec, by
    rw [Category.assoc, fromSpec_comp_eq K gK (hU i)]
    exact (isPullback_member hs hc i).isoPullback_inv_snd⟩

omit [IsDomain R] [IsFractionRing R K] in
theorem coordStr_eq (i : ι) : Spec.map (CommRingCat.ofHom (algK K gK (U i))) =
    coordStr K gK U i := rfl

scoped instance isOpenImmersion_memberChart (i : ι) : IsOpenImmersion
    (memberChart hU hs hc i).1 := by
  change IsOpenImmersion ((isPullback_member hs hc i).isoPullback.inv ≫ (hU i).fromSpec)
  infer_instance

/-- The finite family of affine models supplied by the chosen coordinate data. -/
def family : ModelFamily R K gK where
  ι := ι
  X := memberX K gK U s c
  str := memberStr K gK U s c
  chart := memberChart hU hs hc
  isOpenImmersion_chart := isOpenImmersion_memberChart hU hs hc

omit [IsDomain R] [IsFractionRing R K] in
theorem isAffine_memberX (i : ι) : IsAffine (memberX K gK U s c i) := by
  delta memberX; infer_instance

omit [IsDomain R] in
theorem flat_memberStr [IsDedekindDomain R] (i : ι) : Flat (memberStr K gK U s c i) := by
  have := flat_model (K := K) (A := Coord R K gK (U i)) (gens R K gK U s i) c
  delta memberStr
  exact HasRingHomProperty.Spec_iff.mpr (RingHom.flat_algebraMap_iff.mpr this)

omit [IsDomain R] [IsFractionRing R K] in
theorem locallyOfFiniteType_memberStr (i : ι) : LocallyOfFiniteType (memberStr K gK U s c i) := by
  have := finiteType_model (A := Coord R K gK (U i)) (s := gens R K gK U s i) (s i).finite_toSet c
  delta memberStr
  exact HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr this)

theorem catchesIndexOnePoints_family [IsLocalRing R]
    (hbd : ∀ (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V] [Algebra R V]
        (L : Type u) [Field L] [Algebra V L] [IsFractionRing V L] [Algebra R L]
            [IsScalarTower R V L]
        [Algebra K L] [IsScalarTower R K L]
        (a : Spec (CommRingCat.of L) ⟶ AK), a ≫ gK = Spec.map (CommRingCat.ofHom (algebraMap K L)) →
        ∃ (i : ι) (h : ⊤ ≤ a ⁻¹ᵁ U i), ∀ g ∈ s i,
          algebraMap R L c * (Scheme.ΓSpecIso (CommRingCat.of L)).hom (a.appLE (U i) ⊤ h g) ∈
            Set.range (algebraMap V L)) :
    (family hU hs hc).CatchesIndexOnePoints := by
  intro R' _ _ _ _ _ K' _ _ _ _ _ _ _ _ a
  obtain ⟨i, h, hg⟩ := hbd R' K' a.1 a.2
  let A := Coord R K gK (U i)
  let ψr : A →+* K' := evalHom a.1 (U i) h
  have hψK : ψr.comp (algK K gK (U i)) = algebraMap K K' := evalHom_comp_algK a.1 a.2 (U i) h
  have hψR : ∀ r : R, ψr (algebraMap R A r) = algebraMap R K' r := fun r =>
    calc ψr (algebraMap R A r) = (ψr.comp (algK K gK (U i))) (algebraMap R K r) := rfl
      _ = algebraMap K K' (algebraMap R K r) := by rw [hψK]
      _ = algebraMap R K' r := (IsScalarTower.algebraMap_apply R K K' r).symm
  let ψ : A →ₐ[R] K' := { ψr with commutes' := hψR }
  have hψ : ∀ g ∈ gens R K gK U s i, ψ (algebraMap R A c * g) ∈ Set.range (algebraMap R' K') := by
    intro g hgs
    have := hg g ((mem_gens_iff R K gK U s i g).mp hgs)
    rwa [map_mul, show ψ (algebraMap R A c) = algebraMap R K' c from hψR c]
  obtain ⟨χ, hχ⟩ := exists_lift_model c (IsFractionRing.injective R' K') ψ hψ
  have hχR : (χ.toRingHom : modelRing K gK U s c i →+* R').comp (algebraMap R
      (modelRing K gK U s c i)) =
      algebraMap R R' :=
    χ.comp_algebraMap
  let x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R')))
      (memberStr K gK U s c i) :=
    ⟨Spec.map (CommRingCat.ofHom (χ.toRingHom : modelRing K gK U s c i →+* R')), by
      change Spec.map _ ≫ Spec.map _ = _
      rw [← Spec.map_comp]
      change Spec.map (CommRingCat.ofHom (χ.toRingHom.comp (algebraMap R
        (modelRing K gK U s c i)))) = _
      exact congrArg (fun φ : R →+* R' => Spec.map (CommRingCat.ofHom φ)) hχR⟩
  refine ⟨i, x, ?_⟩
  apply Subtype.ext
  change (pointGenericFibre (K := K) (K' := K') x).1 ≫
      (isPullback_member hs hc i).isoPullback.inv ≫ (hU i).fromSpec = a.1
  rw [eq_specMap_evalHom_comp_fromSpec a.1 (hU i) h, ← Category.assoc]
  congr 1
  have : Mono (coordToMember K gK U s c i) := mono_coordToMember hs hc i
  rw [← cancel_mono (coordToMember K gK U s c i), Category.assoc,
    (isPullback_member hs hc i).isoPullback_inv_fst, pointGenericFibre_coe_comp_fst]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext b
  exact hχ b

end Family

end BoundedModels

end
end AbelianVarieties.NOSProofs.BoundedModelFamilies

namespace NeronModelInfra

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AbelianVarieties.NOSProofs.BoundedModelFamilies.BoundedModels

theorem exists_modelFamily_finite_catchesIndexOnePoints_of_isProper
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {AK : Scheme.{u}} (gK : AK ⟶ Spec (CommRingCat.of K)) [IsProper gK] :
    ∃ M : ModelFamily R K gK, Finite M.ι ∧
      (∀ i, IsAffine (M.X i) ∧ IsSeparated (M.str i) ∧ Flat (M.str i) ∧
        LocallyOfFiniteType (M.str i) ∧ QuasiCompact (M.str i)) ∧
      M.CatchesIndexOnePoints := by
  have : CompactSpace AK := QuasiCompact.compactSpace_of_compactSpace gK
  let 𝒱 := AK.affineCover.finiteSubcover
  let U : 𝒱.I₀ → AK.Opens := fun j => (𝒱.f j).opensRange
  have hU : ∀ j, IsAffineOpen (U j) := fun j => isAffineOpen_opensRange (𝒱.f j)
  have hcov : ⨆ j, U j = ⊤ := 𝒱.iSup_opensRange
  have hgen : ∀ j, ∃ t : Finset (Coord R K gK (U j)),
      Algebra.adjoin K (t : Set (Coord R K gK (U j))) = ⊤ := by
    intro j
    have hft : Algebra.FiniteType K (Coord R K gK (U j)) := finiteType_algK K gK (hU j)
    exact hft.out
  choose s hs using hgen
  obtain ⟨c, hc, hbd⟩ :=
    AlgebraicGeometry.exists_ne_zero_forall_exists_mul_appLE_mem_range_algebraMap_of_isProper
        (R := R) K gK U
      hcov s
  have hs' : ∀ j, Algebra.adjoin K (gens R K gK U s j) = ⊤ := fun j => hs j
  refine ⟨family hU hs' hc, ?_, ?_, catchesIndexOnePoints_family hU hs' hc hbd⟩
  · change Finite 𝒱.I₀
    infer_instance
  · intro j
    refine ⟨isAffine_memberX j, ?_, flat_memberStr j, locallyOfFiniteType_memberStr j, ?_⟩
    · change IsSeparated (Spec.map _)
      infer_instance
    · change QuasiCompact (Spec.map _)
      infer_instance

end
end NeronModelInfra
end
