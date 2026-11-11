/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.Topology.Sober
public import Nyll.SchemeTheory.LocalGeometry.DVRStalks
public import Nyll.AbelianVarieties.NeronModels.Endomorphisms
public import Nyll.AbelianVarieties.NeronModels.OpenExtensions
public import Nyll.AbelianVarieties.NeronModels.StalkExtensions
public import Nyll.AbelianVarieties.NeronModels.WeakModel
public import Nyll.SchemeTheory.Gluing.OpenSubschemes
public import Nyll.SchemeTheory.LocalGeometry.Points
public import Nyll.SchemeTheory.LocalGeometry.OpenIrreducibleComponents
public import Nyll.SchemeTheory.LocalGeometry.IntegralSmooth
public import Nyll.SchemeTheory.LocalGeometry.SmoothNormalStalk

/-! # Separated model covers from extensions of generic fibers -/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_model_openCover_of_forall_isClosedImmersion_pullback_lift.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.ModelGluing

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

namespace Gluing

section OpenGenericFibre

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]

end OpenGenericFibre

section Main

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K))
  {ι : Type u} [Finite ι] [Nonempty ι]
  (Y : ι → Scheme.{u}) (f : ∀ i, Y i ⟶ Spec (CommRingCat.of R))
  (e : ∀ i, SchemeHomOver (pullback.snd (f i) (specGenericFibreInclusion R K)) gK) (he : ∀ i,
    IsIso (e i).1)

/-- Include the common generic fiber into a chosen model. -/
noncomputable def w (i : ι) : XK ⟶ Y i :=
  have : IsIso (e i).1 := he i
  inv (e i).1 ≫ pullback.fst (f i) (specGenericFibreInclusion R K)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [Finite ι] [Nonempty ι] in
include he in
theorem
    e_w (i : ι) :
    (e i).1 ≫ w K gK Y f e he i = pullback.fst (f i) (specGenericFibreInclusion R K) := by
  have : IsIso (e i).1 := he i
  rw [w, IsIso.hom_inv_id_assoc]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [Finite ι] [Nonempty ι] in
theorem w_f (i : ι) : w K gK Y f e he i ≫ f i = gK ≫ specGenericFibreInclusion R K := by
  have : IsIso (e i).1 := he i
  rw [w, Category.assoc, pullback.condition, ← Category.assoc]
  congr 1
  rw [IsIso.inv_comp_eq]
  exact (e i).2.symm

scoped instance isOpenImmersion_w (i : ι) : IsOpenImmersion (w K gK Y f e he i) := by
  have : IsIso (e i).1 := he i
  dsimp only [w]
  infer_instance

end Main

end Gluing

open Gluing in
theorem _root_.NeronModelInfra.exists_model_openCover_of_forall_isClosedImmersion_pullback_lift
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K))
    [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    {ι : Type u} [Finite ι] [Nonempty ι]
    (Y : ι → Scheme.{u}) (f : ∀ i, Y i ⟶ Spec (CommRingCat.of R))
    (hf : ∀ i, Smooth (f i) ∧ IsSeparated (f i) ∧ LocallyOfFiniteType (f i) ∧ QuasiCompact (f i))
    (e : ∀ i, SchemeHomOver (pullback.snd (f i) (specGenericFibreInclusion R K)) gK) (he : ∀ i,
      IsIso (e i).1)
    (hdiag : ∀ i j, i ≠ j → ∀ δ : pullback (e i).1 (e j).1 ⟶ pullback (f i) (f j),
      δ ≫ pullback.fst (f i) (f j) = pullback.fst (e i).1 (e j).1 ≫ pullback.fst (f i)
        (specGenericFibreInclusion R K) →
      δ ≫ pullback.snd (f i) (f j) = pullback.snd (e i).1 (e j).1 ≫ pullback.fst (f j)
        (specGenericFibreInclusion R K) →
      IsClosedImmersion δ) :
    ∃ (X : Scheme.{u}) (g : X ⟶ Spec (CommRingCat.of R))
      (eX : SchemeHomOver (pullback.snd g (specGenericFibreInclusion R K)) gK)
      (j : ∀ i, SchemeHomOver (f i) g),
      Smooth g ∧ IsSeparated g ∧ LocallyOfFiniteType g ∧ QuasiCompact g ∧ IsIso eX.1 ∧
      (∀ i, IsOpenImmersion (j i).1) ∧
      (∀ i, (genericFibreRestrict R K g (f i) (j i)).1 ≫ eX.1 = (e i).1) ∧
      (∀ x : ↥X, ∃ i, x ∈ Set.range (j i).1.base) := by
  classical
  have hI : IsOpenImmersion (specGenericFibreInclusion R K) := inferInstance
  obtain ⟨X, g', hopen, hglue, hcov, hinter, huniv⟩ :=
    AlgebraicGeometry.Scheme.exists_glue_forall_isOpenImmersion_of_forall_isOpenImmersion XK Y (w
      K gK Y f e he)
  have : ∀ i, IsOpenImmersion (g' i) := hopen
  obtain ⟨g, hg, -⟩ := huniv (Spec (CommRingCat.of R)) f (fun i i' => by rw [w_f, w_f])
  obtain ⟨a₀⟩ := (inferInstance : Nonempty ι)
  let h : XK ⟶ X := w K gK Y f e he a₀ ≫ g' a₀
  have hh : ∀ i, w K gK Y f e he i ≫ g' i = h := fun i => hglue i a₀
  have hhg : h ≫ g = gK ≫ specGenericFibreInclusion R K := by
    simp only [h, Category.assoc, hg, w_f]
  have hrange : Set.range h = Set.range (pullback.fst g (specGenericFibreInclusion R K)) := by
    rw [Scheme.Pullback.range_fst]
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      refine ⟨gK z, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hhg]
    · rintro x ⟨t, ht⟩
      have hx : x ∈ ⋃ i, Set.range (g' i).base := by rw [hcov]; trivial
      obtain ⟨i, y, rfl⟩ := Set.mem_iUnion.mp hx
      have hy : y ∈ Set.range (pullback.fst (f i) (specGenericFibreInclusion R K)) := by
        rw [Scheme.Pullback.range_fst]
        refine ⟨t, ?_⟩
        rw [ht, ← Scheme.Hom.comp_apply, hg]
      obtain ⟨z, rfl⟩ := hy
      refine ⟨(e i).1 z, ?_⟩
      rw [← hh i]
      change (g' i) (w K gK Y f e he i ((e i).1 z)) = (g' i) _
      rw [← Scheme.Hom.comp_apply _ (w K gK Y f e he i), e_w]
  let θ := IsOpenImmersion.isoOfRangeEq h (pullback.fst g (specGenericFibreInclusion R K)) hrange
  have hθ : θ.hom ≫ pullback.fst g (specGenericFibreInclusion R K) = h :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hθ2 : θ.hom ≫ pullback.snd g (specGenericFibreInclusion R K) = gK := by
    rw [← cancel_mono (specGenericFibreInclusion R K), Category.assoc, ← pullback.condition,
      ← Category.assoc, hθ, hhg]
  let eX : SchemeHomOver (pullback.snd g (specGenericFibreInclusion R K)) gK :=
    ⟨θ.inv, by rw [← hθ2, Iso.inv_hom_id_assoc]⟩
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers ι Y g' (fun x => by
    have hx : x ∈ ⋃ i, Set.range (g' i).base := by rw [hcov]; trivial
    obtain ⟨i, y, rfl⟩ := Set.mem_iUnion.mp hx
    exact ⟨i, y, rfl⟩)
  have sourceLocal (P : MorphismProperty Scheme.{u})
      (Q : ∀ {A B : Type u} [CommRing A] [CommRing B], (A →+* B) → Prop)
      [HasRingHomProperty P Q] : IsZariskiLocalAtSource P := inferInstance
  have : IsZariskiLocalAtSource @Smooth.{u} := sourceLocal _ RingHom.Smooth
  have : IsZariskiLocalAtSource @LocallyOfFiniteType.{u} := sourceLocal _ RingHom.FiniteType
  have hsm : Smooth g :=
    IsZariskiLocalAtSource.of_openCover (P := @Smooth) 𝒰 fun i => by
      change ι at i
      change Smooth (g' i ≫ g); rw [hg]; exact (hf i).1
  have hlft : LocallyOfFiniteType g :=
    IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType) 𝒰 fun i => by
      change ι at i
      change LocallyOfFiniteType (g' i ≫ g); rw [hg]; exact (hf i).2.2.1
  have hqc : QuasiCompact g := by
    have : CompactSpace ↥X := by
      constructor
      rw [← hcov]
      let : Fintype ι := Fintype.ofFinite ι
      refine isCompact_iUnion fun i => ?_
      have : QuasiCompact (f i) := (hf i).2.2.2
      have : CompactSpace ↥(Y i) := QuasiCompact.compactSpace_of_compactSpace (f i)
      exact isCompact_range (g' i).continuous
    exact quasiCompact_of_compactSpace g
  have hsep : IsSeparated g := by
    refine ⟨?_⟩
    apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion)
      (Scheme.Pullback.openCoverOfLeftRight 𝒰 𝒰 g g)
    rintro ⟨a, b⟩
    change ι at a b
    change IsClosedImmersion (pullback.snd (pullback.diagonal g)
      (pullback.map (g' a ≫ g) (g' b ≫ g) g g (g' a) (g' b) (𝟙 _) (Category.comp_id _)
        (Category.comp_id _)))
    have hw' : pullback.fst (g' a) (g' b) ≫ (g' a ≫ g) = pullback.snd (g' a) (g' b) ≫ (g' b ≫ g)
      := by
      rw [← Category.assoc, pullback.condition, Category.assoc]
    let n : pullback (g' a) (g' b) ⟶ pullback (g' a ≫ g) (g' b ≫ g) :=
      pullback.lift (pullback.fst (g' a) (g' b)) (pullback.snd (g' a) (g' b)) hw'
    have hn : pullback.snd (pullback.diagonal g)
        (pullback.map (g' a ≫ g) (g' b ≫ g) g g (g' a) (g' b) (𝟙 _) (Category.comp_id _)
          (Category.comp_id _)) =
        (pullbackDiagonalMapIdIso (g' a) (g' b) g).hom ≫ n := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, pullbackDiagonalMapIdIso_hom_fst]
      · rw [Category.assoc, pullback.lift_snd, pullbackDiagonalMapIdIso_hom_snd]
    rw [hn]
    suffices hn' : IsClosedImmersion n by infer_instance
    by_cases hab : a = b
    · subst hab
      have hsepa : IsSeparated (g' a ≫ g) := by rw [hg]; exact (hf a).2.1
      have hn2 : n = pullback.fst (g' a) (g' a) ≫ pullback.diagonal (g' a ≫ g) := by
        apply pullback.hom_ext
        · rw [pullback.lift_fst, Category.assoc, pullback.diagonal_fst, Category.comp_id]
        · rw [pullback.lift_snd, Category.assoc, pullback.diagonal_snd, Category.comp_id,
            fst_eq_snd_of_mono_eq]
      rw [hn2]
      infer_instance
    · have hP : IsPullback (w K gK Y f e he a) (w K gK Y f e he b) (g' a) (g' b) := by
        refine (IsOpenImmersion.isPullback (w K gK Y f e he b) (w K gK Y f e he a) (g' b) (g' a)
          (hglue a b) ?_).flip
        ext y
        constructor
        · intro hy
          have hy' : (g' a) y ∈ Set.range (g' a) ∩ Set.range (g' b) := ⟨⟨y, rfl⟩, hy⟩
          rw [hinter a b hab] at hy'
          obtain ⟨z, hz⟩ := hy'
          exact ⟨z, (g' a).isOpenEmbedding.injective (by rwa [← Scheme.Hom.comp_apply])⟩
        · rintro ⟨z, rfl⟩
          change (g' a) ((w K gK Y f e he a) z) ∈ Set.range (g' b)
          have : (g' a) ((w K gK Y f e he a) z) ∈ Set.range (w K gK Y f e he a ≫ g' a) :=
            ⟨z, by rw [Scheme.Hom.comp_apply]⟩
          rw [← hinter a b hab] at this
          exact this.2
      have key : ∀ {fa : Y a ⟶ Spec (CommRingCat.of R)} {fb : Y b ⟶ Spec (CommRingCat.of R)}
          (ha : fa = f a) (hb : fb = f b)
          (hw : w K gK Y f e he a ≫ fa = w K gK Y f e he b ≫ fb),
          IsClosedImmersion (pullback.lift (w K gK Y f e he a) (w K gK Y f e he b) hw : XK ⟶
            pullback fa fb) := by
        intro fa fb ha hb hw
        subst ha hb
        have : IsIso (e a).1 := he a
        have : IsIso (e b).1 := he b
        let δ : pullback (e a).1 (e b).1 ⟶ pullback (f a) (f b) :=
          (pullback.fst (e a).1 (e b).1 ≫ (e a).1) ≫ pullback.lift (w K gK Y f e he a) (w K gK Y f
            e he b) hw
        have hδ : IsClosedImmersion δ := by
          refine hdiag a b hab δ ?_ ?_
          · simp only [δ, Category.assoc, pullback.lift_fst]
            exact congrArg (pullback.fst (e a).1 (e b).1 ≫ ·) (e_w K gK Y f e he a)
          · simp only [δ, Category.assoc, pullback.lift_snd]
            rw [← Category.assoc, pullback.condition, Category.assoc]
            exact congrArg (pullback.snd (e a).1 (e b).1 ≫ ·) (e_w K gK Y f e he b)
        have : pullback.lift (w K gK Y f e he a) (w K gK Y f e he b) hw =
            inv (pullback.fst (e a).1 (e b).1 ≫ (e a).1) ≫ δ := by
          rw [IsIso.eq_inv_comp]
        rw [this]
        infer_instance
      have hm := key (hg a) (hg b)
        (by rw [← Category.assoc, hglue a b, Category.assoc])
      have hn3 : n = hP.isoPullback.inv ≫
          pullback.lift (w K gK Y f e he a) (w K gK Y f e he b)
            (by rw [← Category.assoc, hglue a b, Category.assoc]) := by
        rw [Iso.eq_inv_comp]
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, IsPullback.isoPullback_hom_fst]
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, IsPullback.isoPullback_hom_snd]
      rw [hn3]
      infer_instance
  refine ⟨X, g, eX, fun i => ⟨g' i, hg i⟩, hsm, hsep, hlft, hqc, inferInstance, fun i => hopen i,
    fun i => ?_,
    fun x => ?_⟩
  · change (genericFibreRestrict R K g (f i) ⟨g' i, hg i⟩).1 ≫ θ.inv = (e i).1
    rw [Iso.comp_inv_eq]
    apply pullback.hom_ext
    · rw [genericFibreRestrict_coe_comp_fst, Category.assoc, hθ, ← hh i, ← Category.assoc, e_w]
    · rw [genericFibreRestrict_coe_comp_snd, Category.assoc, hθ2, (e i).2]
  · have hx : x ∈ ⋃ i, Set.range (g' i).base := by rw [hcov]; trivial
    exact Set.mem_iUnion.mp hx

end AbelianVarieties.NOSProofs.ModelGluing
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_finite_maximal_specialFibre_and_existsUnique_specializes_and_exists_opens.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.SpecialFibreComponents

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra

universe u

namespace MaxSpecial

section Top

variable {X : Type u} [TopologicalSpace X]

/-- A generic point of an irreducible component, expressed by specialization. -/
def IsMax (x : X) : Prop := ∀ x' : X, x' ⤳ x → x' = x

theorem isMax_iff_mem_genericPoints [QuasiSober X] [T0Space X] (x : X) :
    IsMax x ↔ x ∈ genericPoints X := by
  constructor
  · intro hx
    obtain ⟨η, hη⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := x))
      isClosed_irreducibleComponent
    have hηx : η ⤳ x := hη.specializes mem_irreducibleComponent
    have := hx η hηx
    subst this
    change closure {η} ∈ irreducibleComponents X
    rw [hη.def]
    exact irreducibleComponent_mem_irreducibleComponents η
  · intro hx x' hx'
    have hZ : closure ({x} : Set X) ∈ irreducibleComponents X := hx
    have hsub : closure ({x} : Set X) ⊆ closure {x'} := by
      rw [← specializes_iff_closure_subset]; exact hx'
    have hle : closure ({x'} : Set X) ≤ closure {x} := hZ.2 isIrreducible_singleton.closure hsub
    have h1 : x' ⤳ x := hx'
    have h2 : x ⤳ x' := specializes_iff_closure_subset.mpr hle
    exact (h1.antisymm h2).eq

theorem finite_isMax [QuasiSober X] [T0Space X] [TopologicalSpace.NoetherianSpace X] :
    Set.Finite {x : X | IsMax x} := by
  have : {x : X | IsMax x} = genericPoints X := by
    ext x; exact isMax_iff_mem_genericPoints x
  rw [this]
  exact genericPoints.finite TopologicalSpace.NoetherianSpace.finite_irreducibleComponents

theorem exists_isMax_specializes [QuasiSober X] [T0Space X] (z : X) : ∃ x : X, IsMax x ∧ x ⤳ z := by
  obtain ⟨η, hη⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := z))
    isClosed_irreducibleComponent
  refine ⟨η, (isMax_iff_mem_genericPoints η).mpr ?_, hη.specializes mem_irreducibleComponent⟩
  change closure {η} ∈ irreducibleComponents X
  rw [hη.def]
  exact irreducibleComponent_mem_irreducibleComponents z

variable (huniq : ∀ x : X, ∀ Z ∈ irreducibleComponents X, x ∈ Z → Z = irreducibleComponent x)

include huniq in
theorem isMax_unique [QuasiSober X] [T0Space X] {x₁ x₂ z : X} (h₁ : IsMax x₁) (h₂ : IsMax x₂)
    (hz₁ : x₁ ⤳ z) (hz₂ : x₂ ⤳ z) : x₁ = x₂ := by
  rw [isMax_iff_mem_genericPoints] at h₁ h₂
  have e₁ := huniq z _ h₁ (specializes_iff_mem_closure.mp hz₁)
  have e₂ := huniq z _ h₂ (specializes_iff_mem_closure.mp hz₂)
  have : closure ({x₁} : Set X) = closure {x₂} := e₁.trans e₂.symm
  exact (isGenericPoint_closure.eq (this ▸ isGenericPoint_closure))

include huniq in
theorem exists_open_isolating [QuasiSober X] [T0Space X] [TopologicalSpace.NoetherianSpace X]
    {x : X} (hx : IsMax x) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ (∀ z ∈ V, x ⤳ z) ∧ (∀ z, x ⤳ z → z ∈ V) := by
  have hxg := (isMax_iff_mem_genericPoints x).mp hx
  have hZ : closure ({x} : Set X) ∈ irreducibleComponents X := hxg
  let B : Set X := ⋃ Z ∈ {Z ∈ irreducibleComponents X | Z ≠ closure {x}}, Z
  have hB : IsClosed B := by
    apply Set.Finite.isClosed_biUnion
    · exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset (fun Z hZ => hZ.1)
    · intro Z hZ; exact isClosed_of_mem_irreducibleComponents _ hZ.1
  refine ⟨Bᶜ, hB.isOpen_compl, ?_, ?_, ?_⟩
  · intro hxB
    obtain ⟨Z, hZmem, hxZ⟩ := Set.mem_iUnion₂.mp hxB
    have := huniq x Z hZmem.1 hxZ
    have := hZmem.2 (this.trans (huniq x _ hZ (subset_closure (Set.mem_singleton x))).symm)
    exact this
  · intro z hz
    have hc : irreducibleComponent z = closure {x} := by
      by_contra hne
      exact hz (Set.mem_iUnion₂.mpr ⟨irreducibleComponent z,
        ⟨irreducibleComponent_mem_irreducibleComponents z, hne⟩,
        mem_irreducibleComponent⟩)
    exact specializes_iff_mem_closure.mpr (hc ▸ mem_irreducibleComponent)
  · intro z hxz hzB
    obtain ⟨Z, hZmem, hzZ⟩ := Set.mem_iUnion₂.mp hzB
    have e1 := huniq z Z hZmem.1 hzZ
    have e2 := huniq z _ hZ (specializes_iff_mem_closure.mp hxz)
    exact hZmem.2 (e1.trans e2.symm)

end Top

section SmoothField

theorem exists_preconnected_nhd {X : Scheme.{u}} [TopologicalSpace.NoetherianSpace X] (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ _root_.IsPreconnected (U : Set X) := by
  let B : Set X := ⋃ Z ∈ {Z ∈ irreducibleComponents X | x ∉ Z}, Z
  have hB : IsClosed B := by
    apply Set.Finite.isClosed_biUnion
    · exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset (fun Z hZ => hZ.1)
    · intro Z hZ; exact isClosed_of_mem_irreducibleComponents _ hZ.1
  refine ⟨⟨Bᶜ, hB.isOpen_compl⟩, fun h => ?_, ?_⟩
  · obtain ⟨Z, hZ, hxZ⟩ := Set.mem_iUnion₂.mp h
    exact hZ.2 hxZ
  · have hcover : (Bᶜ : Set X) = ⋃₀ {S | ∃ Z ∈ irreducibleComponents X, x ∈ Z ∧ S = Z ∩ Bᶜ} := by
      ext z
      constructor
      · intro hz
        refine ⟨irreducibleComponent z ∩ Bᶜ, ⟨irreducibleComponent z,
          irreducibleComponent_mem_irreducibleComponents z, ?_, rfl⟩,
          mem_irreducibleComponent, hz⟩
        by_contra hxZ
        exact hz (Set.mem_iUnion₂.mpr ⟨irreducibleComponent z,
          ⟨irreducibleComponent_mem_irreducibleComponents z, hxZ⟩,
          mem_irreducibleComponent⟩)
      · rintro ⟨S, ⟨Z, -, -, rfl⟩, hzS⟩
        exact hzS.2
    change _root_.IsPreconnected (Bᶜ : Set X)
    rw [hcover]
    apply isPreconnected_sUnion x
    · rintro S ⟨Z, hZ, hxZ, rfl⟩
      exact ⟨hxZ, fun h => (Set.mem_iUnion₂.mp h).elim fun Z' hZ' => hZ'.1.2 hZ'.2⟩
    · rintro S ⟨Z, hZ, hxZ, rfl⟩
      have hZirr : IsPreirreducible Z := hZ.1.isPreirreducible
      have : IsPreirreducible (Z ∩ Bᶜ) := by
        intro u v hu hv ⟨a, ⟨haZ, haB⟩, hau⟩ ⟨b, ⟨hbZ, hbB⟩, hbv⟩
        obtain ⟨c, hcZ, ⟨hcu, hcB⟩, hcv, -⟩ := hZirr (u ∩ Bᶜ) (v ∩ Bᶜ) (hu.inter hB.isOpen_compl)
          (hv.inter hB.isOpen_compl) ⟨a, haZ, hau, haB⟩ ⟨b, hbZ, hbv, hbB⟩
        exact ⟨c, ⟨hcZ, hcB⟩, hcu, hcv⟩
      exact this.isPreconnected

theorem
    isDomain_stalk_of_smooth {k : Type u} [Field k] {X : Scheme.{u}}
    (g : X ⟶ Spec (CommRingCat.of k))
    [Smooth g] [LocallyOfFiniteType g] [CompactSpace X] (x : X) : IsDomain (X.presheaf.stalk x) :=
      by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian g
  have : IsNoetherian X := {}
  obtain ⟨U, hxU, hU⟩ := exists_preconnected_nhd x
  have : PreconnectedSpace (U : Scheme.{u}) := isPreconnected_iff_preconnectedSpace.mp hU
  have : Nonempty (U : Scheme.{u}) := ⟨⟨x, hxU⟩⟩
  have hint : IsIntegral (U : Scheme.{u}) :=
    AlgebraicGeometry.isIntegral_of_smooth_of_preconnectedSpace (U.ι ≫ g)
  let xU : (U : Scheme.{u}) := ⟨x, hxU⟩
  have : IsDomain ((U : Scheme.{u}).presheaf.stalk xU) := inferInstance
  exact Function.Injective.isDomain (U.ι.stalkMap xU).hom
    (ConcreteCategory.injective_of_mono_of_preservesPullback (U.ι.stalkMap xU))

theorem
    unique_component_of_smooth {k : Type u} [Field k] {X : Scheme.{u}}
    (g : X ⟶ Spec (CommRingCat.of k))
    [Smooth g] [LocallyOfFiniteType g] [CompactSpace X] :
    ∀ x : X, ∀ Z ∈ irreducibleComponents X, x ∈ Z → Z = irreducibleComponent x := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian g
  intro x Z hZ hxZ
  exact (AlgebraicGeometry.isOpen_irreducibleComponent_of_isDomain_stalk (isDomain_stalk_of_smooth
    g) x).2 Z hZ hxZ

end SmoothField

theorem main
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) [Smooth f] [LocallyOfFiniteType f]
      [QuasiCompact f] :
    Set.Finite {ξ : Y | f.base ξ = IsLocalRing.closedPoint R ∧
        ∀ y' : Y, y' ⤳ ξ → f.base y' = IsLocalRing.closedPoint R → y' = ξ} ∧
    (∀ y : Y, f.base y = IsLocalRing.closedPoint R →
      ∃! ξ : Y, (f.base ξ = IsLocalRing.closedPoint R ∧
        (∀ y' : Y, y' ⤳ ξ → f.base y' = IsLocalRing.closedPoint R → y' = ξ)) ∧ ξ ⤳ y) ∧
    (∀ ξ : Y, f.base ξ = IsLocalRing.closedPoint R →
      (∀ y' : Y, y' ⤳ ξ → f.base y' = IsLocalRing.closedPoint R → y' = ξ) →
      ∃ V : Y.Opens, ξ ∈ V ∧ (∀ y' : Y, f.base y' ≠ IsLocalRing.closedPoint R → y' ∈ V) ∧
        (∀ y' : Y, y' ∈ V → f.base y' = IsLocalRing.closedPoint R → ξ ⤳ y') ∧
        (∀ y' : Y, f.base y' = IsLocalRing.closedPoint R → ξ ⤳ y' → y' ∈ V)) := by
  set p₀ : (Spec (CommRingCat.of R) : Scheme.{u}) := IsLocalRing.closedPoint R with hp₀
  let Xk : Scheme.{u} := f.fiber p₀
  let ι : Xk ⟶ Y := f.fiberι p₀
  let g : Xk ⟶ Spec (CommRingCat.of ↑((Spec (CommRingCat.of R)).residueField p₀)) :=
    f.fiberToSpecResidueField p₀
  have hemb : Topology.IsEmbedding ι.base := ι.isEmbedding
  have hrange : Set.range ι.base = {y : Y | f.base y = p₀} := by
    change Set.range (f.fiberι p₀) = _
    rw [Scheme.Hom.range_fiberι]; rfl
  have hS : IsClosed {y : Y | f.base y = p₀} := by
    change IsClosed (f.base ⁻¹' {p₀})
    exact IsClosed.preimage f.base.hom.continuous
      ((PrimeSpectrum.isClosed_singleton_iff_isMaximal p₀).mpr (IsLocalRing.maximalIdeal.isMaximal
        R))
  have hcemb : Topology.IsClosedEmbedding ι.base := ⟨hemb, by rw [hrange]; exact hS⟩
  have smoothBaseChange {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S) [Smooth a] :
      Smooth (pullback.snd a b) := inferInstance
  have finiteTypeBaseChange {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
      [LocallyOfFiniteType a] : LocallyOfFiniteType (pullback.snd a b) := inferInstance
  have : Smooth g := smoothBaseChange f ((Spec (CommRingCat.of R)).fromSpecResidueField p₀)
  have : LocallyOfFiniteType g :=
    finiteTypeBaseChange f ((Spec (CommRingCat.of R)).fromSpecResidueField p₀)
  have : IsLocallyNoetherian Xk := LocallyOfFiniteType.isLocallyNoetherian g
  have : IsNoetherian Xk := {}
  have huniq := unique_component_of_smooth g
  have hmem : ∀ {y : Y}, f.base y = p₀ → ∃ x : Xk, ι.base x = y := fun {y} hy => by
    have : y ∈ Set.range ι.base := by rw [hrange]; exact hy
    exact this
  have hbase : ∀ x : Xk, f.base (ι.base x) = p₀ := fun x => by
    have : ι.base x ∈ Set.range ι.base := ⟨x, rfl⟩
    rw [hrange] at this; exact this
  have hspec : ∀ x x' : Xk, ι.base x ⤳ ι.base x' ↔ x ⤳ x' := fun x x' =>
    hemb.isInducing.specializes_iff
  have hdict : ∀ x : Xk, IsMax x ↔
      (f.base (ι.base x) = p₀ ∧ ∀ y' : Y, y' ⤳ ι.base x → f.base y' = p₀ → y' = ι.base x) := by
    intro x
    constructor
    · intro hx
      refine ⟨hbase x, fun y' hy' hy'S => ?_⟩
      obtain ⟨x', rfl⟩ := hmem hy'S
      rw [hx x' ((hspec _ _).mp hy')]
    · rintro ⟨-, hx⟩ x' hx'
      exact hemb.injective (hx _ ((hspec _ _).mpr hx') (hbase x'))
  refine ⟨?_, ?_, ?_⟩
  · apply ((finite_isMax (X := ↥Xk)).image ι.base).subset
    rintro ξ ⟨hξ, hmax⟩
    obtain ⟨x, rfl⟩ := hmem hξ
    exact ⟨x, (hdict x).mpr ⟨hξ, hmax⟩, rfl⟩
  · intro y hy
    obtain ⟨z, rfl⟩ := hmem hy
    obtain ⟨x, hx, hxz⟩ := exists_isMax_specializes z
    refine ⟨ι.base x, ⟨(hdict x).mp hx, (hspec _ _).mpr hxz⟩, ?_⟩
    rintro ξ' ⟨hξ', hξ'z⟩
    obtain ⟨x', rfl⟩ := hmem hξ'.1
    rw [isMax_unique huniq ((hdict x').mpr hξ') hx ((hspec _ _).mp hξ'z) hxz]
  · intro ξ hξ hmax
    obtain ⟨x, rfl⟩ := hmem hξ
    have hx : IsMax x := (hdict x).mpr ⟨hξ, hmax⟩
    obtain ⟨V₀, hV₀, hxV₀, hV₀spec, hspecV₀⟩ := exists_open_isolating huniq hx
    have hC : IsClosed (ι.base '' V₀ᶜ) := hcemb.isClosedMap _ hV₀.isClosed_compl
    refine ⟨⟨(ι.base '' V₀ᶜ)ᶜ, hC.isOpen_compl⟩, ?_, ?_, ?_, ?_⟩
    · rintro ⟨x', hx', hxx'⟩
      exact hx' (hemb.injective hxx' ▸ hxV₀)
    · intro y' hy' hy'C
      obtain ⟨x', -, rfl⟩ := hy'C
      exact hy' (hbase x')
    · intro y' hy'V hy'S
      obtain ⟨z, rfl⟩ := hmem hy'S
      have hz : z ∈ V₀ := by
        by_contra hz; exact hy'V ⟨z, hz, rfl⟩
      exact (hspec _ _).mpr (hV₀spec z hz)
    · intro y' hy'S hξy'
      obtain ⟨z, rfl⟩ := hmem hy'S
      rintro ⟨z', hz', hzz'⟩
      exact hz' (hemb.injective hzz' ▸ hspecV₀ z ((hspec _ _).mp hξy'))

end MaxSpecial

theorem
    _root_.NeronModelInfra.finite_maximal_specialFibre_and_existsUnique_specializes_and_exists_opens
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) [Smooth f] [LocallyOfFiniteType f]
      [QuasiCompact f] :
    Set.Finite {ξ : Y | f.base ξ = IsLocalRing.closedPoint R ∧
        ∀ y' : Y, y' ⤳ ξ → f.base y' = IsLocalRing.closedPoint R → y' = ξ} ∧
    (∀ y : Y, f.base y = IsLocalRing.closedPoint R →
      ∃! ξ : Y, (f.base ξ = IsLocalRing.closedPoint R ∧
        (∀ y' : Y, y' ⤳ ξ → f.base y' = IsLocalRing.closedPoint R → y' = ξ)) ∧ ξ ⤳ y) ∧
    (∀ ξ : Y, f.base ξ = IsLocalRing.closedPoint R →
      (∀ y' : Y, y' ⤳ ξ → f.base y' = IsLocalRing.closedPoint R → y' = ξ) →
      ∃ V : Y.Opens, ξ ∈ V ∧ (∀ y' : Y, f.base y' ≠ IsLocalRing.closedPoint R → y' ∈ V) ∧
        (∀ y' : Y, y' ∈ V → f.base y' = IsLocalRing.closedPoint R → ξ ⤳ y') ∧
        (∀ y' : Y, f.base y' = IsLocalRing.closedPoint R → ξ ⤳ y' → y' ∈ V)) :=
  MaxSpecial.main f

end AbelianVarieties.NOSProofs.SpecialFibreComponents
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_not_mem_closure_image_fst_closure_range_of_forall_not_exists_extension_of_isIntegral.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace NeronModelInfra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra Topology

universe u

theorem
 not_mem_closure_image_fst_closure_range_of_forall_not_exists_extension_of_isIntegral
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K))
    [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    {Y₁ Y₂ : Scheme.{u}} (f₁ : Y₁ ⟶ Spec (CommRingCat.of R)) (f₂ : Y₂ ⟶ Spec (CommRingCat.of R))
    (hf₁ : Smooth f₁ ∧ IsSeparated f₁ ∧ LocallyOfFiniteType f₁ ∧ QuasiCompact f₁)
    (hf₂ : Smooth f₂ ∧ IsSeparated f₂ ∧ LocallyOfFiniteType f₂ ∧ QuasiCompact f₂)
    (e₁ : SchemeHomOver (pullback.snd f₁ (specGenericFibreInclusion R K)) gK) (he₁ :
      IsOpenImmersion e₁.1)
    (e₂ : SchemeHomOver (pullback.snd f₂ (specGenericFibreInclusion R K)) gK) (he₂ : IsIso e₂.1)
    [IsIntegral Y₁]
    (ξ₁ : ↥Y₁) (hξ₁ : f₁.base ξ₁ = IsLocalRing.closedPoint R)
    (hξ₁gen : ∀ y : ↥Y₁, f₁.base y = IsLocalRing.closedPoint R → ξ₁ ⤳ y)
    (hne : ∀ (U : Y₁.Opens), ξ₁ ∈ U → ∀ u : SchemeHomOver (U.ι ≫ f₁) f₂,
      (genericFibreRestrict R K f₂ (U.ι ≫ f₁) u).1 ≫ e₂.1 ≠
        (genericFibreRestrict R K f₁ (U.ι ≫ f₁) ⟨U.ι, rfl⟩).1 ≫ e₁.1)
    (δ : pullback e₁.1 e₂.1 ⟶ pullback f₁ f₂)
    (hδ₁ : δ ≫ pullback.fst f₁ f₂ = pullback.fst e₁.1 e₂.1 ≫ pullback.fst f₁
      (specGenericFibreInclusion R K))
    (hδ₂ : δ ≫ pullback.snd f₁ f₂ = pullback.snd e₁.1 e₂.1 ≫ pullback.fst f₂
      (specGenericFibreInclusion R K)) :
    ξ₁ ∉ closure ((pullback.fst f₁ f₂).base ''
      (closure (Set.range δ.base) ∩
        {q | f₁.base ((pullback.fst f₁ f₂).base q) = IsLocalRing.closedPoint R})) := by
  intro hmem
  obtain ⟨hsm₁, hsep₁, hlft₁, hqc₁⟩ := hf₁
  obtain ⟨hsm₂, hsep₂, hlft₂, hqc₂⟩ := hf₂
  have : IsLocallyNoetherian (pullback f₁ f₂) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f₁ f₂ ≫ f₁)
  have : CompactSpace ↥(pullback f₁ f₂) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst f₁ f₂ ≫ f₁)
  have : IsNoetherian (pullback f₁ f₂) := {}
  have : IsLocallyNoetherian Y₁ := LocallyOfFiniteType.isLocallyNoetherian f₁
  have : CompactSpace ↥Y₁ := QuasiCompact.compactSpace_of_compactSpace f₁
  set Z : Set ↥(pullback f₁ f₂) := closure (Set.range δ.base) ∩
    {q | f₁.base ((pullback.fst f₁ f₂).base q) = IsLocalRing.closedPoint R} with hZdef
  have hZclosed : IsClosed Z := isClosed_closure.inter
    ((IsLocalRing.isClosed_singleton_closedPoint (R := R)).preimage
      (f₁.continuous.comp (pullback.fst f₁ f₂).continuous))
  have hZc : IsConstructible Z :=
    isConstructible_compl.mp
      ((TopologicalSpace.NoetherianSpace.isCompact Zᶜ).isConstructible hZclosed.isOpen_compl)
  obtain ⟨η₀, ⟨hη₀, hη₀k⟩, hη₀₁⟩ :=
    AlgebraicGeometry.mem_image_of_mem_closure_image_of_forall_specializes (pullback.fst f₁ f₂)
      hZc hmem
      (fun q hq => hξ₁gen _ hq.2)
  obtain ⟨hopen, hlocus, hsupp⟩ :=
    NeronModelInfra.isOpenImmersion_toImage_and_range_toImage_and_range_imageInc_of_genericFibre
      K gK f₁ f₂ ⟨hsm₁, hsep₁, hlft₁, hqc₁⟩ ⟨hsm₂, hsep₂, hlft₂, hqc₂⟩ e₁ he₁ e₂ he₂ δ hδ₁ hδ₂
  have hη₀' : η₀ ∈ Set.range δ.imageι.base := by rw [hsupp]; exact hη₀
  obtain ⟨η, rfl⟩ := hη₀'
  have hiso := NeronModelInfra.isIso_stalkMap_imageInc_fst_of_fst_eq K gK f₁ f₂ ⟨hsm₁, hsep₁,
    hlft₁, hqc₁⟩
    ⟨hsm₂, hsep₂, hlft₂, hqc₂⟩ e₁ he₁ e₂ he₂ ξ₁ hξ₁ hξ₁gen δ hδ₁ hδ₂ η hη₀₁
  obtain ⟨U, hU, u, hu⟩ :=
    NeronModelInfra.exists_nhds_extension_of_isIso_stalkMap_imageInc_fst K gK f₁ f₂ ⟨hsm₁, hsep₁,
      hlft₁, hqc₁⟩
      ⟨hsm₂, hsep₂, hlft₂, hqc₂⟩ e₁ he₁ e₂ he₂ ξ₁ hξ₁ δ hδ₁ hδ₂ hopen hlocus η hη₀₁ hiso
  exact hne U hU u hu

end NeronModelInfra
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_not_mem_closure_image_fst_closure_range_of_forall_not_exists_extension.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.LocalNonextension

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra Topology

universe u

namespace GenericRestrictions

variable {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K]
  {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K))
  {Y₁ Y₂ : Scheme.{u}} (f₁ : Y₁ ⟶ Spec (CommRingCat.of R)) (f₂ : Y₂ ⟶ Spec (CommRingCat.of R))

theorem genericFibreRestrict_comp {A B C : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of R)}
    {b : B ⟶ Spec (CommRingCat.of R)} {c : C ⟶ Spec (CommRingCat.of R)}
    (φ : SchemeHomOver a b) (ψ : SchemeHomOver b c) :
    (genericFibreRestrict R K c a (schemeHomOverComp φ ψ)).1 =
      (genericFibreRestrict R K b a φ).1 ≫ (genericFibreRestrict R K c b ψ).1 := by
  apply pullback.hom_ext
  · rw [genericFibreRestrict_coe_comp_fst, Category.assoc, genericFibreRestrict_coe_comp_fst,
      ← Category.assoc, genericFibreRestrict_coe_comp_fst, Category.assoc]
    rfl
  · rw [genericFibreRestrict_coe_comp_snd, Category.assoc, genericFibreRestrict_coe_comp_snd,
      genericFibreRestrict_coe_comp_snd]

theorem genericFibreRestrict_congr {A B : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of R)}
    {b : B ⟶ Spec (CommRingCat.of R)} (φ ψ : SchemeHomOver a b) (h : φ.1 = ψ.1) :
    (genericFibreRestrict R K b a φ).1 = (genericFibreRestrict R K b a ψ).1 := by
  have : φ = ψ := Subtype.ext h
  subst this
  rfl

end GenericRestrictions

open GenericRestrictions in
theorem
    _root_.NeronModelInfra.not_mem_closure_image_fst_closure_range_of_forall_not_exists_extension
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K))
    [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    {Y₁ Y₂ : Scheme.{u}} (f₁ : Y₁ ⟶ Spec (CommRingCat.of R)) (f₂ : Y₂ ⟶ Spec (CommRingCat.of R))
    (hf₁ : Smooth f₁ ∧ IsSeparated f₁ ∧ LocallyOfFiniteType f₁ ∧ QuasiCompact f₁)
    (hf₂ : Smooth f₂ ∧ IsSeparated f₂ ∧ LocallyOfFiniteType f₂ ∧ QuasiCompact f₂)
    (e₁ : SchemeHomOver (pullback.snd f₁ (specGenericFibreInclusion R K)) gK) (he₁ : IsIso e₁.1)
    (e₂ : SchemeHomOver (pullback.snd f₂ (specGenericFibreInclusion R K)) gK) (he₂ : IsIso e₂.1)
    (ξ₁ : ↥Y₁) (hξ₁ : f₁.base ξ₁ = IsLocalRing.closedPoint R)
    (hξ₁gen : ∀ y : ↥Y₁, f₁.base y = IsLocalRing.closedPoint R → ξ₁ ⤳ y)
    (hne : ∀ (U : Y₁.Opens), ξ₁ ∈ U → ∀ u : SchemeHomOver (U.ι ≫ f₁) f₂,
      (genericFibreRestrict R K f₂ (U.ι ≫ f₁) u).1 ≫ e₂.1 ≠
        (genericFibreRestrict R K f₁ (U.ι ≫ f₁) ⟨U.ι, rfl⟩).1 ≫ e₁.1)
    (δ : pullback e₁.1 e₂.1 ⟶ pullback f₁ f₂)
    (hδ₁ : δ ≫ pullback.fst f₁ f₂ = pullback.fst e₁.1 e₂.1 ≫ pullback.fst f₁
      (specGenericFibreInclusion R K))
    (hδ₂ : δ ≫ pullback.snd f₁ f₂ = pullback.snd e₁.1 e₂.1 ≫ pullback.fst f₂
      (specGenericFibreInclusion R K)) :
    ξ₁ ∉ closure ((pullback.fst f₁ f₂).base ''
      (closure (Set.range δ.base) ∩
        {q | f₁.base ((pullback.fst f₁ f₂).base q) = IsLocalRing.closedPoint R})) := by
  intro hmem
  obtain ⟨hsm₁, hsep₁, hlft₁, hqc₁⟩ := hf₁
  have : IsIso e₁.1 := he₁
  have : IsIso e₂.1 := he₂
  have : IsLocallyNoetherian Y₁ := LocallyOfFiniteType.isLocallyNoetherian f₁
  have : CompactSpace ↥Y₁ := QuasiCompact.compactSpace_of_compactSpace f₁
  have : IsNoetherian Y₁ := {}
  have hdom : ∀ x : ↥Y₁, IsDomain (Y₁.presheaf.stalk x) := fun x =>
    (AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing R
      f₁ x).1
  obtain ⟨hUopen, -⟩ := AlgebraicGeometry.isOpen_irreducibleComponent_of_isDomain_stalk hdom ξ₁
  let U₁ : Y₁.Opens := ⟨irreducibleComponent ξ₁, hUopen⟩
  have hξU : ξ₁ ∈ U₁ := mem_irreducibleComponent
  have : IsReduced Y₁ := by
    have : ∀ x : ↥Y₁, _root_.IsReduced (Y₁.presheaf.stalk x) := fun x => inferInstance
    exact isReduced_of_isReduced_stalk Y₁
  have : IrreducibleSpace ↥(U₁ : Scheme.{u}) :=
    Subtype.irreducibleSpace (isIrreducible_irreducibleComponent (x := ξ₁))
  have : IsIntegral (U₁ : Scheme.{u}) := isIntegral_of_irreducibleSpace_of_isReduced _
  let f₁' : (U₁ : Scheme.{u}) ⟶ Spec (CommRingCat.of R) := U₁.ι ≫ f₁
  have hf₁' : Smooth f₁' ∧ IsSeparated f₁' ∧ LocallyOfFiniteType f₁' ∧ QuasiCompact f₁' := by
    have : TopologicalSpace.NoetherianSpace ↥(U₁ : Scheme.{u}) :=
      (inferInstance : TopologicalSpace.NoetherianSpace (U₁ : Set ↥Y₁))
    exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  let ρ : SchemeHomOver f₁' f₁ := ⟨U₁.ι, rfl⟩
  let r := (genericFibreRestrict R K f₁ f₁' ρ).1
  have hr : r ≫ pullback.fst f₁ (specGenericFibreInclusion R K) =
      pullback.fst f₁' (specGenericFibreInclusion R K) ≫ U₁.ι :=
    genericFibreRestrict_coe_comp_fst R K f₁ f₁' ρ
  have hro : IsOpenImmersion r := by
    have : IsOpenImmersion (r ≫ pullback.fst f₁ (specGenericFibreInclusion R K)) := by
      rw [hr]; infer_instance
    exact IsOpenImmersion.of_comp _ (pullback.fst f₁ (specGenericFibreInclusion R K))
  let e₁' : SchemeHomOver (pullback.snd f₁' (specGenericFibreInclusion R K)) gK :=
    schemeHomOverComp (genericFibreRestrict R K f₁ f₁' ρ) e₁
  have he₁' : IsOpenImmersion e₁'.1 := by
    change IsOpenImmersion (r ≫ e₁.1); infer_instance
  let ξ₁' : ↥(U₁ : Scheme.{u}) := ⟨ξ₁, hξU⟩
  have hξ₁' : f₁'.base ξ₁' = IsLocalRing.closedPoint R := by
    change f₁.base (U₁.ι.base ξ₁') = _
    rw [Scheme.Opens.ι_apply]; exact hξ₁
  have hξ₁gen' : ∀ y : ↥(U₁ : Scheme.{u}), f₁'.base y = IsLocalRing.closedPoint R → ξ₁' ⤳ y := by
    intro y hy
    exact (U₁.ι.isOpenEmbedding.isEmbedding.toIsInducing.specializes_iff).mp (hξ₁gen y.1 hy)
  have hcond : (pullback.fst e₁'.1 e₂.1 ≫ pullback.fst f₁' (specGenericFibreInclusion R K)) ≫ f₁' =
      (pullback.snd e₁'.1 e₂.1 ≫ pullback.fst f₂ (specGenericFibreInclusion R K)) ≫ f₂ := by
    have hi : pullback.fst e₁'.1 e₂.1 ≫ pullback.snd f₁' (specGenericFibreInclusion R K) =
        (pullback.fst e₁'.1 e₂.1 ≫ e₁'.1) ≫ gK := by rw [Category.assoc, e₁'.2]
    have hj : pullback.snd e₁'.1 e₂.1 ≫ pullback.snd f₂ (specGenericFibreInclusion R K) =
        (pullback.snd e₁'.1 e₂.1 ≫ e₂.1) ≫ gK := by rw [Category.assoc, e₂.2]
    rw [Category.assoc, Category.assoc, pullback.condition, pullback.condition, ← Category.assoc,
      ← Category.assoc, hi, hj, pullback.condition]
  let δ' : pullback e₁'.1 e₂.1 ⟶ pullback f₁' f₂ :=
    pullback.lift (pullback.fst e₁'.1 e₂.1 ≫ pullback.fst f₁' (specGenericFibreInclusion R K))
      (pullback.snd e₁'.1 e₂.1 ≫ pullback.fst f₂ (specGenericFibreInclusion R K)) hcond
  have hδ'₁ : δ' ≫ pullback.fst f₁' f₂ = pullback.fst e₁'.1 e₂.1 ≫ pullback.fst f₁' _ :=
    pullback.lift_fst _ _ _
  have hδ'₂ : δ' ≫ pullback.snd f₁' f₂ = pullback.snd e₁'.1 e₂.1 ≫ pullback.fst f₂ _ :=
    pullback.lift_snd _ _ _
  let m : pullback f₁' f₂ ⟶ pullback f₁ f₂ :=
    pullback.map _ _ _ _ U₁.ι (𝟙 Y₂) (𝟙 _) rfl (by rw [Category.comp_id, Category.id_comp])
  let s : pullback e₁'.1 e₂.1 ⟶ pullback e₁.1 e₂.1 :=
    pullback.map _ _ _ _ r (𝟙 _) (𝟙 XK) (by rw [Category.comp_id]; rfl) (by rw [Category.comp_id,
      Category.id_comp])
  have hsm : δ' ≫ m = s ≫ δ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hδ₁]
      change δ' ≫ pullback.map _ _ _ _ U₁.ι (𝟙 Y₂) (𝟙 _) _ _ ≫ pullback.fst f₁ f₂ =
        pullback.map _ _ _ _ r (𝟙 _) (𝟙 XK) _ _ ≫ pullback.fst e₁.1 e₂.1 ≫ pullback.fst f₁ _
      rw [pullback.lift_fst, ← Category.assoc, hδ'₁, ← Category.assoc, pullback.lift_fst,
        Category.assoc,
        Category.assoc, hr]
    · rw [Category.assoc, Category.assoc, hδ₂]
      change δ' ≫ pullback.map _ _ _ _ U₁.ι (𝟙 Y₂) (𝟙 _) _ _ ≫ pullback.snd f₁ f₂ =
        pullback.map _ _ _ _ r (𝟙 _) (𝟙 XK) _ _ ≫ pullback.snd e₁.1 e₂.1 ≫ pullback.fst f₂ _
      rw [pullback.lift_snd, ← Category.assoc, hδ'₂, ← Category.assoc, pullback.lift_snd]
      simp only [Category.comp_id]
  have hne' : ∀ (U' : (U₁ : Scheme.{u}).Opens), ξ₁' ∈ U' → ∀ u' : SchemeHomOver (U'.ι ≫ f₁') f₂,
      (genericFibreRestrict R K f₂ (U'.ι ≫ f₁') u').1 ≫ e₂.1 ≠
        (genericFibreRestrict R K f₁' (U'.ι ≫ f₁') ⟨U'.ι, rfl⟩).1 ≫ e₁'.1 := by
    intro U' hU' u' heq'
    let U : Y₁.Opens := U₁.ι ''ᵁ U'
    have hU : ξ₁ ∈ U := ⟨ξ₁', hU', rfl⟩
    let ε := U₁.ι.isoImage U'
    let u : SchemeHomOver (U.ι ≫ f₁) f₂ := ⟨ε.inv ≫ u'.1, by
      rw [Category.assoc, u'.2, ← Category.assoc, ← Category.assoc]
      change (ε.inv ≫ U'.ι ≫ U₁.ι) ≫ f₁ = _
      rw [Scheme.Hom.isoImage_inv_ι]⟩
    let κ : SchemeHomOver (U.ι ≫ f₁) (U'.ι ≫ f₁') := ⟨ε.inv, by
      change ε.inv ≫ U'.ι ≫ U₁.ι ≫ f₁ = _
      rw [← Category.assoc U'.ι, ← Category.assoc, Scheme.Hom.isoImage_inv_ι]⟩
    apply hne U hU u
    have h1 : (genericFibreRestrict R K f₂ (U.ι ≫ f₁) u).1 =
        (genericFibreRestrict R K (U'.ι ≫ f₁') (U.ι ≫ f₁) κ).1 ≫
          (genericFibreRestrict R K f₂ (U'.ι ≫ f₁') u').1 := by
      rw [← genericFibreRestrict_comp]
      rfl
    have h2 : (genericFibreRestrict R K f₁ (U.ι ≫ f₁) ⟨U.ι, rfl⟩).1 =
        (genericFibreRestrict R K (U'.ι ≫ f₁') (U.ι ≫ f₁) κ).1 ≫
          (genericFibreRestrict R K f₁' (U'.ι ≫ f₁') ⟨U'.ι, rfl⟩).1 ≫
            (genericFibreRestrict R K f₁ f₁' ρ).1 := by
      have h2' : (genericFibreRestrict R K (U'.ι ≫ f₁') (U.ι ≫ f₁) κ).1 ≫
          (genericFibreRestrict R K f₁' (U'.ι ≫ f₁') ⟨U'.ι, rfl⟩).1 ≫
            (genericFibreRestrict R K f₁ f₁' ρ).1 =
          (genericFibreRestrict R K f₁ (U.ι ≫ f₁)
            (schemeHomOverComp κ (schemeHomOverComp (⟨U'.ι, rfl⟩ : SchemeHomOver (U'.ι ≫ f₁') f₁')
              ρ))).1 := by
        rw [genericFibreRestrict_comp, genericFibreRestrict_comp]
      rw [h2']
      exact genericFibreRestrict_congr K _ _ (Scheme.Hom.isoImage_inv_ι U₁.ι U').symm
    rw [h1, h2, Category.assoc, heq', Category.assoc, Category.assoc]
    rfl
  have key :=
    not_mem_closure_image_fst_closure_range_of_forall_not_exists_extension_of_isIntegral
    K gK f₁' f₂ hf₁' hf₂ e₁' he₁' e₂ he₂ ξ₁' hξ₁' hξ₁gen' hne' δ' hδ'₁ hδ'₂
  apply key
  have : IsOpenImmersion m :=
    MorphismProperty.pullbackMap (P := @IsOpenImmersion.{u})
      (inferInstance : IsOpenImmersion U₁.ι) (inferInstance : IsOpenImmersion (𝟙 Y₂))
      rfl (Category.id_comp f₂).symm
  have hrm : Set.range m.base = (pullback.fst f₁ f₂).base ⁻¹' (U₁ : Set ↥Y₁) := by
    have := Scheme.Pullback.range_map f₁' f₂ f₁ f₂ U₁.ι (𝟙 Y₂) (𝟙 _) rfl
      (by rw [Category.comp_id, Category.id_comp])
    rw [Scheme.Opens.range_ι] at this
    change Set.range m.base = _ at this
    rw [this]
    ext q; constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, ⟨(pullback.snd f₁ f₂).base q, rfl⟩⟩
  have hrr : Set.range r.base =
      (pullback.fst f₁ (specGenericFibreInclusion R K)).base ⁻¹' (U₁ : Set ↥Y₁) := by
    apply le_antisymm
    · rintro _ ⟨z', rfl⟩
      change (pullback.fst f₁ (specGenericFibreInclusion R K)).base (r.base z') ∈ (U₁ : Set ↥Y₁)
      rw [← Scheme.Hom.comp_apply, hr, Scheme.Hom.comp_apply]
      exact (pullback.fst f₁' (specGenericFibreInclusion R K) z').2
    · intro z hz
      obtain ⟨v, hv⟩ : (pullback.fst f₁ (specGenericFibreInclusion R K)).base z ∈ Set.range
        U₁.ι.base := by
        rw [Scheme.Opens.range_ι]; exact hz
      have hv' : v ∈ Set.range (pullback.fst f₁' (specGenericFibreInclusion R K)).base := by
        rw [Scheme.Pullback.range_fst]
        refine ⟨(pullback.snd f₁ (specGenericFibreInclusion R K)).base z, ?_⟩
        rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
        change f₁.base ((pullback.fst f₁ (specGenericFibreInclusion R K)).base z) =
          (U₁.ι ≫ f₁).base v
        rw [Scheme.Hom.comp_apply, hv]
      obtain ⟨z', hz'⟩ := hv'
      refine ⟨z', (pullback.fst f₁ (specGenericFibreInclusion R K)).isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, hr, Scheme.Hom.comp_apply, hz', hv]
  have hmδ : m.base ⁻¹' Set.range δ.base = Set.range δ'.base := by
    apply le_antisymm
    · rintro q' ⟨x, hx⟩
      have hxs : x ∈ Set.range s.base := by
        have := Scheme.Pullback.range_map e₁'.1 e₂.1 e₁.1 e₂.1 r (𝟙 _) (𝟙 XK)
          (by rw [Category.comp_id]; rfl) (by rw [Category.comp_id, Category.id_comp])
        change Set.range s.base = _ at this
        rw [this]
        refine ⟨?_, ⟨(pullback.snd e₁.1 e₂.1).base x, rfl⟩⟩
        change (pullback.fst e₁.1 e₂.1).base x ∈ Set.range r.base
        rw [hrr]
        change (pullback.fst f₁ (specGenericFibreInclusion R K)).base ((pullback.fst e₁.1 e₂.1).base
          x) ∈ (U₁ : Set ↥Y₁)
        rw [← Scheme.Hom.comp_apply, ← hδ₁, Scheme.Hom.comp_apply, hx]
        have hq : m.base q' ∈ Set.range m.base := ⟨q', rfl⟩
        rw [hrm] at hq
        exact hq
      obtain ⟨x', rfl⟩ := hxs
      refine ⟨x', m.isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, hsm, Scheme.Hom.comp_apply, hx]
    · rintro _ ⟨x', rfl⟩
      refine ⟨s.base x', ?_⟩
      rw [← Scheme.Hom.comp_apply, ← hsm, Scheme.Hom.comp_apply]
  have hmcl : m.base ⁻¹' closure (Set.range δ.base) = closure (Set.range δ'.base) := by
    rw [m.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage m.continuous, hmδ]
  set A : Set ↥Y₁ := (pullback.fst f₁ f₂).base ''
      (closure (Set.range δ.base) ∩ {q | f₁.base ((pullback.fst f₁ f₂).base q) =
        IsLocalRing.closedPoint R})
    with hA
  set A' : Set ↥(U₁ : Scheme.{u}) := (pullback.fst f₁' f₂).base ''
      (closure (Set.range δ'.base) ∩ {q | f₁'.base ((pullback.fst f₁' f₂).base q) =
        IsLocalRing.closedPoint R})
    with hA'
  have hAA' : (U₁ : Set ↥Y₁) ∩ A ⊆ U₁.ι.base '' A' := by
    rintro y ⟨hyU, ⟨q, ⟨hq, hqk⟩, rfl⟩⟩
    have hqm : q ∈ Set.range m.base := by rw [hrm]; exact hyU
    obtain ⟨q', rfl⟩ := hqm
    refine ⟨(pullback.fst f₁' f₂).base q', ⟨q', ⟨?_, ?_⟩, rfl⟩, ?_⟩
    · rw [← hmcl]; exact hq
    · change f₁.base (U₁.ι.base ((pullback.fst f₁' f₂).base q')) = _
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
      change ((pullback.map _ _ _ _ U₁.ι (𝟙 Y₂) (𝟙 _) _ _ ≫ pullback.fst f₁ f₂) ≫ f₁) q' = _ at hqk
      rwa [pullback.lift_fst, Category.assoc] at hqk
    · symm
      rw [← Scheme.Hom.comp_apply]
      change (pullback.map _ _ _ _ U₁.ι (𝟙 Y₂) (𝟙 _) _ _ ≫ pullback.fst f₁ f₂) q' = _
      rw [pullback.lift_fst, Scheme.Hom.comp_apply]
  have h1 : ξ₁ ∈ closure ((U₁ : Set ↥Y₁) ∩ A) := U₁.2.inter_closure ⟨hξU, hmem⟩
  have h2 : ξ₁ ∈ closure (U₁.ι.base '' A') := closure_mono hAA' h1
  have h3 : ξ₁' ∈ U₁.ι.base ⁻¹' closure (U₁.ι.base '' A') := h2
  rwa [← U₁.ι.isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image] at h3

end AbelianVarieties.NOSProofs.LocalNonextension
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_opens_forall_isClosedImmersion_of_forall_ne_not_exists_extension.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.SeparatedModelShrinking

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

namespace Shrinking

section DVR

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]

theorem sι_ne_closedPoint (t : ↥(Spec (CommRingCat.of K))) :
    (specGenericFibreInclusion R K).base t ≠ IsLocalRing.closedPoint R := by
  intro h
  have h1 : (IsLocalRing.closedPoint R).asIdeal = Ideal.comap (algebraMap R K) t.asIdeal := by
    rw [← h]; rfl
  have : t.asIdeal.IsPrime := t.isPrime
  have ht : t.asIdeal = ⊥ := Ideal.eq_bot_of_prime t.asIdeal
  rw [ht, Ideal.comap_bot_of_injective (algebraMap R K) (IsFractionRing.injective R K)] at h1
  exact IsDiscreteValuationRing.not_a_field R h1

theorem mem_range_sι_of_ne_closedPoint (t : ↥(Spec (CommRingCat.of R)))
    (ht : t ≠ IsLocalRing.closedPoint R) : t ∈ Set.range (specGenericFibreInclusion R K).base := by
  have : t.asIdeal.IsPrime := t.isPrime
  have hbot : t.asIdeal = ⊥ := by
    by_contra hne
    apply ht
    apply PrimeSpectrum.ext
    exact IsLocalRing.eq_maximalIdeal (IsPrime.to_maximal_ideal hne)
  refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
  apply PrimeSpectrum.ext
  change Ideal.comap (algebraMap R K) ⊥ = t.asIdeal
  rw [hbot, Ideal.comap_bot_of_injective (algebraMap R K) (IsFractionRing.injective R K)]

end DVR

section Pair

variable {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K]
  {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K))
  {ι : Type u} (Y : ι → Scheme.{u}) (f : ∀ i, Y i ⟶ Spec (CommRingCat.of R))
  (e : ∀ i, SchemeHomOver (pullback.snd (f i) (specGenericFibreInclusion R K)) gK)

theorem cond (i j : ι) :
    (pullback.fst (e i).1 (e j).1 ≫ pullback.fst (f i) (specGenericFibreInclusion R K)) ≫ f i =
      (pullback.snd (e i).1 (e j).1 ≫ pullback.fst (f j) (specGenericFibreInclusion R K)) ≫ f j :=
        by
  have hi : pullback.fst (e i).1 (e j).1 ≫ pullback.snd (f i) (specGenericFibreInclusion R K) =
      (pullback.fst (e i).1 (e j).1 ≫ (e i).1) ≫ gK := by rw [Category.assoc, (e i).2]
  have hj : pullback.snd (e i).1 (e j).1 ≫ pullback.snd (f j) (specGenericFibreInclusion R K) =
      (pullback.snd (e i).1 (e j).1 ≫ (e j).1) ≫ gK := by rw [Category.assoc, (e j).2]
  rw [Category.assoc, Category.assoc, pullback.condition, pullback.condition, ← Category.assoc,
    ← Category.assoc, hi, hj, pullback.condition]

/-- The comparison from the generic overlap into the model product. -/
noncomputable def δ₀ (i j : ι) : pullback (e i).1 (e j).1 ⟶ pullback (f i) (f j) :=
  pullback.lift (pullback.fst (e i).1 (e j).1 ≫ pullback.fst (f i) (specGenericFibreInclusion R K))
    (pullback.snd (e i).1 (e j).1 ≫ pullback.fst (f j) (specGenericFibreInclusion R K)) (cond K gK
      Y f e i j)

@[scoped simp] theorem δ₀_fst (i j : ι) : δ₀ K gK Y f e i j ≫ pullback.fst (f i) (f j) =
    pullback.fst (e i).1 (e j).1 ≫ pullback.fst (f i) (specGenericFibreInclusion R K) :=
      pullback.lift_fst _ _ _

@[scoped simp] theorem δ₀_snd (i j : ι) : δ₀ K gK Y f e i j ≫ pullback.snd (f i) (f j) =
    pullback.snd (e i).1 (e j).1 ≫ pullback.fst (f j) (specGenericFibreInclusion R K) :=
      pullback.lift_snd _ _ _

/-- The projection from the pullback of the generic overlap. -/
noncomputable def u (i j : ι) :
    pullback (pullback.fst (f i) (specGenericFibreInclusion R K) ≫ f i) (f j) ⟶ pullback (f i) (f
      j) :=
  pullback.map _ _ _ _ (pullback.fst (f i) (specGenericFibreInclusion R K)) (𝟙 _) (𝟙 _)
    (Category.comp_id _) (by rw [Category.comp_id, Category.id_comp])

/-- The generic comparison lifted to the pullback. -/
noncomputable def δK (i j : ι) :
    pullback (e i).1 (e j).1 ⟶ pullback (pullback.fst (f i) (specGenericFibreInclusion R K) ≫ f i)
      (f j) :=
  pullback.lift (pullback.fst (e i).1 (e j).1)
    (pullback.snd (e i).1 (e j).1 ≫ pullback.fst (f j) (specGenericFibreInclusion R K))
    (by rw [← Category.assoc]; exact cond K gK Y f e i j)

theorem δK_u (i j : ι) : δK K gK Y f e i j ≫ u K Y f i j = δ₀ K gK Y f e i j := by
  apply pullback.hom_ext
  · rw [Category.assoc, u, pullback.lift_fst, ← Category.assoc, δK, pullback.lift_fst, δ₀_fst]
  · rw [Category.assoc, u, pullback.lift_snd, ← Category.assoc, δK, pullback.lift_snd, δ₀_snd,
      Category.comp_id]

end Pair

end Shrinking

open Shrinking in
theorem
    _root_.NeronModelInfra.exists_opens_forall_isClosedImmersion_of_forall_ne_not_exists_extension
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K))
    [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    {ι : Type u} [Finite ι]
    (Y : ι → Scheme.{u}) (f : ∀ i, Y i ⟶ Spec (CommRingCat.of R))
    (hf : ∀ i, Smooth (f i) ∧ IsSeparated (f i) ∧ LocallyOfFiniteType (f i) ∧ QuasiCompact (f i))
    (e : ∀ i, SchemeHomOver (pullback.snd (f i) (specGenericFibreInclusion R K)) gK) (he : ∀ i,
      IsIso (e i).1)
    (ξ : ∀ i, ↥(Y i)) (hξ : ∀ i, (f i).base (ξ i) = IsLocalRing.closedPoint R)
    (hξgen : ∀ i (y : ↥(Y i)), (f i).base y = IsLocalRing.closedPoint R → ξ i ⤳ y)
    (hne : ∀ i j, i ≠ j → ∀ (U : (Y i).Opens), ξ i ∈ U → ∀ u : SchemeHomOver (U.ι ≫ f i) (f j),
      (genericFibreRestrict R K (f j) (U.ι ≫ f i) u).1 ≫ (e j).1 ≠
        (genericFibreRestrict R K (f i) (U.ι ≫ f i) ⟨U.ι, rfl⟩).1 ≫ (e i).1) :
    ∃ V : ∀ i, (Y i).Opens,
      (∀ i, ξ i ∈ V i) ∧
      (∀ i (y : ↥(Y i)), (f i).base y ≠ IsLocalRing.closedPoint R → y ∈ V i) ∧
      (∀ i, IsIso (genericFibreRestrict R K (f i) ((V i).ι ≫ f i) ⟨(V i).ι, rfl⟩).1) ∧
      ∀ i j, i ≠ j →
        ∀ δ : pullback
              (schemeHomOverComp (genericFibreRestrict R K (f i) ((V i).ι ≫ f i) ⟨(V i).ι, rfl⟩)
                (e i)).1
              (schemeHomOverComp (genericFibreRestrict R K (f j) ((V j).ι ≫ f j) ⟨(V j).ι, rfl⟩)
                (e j)).1 ⟶
            pullback ((V i).ι ≫ f i) ((V j).ι ≫ f j),
          δ ≫ pullback.fst ((V i).ι ≫ f i) ((V j).ι ≫ f j) =
            pullback.fst _ _ ≫ pullback.fst ((V i).ι ≫ f i) (specGenericFibreInclusion R K) →
          δ ≫ pullback.snd ((V i).ι ≫ f i) ((V j).ι ≫ f j) =
            pullback.snd _ _ ≫ pullback.fst ((V j).ι ≫ f j) (specGenericFibreInclusion R K) →
          IsClosedImmersion δ := by
  classical
  have hI : IsOpenImmersion (specGenericFibreInclusion R K) := inferInstance
  let B : ∀ i j : ι, Set ↥(Y i) := fun i j =>
    closure ((pullback.fst (f i) (f j)).base ''
      (closure (Set.range (δ₀ K gK Y f e i j).base) ∩
        {q | (f i).base ((pullback.fst (f i) (f j)).base q) = IsLocalRing.closedPoint R}))
  have hBspec : ∀ i j, B i j ⊆ {y | (f i).base y = IsLocalRing.closedPoint R} := by
    intro i j
    refine closure_minimal ?_ ?_
    · rintro _ ⟨q, ⟨-, hq⟩, rfl⟩; exact hq
    · exact (IsLocalRing.isClosed_singleton_closedPoint (R := R)).preimage (f i).continuous
  have hBξ : ∀ i j, i ≠ j → ξ i ∉ B i j := fun i j hij =>
    NeronModelInfra.not_mem_closure_image_fst_closure_range_of_forall_not_exists_extension
      K gK (f i) (f j) (hf i) (hf j) (e i) (he i) (e j) (he j) (ξ i) (hξ i) (hξgen i) (hne i j hij)
      (δ₀ K gK Y f e i j) (δ₀_fst K gK Y f e i j) (δ₀_snd K gK Y f e i j)
  let S : ∀ i, Set ↥(Y i) := fun i => ⋃ j : {j // j ≠ i}, B i j.1
  have hS : ∀ i, IsClosed (S i) := fun i => isClosed_iUnion_of_finite fun _ => isClosed_closure
  let V : ∀ i, (Y i).Opens := fun i => ⟨(S i)ᶜ, (hS i).isOpen_compl⟩
  have hVmem : ∀ i (y : ↥(Y i)), y ∈ V i ↔ ∀ j : {j // j ≠ i}, y ∉ B i j.1 := fun i y => by
    change y ∈ (S i)ᶜ ↔ _
    simp only [S, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
  have hξV : ∀ i, ξ i ∈ V i := fun i => (hVmem i _).mpr fun j => hBξ i j.1 (Ne.symm j.2)
  have hgen : ∀ i (y : ↥(Y i)), (f i).base y ≠ IsLocalRing.closedPoint R → y ∈ V i :=
    fun i y hy => (hVmem i y).mpr fun j hB => hy (hBspec i j.1 hB)
  have hiso : ∀ i, IsIso (genericFibreRestrict R K (f i) ((V i).ι ≫ f i) ⟨(V i).ι, rfl⟩).1 := by
    intro i
    have hr : (genericFibreRestrict R K (f i) ((V i).ι ≫ f i) ⟨(V i).ι, rfl⟩).1 ≫
        pullback.fst (f i) (specGenericFibreInclusion R K) =
        pullback.fst ((V i).ι ≫ f i) (specGenericFibreInclusion R K) ≫ (V i).ι :=
      genericFibreRestrict_coe_comp_fst R K (f i) ((V i).ι ≫ f i) ⟨(V i).ι, rfl⟩
    have : IsOpenImmersion ((genericFibreRestrict R K (f i) ((V i).ι ≫ f i) ⟨(V i).ι, rfl⟩).1 ≫
        pullback.fst (f i) (specGenericFibreInclusion R K)) := by rw [hr]; infer_instance
    have : IsOpenImmersion (genericFibreRestrict R K (f i) ((V i).ι ≫ f i) ⟨(V i).ι, rfl⟩).1 :=
      IsOpenImmersion.of_comp _ (pullback.fst (f i) (specGenericFibreInclusion R K))
    apply isIso_of_isOpenImmersion_of_opensRange_eq_top
    refine eq_top_iff.mpr fun z _ => ?_
    change z ∈ Set.range _
    have hz : (f i).base ((pullback.fst (f i) (specGenericFibreInclusion R K)).base z) ≠
        IsLocalRing.closedPoint R := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
      exact sι_ne_closedPoint K _
    have hzV : (pullback.fst (f i) (specGenericFibreInclusion R K)).base z ∈ Set.range (V
      i).ι.base := by
      rw [Scheme.Opens.range_ι]; exact hgen i _ hz
    obtain ⟨v, hv⟩ := hzV
    have hv' : v ∈ Set.range (pullback.fst ((V i).ι ≫ f i) (specGenericFibreInclusion R K)).base
      := by
      rw [Scheme.Pullback.range_fst]
      refine ⟨(pullback.snd (f i) (specGenericFibreInclusion R K)).base z, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply,
        Scheme.Hom.comp_apply, hv]
    obtain ⟨z', hz'⟩ := hv'
    refine ⟨z', (pullback.fst (f i) (specGenericFibreInclusion R K)).isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hr, Scheme.Hom.comp_apply, hz', hv]
  refine ⟨V, hξV, hgen, hiso, ?_⟩
  intro i j hij δ' h1 h2
  have : IsIso (genericFibreRestrict R K (f i) ((V i).ι ≫ f i)
    ⟨(V i).ι, rfl⟩).1 := hiso i
  have : IsIso (genericFibreRestrict R K (f j) ((V j).ι ≫ f j)
    ⟨(V j).ι, rfl⟩).1 := hiso j
  have : IsIso (e i).1 := he i
  have : IsIso (e j).1 := he j
  have : IsSeparated (f j) := (hf j).2.1
  let s : pullback (schemeHomOverComp (genericFibreRestrict R K (f i) ((V i).ι ≫ f i) ⟨(V i).ι,
    rfl⟩) (e i)).1
      (schemeHomOverComp (genericFibreRestrict R K (f j) ((V j).ι ≫ f j) ⟨(V j).ι, rfl⟩) (e j)).1 ⟶
      pullback (e i).1 (e j).1 :=
    pullback.map _ _ _ _ (genericFibreRestrict R K (f i) ((V i).ι ≫ f i) ⟨(V i).ι, rfl⟩).1
      (genericFibreRestrict R K (f j) ((V j).ι ≫ f j) ⟨(V j).ι, rfl⟩).1 (𝟙 XK)
      (by rw [Category.comp_id]; rfl) (by rw [Category.comp_id]; rfl)
  let m : pullback ((V i).ι ≫ f i) ((V j).ι ≫ f j) ⟶ pullback (f i) (f j) :=
    pullback.map _ _ _ _ (V i).ι (V j).ι (𝟙 _) (Category.comp_id _) (Category.comp_id _)
  have hA : δ' ≫ m = s ≫ δ₀ K gK Y f e i j := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, δ₀_fst]
      change δ' ≫ pullback.map _ _ _ _ (V i).ι (V j).ι (𝟙 _) _ _ ≫ pullback.fst (f i) (f j) =
        pullback.map _ _ _ _ _ _ (𝟙 XK) _ _ ≫ pullback.fst (e i).1 (e j).1 ≫ pullback.fst (f i) _
      rw [pullback.lift_fst, ← Category.assoc, h1, ← Category.assoc, pullback.lift_fst,
        Category.assoc,
        Category.assoc, genericFibreRestrict_coe_comp_fst]
    · rw [Category.assoc, Category.assoc, δ₀_snd]
      change δ' ≫ pullback.map _ _ _ _ (V i).ι (V j).ι (𝟙 _) _ _ ≫ pullback.snd (f i) (f j) =
        pullback.map _ _ _ _ _ _ (𝟙 XK) _ _ ≫ pullback.snd (e i).1 (e j).1 ≫ pullback.fst (f j) _
      rw [pullback.lift_snd, ← Category.assoc, h2, ← Category.assoc, pullback.lift_snd,
        Category.assoc,
        Category.assoc, genericFibreRestrict_coe_comp_fst]
  have hδK : IsClosedImmersion (δK K gK Y f e i j) := by
    have : IsClosedImmersion (δK K gK Y f e i j ≫
        pullback.fst (pullback.fst (f i) (specGenericFibreInclusion R K) ≫ f i) (f j)) := by
      rw [δK, pullback.lift_fst]; infer_instance
    exact IsClosedImmersion.of_comp (δK K gK Y f e i j)
      (pullback.fst (pullback.fst (f i) (specGenericFibreInclusion R K) ≫ f i) (f j))
  have hu : IsOpenImmersion (u K Y f i j) := by dsimp only [u]; infer_instance
  have hpre : IsPreimmersion δ' := by
    have : IsPreimmersion (δ' ≫ m) := by rw [hA, ← δK_u]; infer_instance
    exact IsPreimmersion.of_comp δ' m
  have hrange : Set.range δ'.base = m.base ⁻¹' Set.range (δ₀ K gK Y f e i j).base := by
    have h := congrArg (fun φ => Set.range φ.base) hA
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp] at h
    have hs : Function.Surjective s := fun y =>
      ⟨(inv s) y, by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
    rw [hs.range_eq, Set.image_univ] at h
    rw [← h, m.isOpenEmbedding.injective.preimage_image]
  have hclosed : IsClosed (Set.range δ'.base) := by
    rw [hrange]
    suffices heq : m.base ⁻¹' Set.range (δ₀ K gK Y f e i j).base =
        m.base ⁻¹' closure (Set.range (δ₀ K gK Y f e i j).base) by
      rw [heq]; exact isClosed_closure.preimage m.continuous
    ext q'
    refine ⟨fun hq => subset_closure hq, fun hq => ?_⟩
    change m.base q' ∈ closure (Set.range (δ₀ K gK Y f e i j).base) at hq
    change m.base q' ∈ Set.range (δ₀ K gK Y f e i j).base
    have hfst : (pullback.fst (f i) (f j)).base (m.base q') ∈ (V i : Set ↥(Y i)) := by
      rw [← Scheme.Opens.range_ι, ← Scheme.Hom.comp_apply]
      change (pullback.map _ _ _ _ (V i).ι (V j).ι (𝟙 _) _ _ ≫ pullback.fst (f i) (f j)) q' ∈ _
      rw [pullback.lift_fst, Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    by_cases hsp : (f i).base ((pullback.fst (f i) (f j)).base (m.base q')) =
      IsLocalRing.closedPoint R
    · have hB : (pullback.fst (f i) (f j)).base (m.base q') ∈ B i j :=
        subset_closure ⟨m.base q', ⟨hq, hsp⟩, rfl⟩
      exact absurd hB ((hVmem i _).mp hfst ⟨j, Ne.symm hij⟩)
    · have hq_u : m.base q' ∈ Set.range (u K Y f i j).base := by
        have hru : Set.range (u K Y f i j).base =
            (pullback.fst (f i) (f j)).base ⁻¹' Set.range (pullback.fst (f i)
              (specGenericFibreInclusion R K)).base ∩
              (pullback.snd (f i) (f j)).base ⁻¹' Set.range (𝟙 (Y j) : Y j ⟶ Y j).base :=
          Scheme.Pullback.range_map (pullback.fst (f i) (specGenericFibreInclusion R K) ≫ f i) (f
            j) (f i) (f j)
            (pullback.fst (f i) (specGenericFibreInclusion R K)) (𝟙 _) (𝟙 _)
            (Category.comp_id _) (by rw [Category.comp_id, Category.id_comp])
        rw [hru]
        refine ⟨?_, ?_⟩
        · change (pullback.fst (f i) (f j)).base (m.base q') ∈ Set.range _
          rw [Scheme.Pullback.range_fst]
          exact mem_range_sι_of_ne_closedPoint K _ hsp
        · exact ⟨(pullback.snd (f i) (f j)).base (m.base q'), rfl⟩
      obtain ⟨q'', hq''⟩ := hq_u
      have hpre' : (u K Y f i j).base ⁻¹' Set.range (δ₀ K gK Y f e i j).base =
          Set.range (δK K gK Y f e i j).base := by
        rw [← δK_u, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
          (u K Y f i j).isOpenEmbedding.injective.preimage_image]
      have hcl : (u K Y f i j).base ⁻¹' closure (Set.range (δ₀ K gK Y f e i j).base) =
          Set.range (δK K gK Y f e i j).base := by
        rw [(u K Y f i j).isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
          (u K Y f i j).continuous, hpre']
        exact (δK K gK Y f e i j).isClosedEmbedding.isClosed_range.closure_eq
      have hx : q'' ∈ Set.range (δK K gK Y f e i j).base := by
        rw [← hcl, Set.mem_preimage, hq'']; exact hq
      obtain ⟨x, rfl⟩ := hx
      refine ⟨x, ?_⟩
      rw [← hq'', ← Scheme.Hom.comp_apply, δK_u]
  exact IsClosedImmersion.iff_isPreimmersion.mpr ⟨hpre, hclosed⟩

end AbelianVarieties.NOSProofs.SeparatedModelShrinking
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_model_openCover_of_forall_ne_not_exists_extension.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.SeparatedModelCover

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

theorem _root_.NeronModelInfra.exists_model_openCover_of_forall_ne_not_exists_extension
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K))
    [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    {ι : Type u} [Finite ι] [Nonempty ι]
    (Y : ι → Scheme.{u}) (f : ∀ i, Y i ⟶ Spec (CommRingCat.of R))
    (hf : ∀ i, Smooth (f i) ∧ IsSeparated (f i) ∧ LocallyOfFiniteType (f i) ∧ QuasiCompact (f i))
    (e : ∀ i, SchemeHomOver (pullback.snd (f i) (specGenericFibreInclusion R K)) gK) (he : ∀ i,
      IsIso (e i).1)
    (ξ : ∀ i, ↥(Y i)) (hξ : ∀ i, (f i).base (ξ i) = IsLocalRing.closedPoint R)
    (hξgen : ∀ i (y : ↥(Y i)), (f i).base y = IsLocalRing.closedPoint R → ξ i ⤳ y)
    (hne : ∀ i j, i ≠ j → ∀ (U : (Y i).Opens), ξ i ∈ U → ∀ u : SchemeHomOver (U.ι ≫ f i) (f j),
      (genericFibreRestrict R K (f j) (U.ι ≫ f i) u).1 ≫ (e j).1 ≠
        (genericFibreRestrict R K (f i) (U.ι ≫ f i) ⟨U.ι, rfl⟩).1 ≫ (e i).1) :
    ∃ (X : Scheme.{u}) (g : X ⟶ Spec (CommRingCat.of R))
      (eX : SchemeHomOver (pullback.snd g (specGenericFibreInclusion R K)) gK)
      (V : ∀ i, (Y i).Opens) (j : ∀ i, SchemeHomOver ((V i).ι ≫ f i) g),
      Smooth g ∧ IsSeparated g ∧ LocallyOfFiniteType g ∧ QuasiCompact g ∧ IsIso eX.1 ∧
      (∀ i, ξ i ∈ V i) ∧
      (∀ i (y : ↥(Y i)), (f i).base y ≠ IsLocalRing.closedPoint R → y ∈ V i) ∧
      (∀ i, IsOpenImmersion (j i).1) ∧
      (∀ i, (genericFibreRestrict R K g ((V i).ι ≫ f i) (j i)).1 ≫ eX.1 =
        (genericFibreRestrict R K (f i) ((V i).ι ≫ f i) ⟨(V i).ι, rfl⟩).1 ≫ (e i).1) ∧
      (∀ x : ↥X, ∃ i, x ∈ Set.range (j i).1.base) := by
  obtain ⟨V, hξV, hgen, hiso, hdiag⟩ :=
    NeronModelInfra.exists_opens_forall_isClosedImmersion_of_forall_ne_not_exists_extension
      K gK Y f hf e he ξ hξ hξgen hne
  have hf' : ∀ i, Smooth ((V i).ι ≫ f i) ∧ IsSeparated ((V i).ι ≫ f i) ∧
      LocallyOfFiniteType ((V i).ι ≫ f i) ∧ QuasiCompact ((V i).ι ≫ f i) := by
    intro i
    obtain ⟨h1, h2, h3, h4⟩ := hf i
    have : IsLocallyNoetherian (Y i) := LocallyOfFiniteType.isLocallyNoetherian (f i)
    have : CompactSpace ↥(Y i) := QuasiCompact.compactSpace_of_compactSpace (f i)
    have : IsNoetherian (Y i) := {}
    have : TopologicalSpace.NoetherianSpace ↥(V i : Scheme.{u}) :=
      (inferInstance : TopologicalSpace.NoetherianSpace (V i : Set ↥(Y i)))
    exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  have he' : ∀ i, IsIso (schemeHomOverComp
      (genericFibreRestrict R K (f i) ((V i).ι ≫ f i) ⟨(V i).ι, rfl⟩) (e i)).1 := by
    intro i
    have : IsIso (genericFibreRestrict R K (f i) ((V i).ι ≫ f i)
    ⟨(V i).ι, rfl⟩).1 := hiso i
    have : IsIso (e i).1 := he i
    change IsIso ((genericFibreRestrict R K (f i) ((V i).ι ≫ f i) ⟨(V i).ι, rfl⟩).1 ≫ (e i).1)
    infer_instance
  obtain ⟨X, g, eX, j, hsm, hsep, hlft, hqc, hiX, hopen, hcomp, hcov⟩ :=
    NeronModelInfra.exists_model_openCover_of_forall_isClosedImmersion_pullback_lift
      K gK (fun i => (V i : Scheme.{u})) (fun i => (V i).ι ≫ f i) hf'
      (fun i => schemeHomOverComp (genericFibreRestrict R K (f i) ((V i).ι ≫ f i) ⟨(V i).ι, rfl⟩)
        (e i))
      he' hdiag
  exact ⟨X, g, eX, V, j, hsm, hsep, hlft, hqc, hiX, hξV, hgen, hopen, hcomp, hcov⟩

end AbelianVarieties.NOSProofs.SeparatedModelCover
end
