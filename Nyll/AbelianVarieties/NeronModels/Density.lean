/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Nyll.AbelianVarieties.NeronModels.Basic
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.BaseChange
public import Nyll.SchemeTheory.Morphisms.SmoothReducedReduced
public import Nyll.SchemeTheory.Sheaves.IdealSheafDataReducedSubschemeVanishingIdealLeKer
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-!
# Dense domains for partial group laws

Restrict partial multiplication to dense fibrewise domains, preserve density under base change,
and compare morphisms through the reduced closure of the multiplication graph.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_forall_dense_preimage_fibre_comp_eq_comp_of_forall_dense_preimage_fibre_of_relativeGroupLaw.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.AssociativityRestriction


universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
    Topology

namespace PartialMultiplication

section Topo

variable {P : Type*} [TopologicalSpace P]

/-- Density of a subset inside a specified fibre or subspace. -/
def DenseIn (S F : Set P) : Prop := F ⊆ closure (S ∩ F)

theorem denseIn_iff_dense_preimage_val (S F : Set P) :
    DenseIn S F ↔ Dense ((Subtype.val : F → P) ⁻¹' S) := by
  rw [DenseIn, Subtype.dense_iff, Subtype.image_preimage_coe, Set.inter_comm]

theorem denseIn_setOf_iff {p : P → Prop} (S : Set P) :
    DenseIn S {q | p q} ↔ Dense ((Subtype.val : {q // p q} → P) ⁻¹' S) :=
  denseIn_iff_dense_preimage_val S {q | p q}

theorem DenseIn.mono {S S' F : Set P} (h : DenseIn S F) (hS : S ⊆ S') : DenseIn S' F :=
  h.trans (closure_mono (Set.inter_subset_inter_left _ hS))

theorem DenseIn.image_iff {W : Type*} [TopologicalSpace W] {φ : W → P} (hφ : IsInducing φ) {F : Set
    P}
    (hd : DenseIn (Set.range φ) F) (S : Set W) :
    DenseIn (φ '' S) F ↔ DenseIn S (φ ⁻¹' F) := by
  constructor
  · intro h w hw
    rw [hφ.closure_eq_preimage_closure_image, Set.image_inter_preimage]
    exact h hw
  · intro h x hx
    rw [mem_closure_iff]
    intro O hO hxO
    obtain ⟨_, hyO, ⟨w, rfl⟩, hyF⟩ := mem_closure_iff.mp (hd hx) O hO hxO
    obtain ⟨w', hw'O, hw'S, hw'F⟩ :=
      mem_closure_iff.mp (h hyF) (φ ⁻¹' O) (hO.preimage hφ.continuous) hyO
    exact ⟨φ w', hw'O, ⟨w', hw'S, rfl⟩, hw'F⟩

theorem dense_fibre_transfer {W A B : Type*} [TopologicalSpace W] {φ : W → P} (hφ : IsOpenEmbedding
    φ)
    (pW : W → A) (pP : P → B) (g : A → B) (hg : Function.Injective g)
    (hcomm : ∀ z, pP (φ z) = g (pW z)) {S : Set P} (hS : S ⊆ Set.range φ) {SW : Set W}
    (hSW : SW = φ ⁻¹' S) (a : A)
    (hd : Dense ((Subtype.val : {q // pP q = g a} → P) ⁻¹' S)) :
    Dense ((Subtype.val : {z // pW z = a} → W) ⁻¹' SW) := by
  rw [← denseIn_setOf_iff] at hd ⊢
  have hF : φ ⁻¹' {q | pP q = g a} = {z | pW z = a} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hcomm, hg.eq_iff]
  have hr : DenseIn (Set.range φ) {q | pP q = g a} := hd.mono hS
  have hSe : φ '' (φ ⁻¹' S) = S := Set.image_preimage_eq_of_subset hS
  rw [← hF, hSW]
  exact (DenseIn.image_iff hφ.isInducing hr _).mp (hSe.symm ▸ hd)

end Topo

section GenericPoint

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]

theorem isLocalization_away {ϖ : R} (hϖ : Irreducible ϖ) : IsLocalization.Away ϖ K where
  map_units := by
    rintro ⟨y, n, rfl⟩
    exact IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr (pow_ne_zero n
      hϖ.ne_zero))
  surj := by
    intro z
    obtain ⟨⟨a, b, hb⟩, h⟩ := IsLocalization.surj (nonZeroDivisors R) z
    obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (nonZeroDivisors.ne_zero hb) hϖ
    refine ⟨⟨a * ↑v⁻¹, ⟨ϖ ^ n, n, rfl⟩⟩, ?_⟩
    simp only at h ⊢
    have hϖn : (ϖ ^ n : R) = b * ↑v⁻¹ := by
      rw [hv, mul_assoc, mul_comm (ϖ ^ n), ← mul_assoc, Units.mul_inv, one_mul]
    rw [hϖn, map_mul, map_mul, ← mul_assoc, h]
  exists_of_eq := by
    intro x y h
    exact ⟨1, by simpa only [OneMemClass.coe_one, one_mul] using IsFractionRing.injective R K h⟩

scoped instance isOpenImmersion_specGenericFibreInclusion : IsOpenImmersion
    (specGenericFibreInclusion R K) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have : IsLocalization.Away ϖ K := isLocalization_away R K hϖ
  exact IsOpenImmersion.of_isLocalization ϖ

theorem range_specGenericFibreInclusion :
    Set.range (specGenericFibreInclusion R K).base = {q | q ≠ IsLocalRing.closedPoint R} := by
  ext q
  constructor
  · rintro ⟨s, rfl⟩ h
    have hs : s.asIdeal.IsPrime := s.isPrime
    have h1 := congrArg PrimeSpectrum.asIdeal h
    change Ideal.comap (algebraMap R K) s.asIdeal = IsLocalRing.maximalIdeal R at h1
    rw [Ideal.eq_bot_of_prime s.asIdeal,
      Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)] at h1
    exact IsDiscreteValuationRing.not_a_field' (R := R) h1.symm
  · intro hq
    have hbot : q.asIdeal = ⊥ := by
      by_contra hne
      apply hq
      have hmax := Ideal.IsPrime.isMaximal q.isPrime hne
      exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hmax)
    refine ⟨⟨⊥, Ideal.isPrime_bot⟩, PrimeSpectrum.ext ?_⟩
    change Ideal.comap (algebraMap R K) (⊥ : Ideal K) = q.asIdeal
    rw [hbot, Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)]

variable {R K}

theorem isDominant_fst_specGenericFibreInclusion {Z : Scheme.{u}} (g : Z ⟶ Spec (CommRingCat.of R))
    [Smooth g] : IsDominant (pullback.fst g (specGenericFibreInclusion R K)) := by
  refine ⟨?_⟩
  rw [DenseRange, Scheme.Pullback.range_fst, dense_iff_inter_open]
  rintro O hO ⟨z, hz⟩
  have hopen : IsOpen (g.base '' O) := g.isOpenMap O hO
  let η : ↥(Spec (CommRingCat.of R)) := ⟨(⊥ : Ideal R), Ideal.isPrime_bot⟩
  have hη : η ∈ g.base '' O := by
    have hgz : g.base z ∈ g.base '' O := ⟨z, hz, rfl⟩
    have hsp : η ⤳ g.base z := (PrimeSpectrum.le_iff_specializes η (g.base z)).mp bot_le
    exact hsp.mem_open hopen hgz
  obtain ⟨o, ho, hoη⟩ := hη
  refine ⟨o, ho, ?_⟩
  change g.base o ∈ Set.range (specGenericFibreInclusion R K).base
  rw [hoη, range_specGenericFibreInclusion]
  intro h
  have h1 := congrArg PrimeSpectrum.asIdeal h
  exact IsDiscreteValuationRing.not_a_field' (R := R) h1.symm

end GenericPoint

section Algebra

variable {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K]
variable {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
variable (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK)

/-- The relation saying that generic-fibre images multiply to the prescribed third point. -/
def MulRel {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (a b τ : SchemeHomOver t f) : Prop :=
  NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f t τ) e =
    LXK.mul (pullback.snd t (specGenericFibreInclusion R K))
      (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f t a) e)
      (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f t b) e)

variable {K LXK f e}

theorem grj_comp_eq {B T' T A : Scheme.{u}} {t : T ⟶ B} {t' : T' ⟶ B} {g : A ⟶ B}
    (ψ : SchemeHomOver t' t) (x : SchemeHomOver t g) :
    GoodReductionJacobian.schemeHomOverComp ψ.1 ψ.2 x = NeronModelInfra.schemeHomOverComp ψ x := rfl

theorem MulRel.comp {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec
    (CommRingCat.of R)}
    {a b τ : SchemeHomOver t f} (h : MulRel K LXK f e a b τ) (ψ : SchemeHomOver t' t) :
    MulRel K LXK f e (NeronModelInfra.schemeHomOverComp ψ a) (NeronModelInfra.schemeHomOverComp ψ b)
      (NeronModelInfra.schemeHomOverComp ψ τ) := by
  unfold MulRel at h ⊢
  have h2 := congrArg (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K t t' ψ)) h
  rw [← schemeHomOverComp_assoc, ← genericFibreRestrict_schemeHomOverComp] at h2
  rw [h2, ← grj_comp_eq, LXK.mul_natural, grj_comp_eq, grj_comp_eq, ← schemeHomOverComp_assoc,
    ← schemeHomOverComp_assoc, ← genericFibreRestrict_schemeHomOverComp, ←
      genericFibreRestrict_schemeHomOverComp]

theorem comp_e_injective [IsIso e.1] {S : Scheme.{u}} {s : S ⟶ Spec (CommRingCat.of K)}
    {x y : SchemeHomOver s (pullback.snd f (specGenericFibreInclusion R K))}
    (h : NeronModelInfra.schemeHomOverComp x e = NeronModelInfra.schemeHomOverComp y e) : x = y :=
      by
  apply Subtype.ext
  rw [← cancel_mono e.1]
  exact congrArg Subtype.val h

theorem MulRel.gfr_assoc [IsIso e.1] {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {a b c ab bc abc₁ abc₂ : SchemeHomOver t f}
    (h₁ : MulRel K LXK f e a b ab) (h₂ : MulRel K LXK f e b c bc)
    (h₃ : MulRel K LXK f e ab c abc₁) (h₄ : MulRel K LXK f e a bc abc₂) :
    genericFibreRestrict R K f t abc₁ = genericFibreRestrict R K f t abc₂ := by
  apply comp_e_injective (e := e)
  unfold MulRel at h₁ h₂ h₃ h₄
  rw [h₃, h₄, h₁, h₂, LXK.mul_assoc]

theorem fst_comp_eq_of_gfr_eq {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {x y :
    SchemeHomOver t f}
    (h : genericFibreRestrict R K f t x = genericFibreRestrict R K f t y) :
    pullback.fst t (specGenericFibreInclusion R K) ≫ x.1 =
      pullback.fst t (specGenericFibreInclusion R K) ≫ y.1 := by
  rw [← genericFibreRestrict_coe_comp_fst, ← genericFibreRestrict_coe_comp_fst, h]

theorem mulRel_iff_display (U : (pullback f f).Opens) (τ : SchemeHomOver (U.ι ≫ pullback.fst f f ≫
    f) f)
    (c d : SchemeHomOver (pullback.fst f f ≫ f) f) :
    MulRel K LXK f e
      (NeronModelInfra.schemeHomOverComp (⟨U.ι, rfl⟩ : SchemeHomOver (U.ι ≫ pullback.fst f f ≫ f) _)
        c)
      (NeronModelInfra.schemeHomOverComp (⟨U.ι, rfl⟩ : SchemeHomOver (U.ι ≫ pullback.fst f f ≫ f) _)
        d) τ ↔
    (NeronModelInfra.schemeHomOverComp
        (genericFibreRestrict R K f (U.ι ≫ pullback.fst f f ≫ f) τ) e).1 =
      pullback.map (U.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
          (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
        (LXK.mul (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
          (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f (pullback.fst f f ≫ f) c)
            e)
          (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f (pullback.fst f f ≫ f) d)
            e)).1 := by
  set incl : SchemeHomOver (U.ι ≫ pullback.fst f f ≫ f) (pullback.fst f f ≫ f) := ⟨U.ι, rfl⟩
  have hmap : pullback.map (U.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
      (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
      (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) =
      (genericFibreRestrict R K (pullback.fst f f ≫ f) _ incl).1 :=
    (genericFibreRestrict_coe_eq_pullbackMap _ _ incl _ _).symm
  have key : (genericFibreRestrict R K (pullback.fst f f ≫ f) _ incl).1 ≫
      (LXK.mul (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
        (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f (pullback.fst f f ≫ f) c) e)
        (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f (pullback.fst f f ≫ f) d)
          e)).1 =
      (LXK.mul (pullback.snd (U.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
        (NeronModelInfra.schemeHomOverComp
          (genericFibreRestrict R K f _ (NeronModelInfra.schemeHomOverComp incl c)) e)
        (NeronModelInfra.schemeHomOverComp
          (genericFibreRestrict R K f _ (NeronModelInfra.schemeHomOverComp incl d)) e)).1 := by
    have h := congrArg Subtype.val (LXK.mul_natural _ _ (genericFibreRestrict R K (pullback.fst f f
      ≫ f) _ incl).1
      (genericFibreRestrict R K (pullback.fst f f ≫ f) _ incl).2
      (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f (pullback.fst f f ≫ f) c) e)
      (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f (pullback.fst f f ≫ f) d) e))
    rw [GoodReductionJacobian.schemeHomOverComp_coe] at h
    rw [h, grj_comp_eq, grj_comp_eq, ← schemeHomOverComp_assoc, ← schemeHomOverComp_assoc,
      ← genericFibreRestrict_schemeHomOverComp, ← genericFibreRestrict_schemeHomOverComp]
  rw [hmap, key, MulRel]
  exact Subtype.ext_iff

theorem mulRel_of_display (W : (pullback f f).Opens) (m : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f)
    f)
    (hmK : (NeronModelInfra.schemeHomOverComp
        (genericFibreRestrict R K f (W.ι ≫ pullback.fst f f ≫ f) m) e).1 =
      pullback.map (W.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
          (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) W.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
        (LXK.mul (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩) e)
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (pullback.fst f f ≫ f)
              ⟨pullback.snd f f, pullback.condition.symm⟩) e)).1)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (w : SchemeHomOver t (W.ι ≫ pullback.fst f f ≫ f)) (a b τ : SchemeHomOver t f)
    (ha : a.1 = w.1 ≫ W.ι ≫ pullback.fst f f) (hb : b.1 = w.1 ≫ W.ι ≫ pullback.snd f f)
    (hτ : τ.1 = w.1 ≫ m.1) : MulRel K LXK f e a b τ := by
  have relm := ((mulRel_iff_display (K := K) (LXK := LXK) (e := e) W m ⟨pullback.fst f f, rfl⟩
    ⟨pullback.snd f f, pullback.condition.symm⟩).mpr hmK).comp w
  have ea : a = NeronModelInfra.schemeHomOverComp w
      (NeronModelInfra.schemeHomOverComp (⟨W.ι, rfl⟩ : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) _)
        (⟨pullback.fst f f, rfl⟩ : SchemeHomOver (pullback.fst f f ≫ f) f)) :=
    Subtype.ext (by rw [ha]; rfl)
  have eb : b = NeronModelInfra.schemeHomOverComp w
      (NeronModelInfra.schemeHomOverComp (⟨W.ι, rfl⟩ : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) _)
        (⟨pullback.snd f f, pullback.condition.symm⟩ : SchemeHomOver (pullback.fst f f ≫ f) f)) :=
    Subtype.ext (by rw [hb]; rfl)
  have eτ : τ = NeronModelInfra.schemeHomOverComp w m := Subtype.ext (by rw [hτ]; rfl)
  rw [ea, eb, eτ]
  exact relm

end Algebra

section Restrict

variable {R : Type u} [CommRing R]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
variable (W : (pullback f f).Opens) (m : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f)
variable (X' : X.Opens) (U : (pullback f f).Opens) (hUW : U ≤ W)

/-- The product map induced by an open subscheme inclusion. -/
def jj : pullback (X'.ι ≫ f) (X'.ι ≫ f) ⟶ pullback f f :=
  pullback.map (X'.ι ≫ f) (X'.ι ≫ f) f f X'.ι X'.ι (𝟙 _) (Category.comp_id _) (Category.comp_id _)

@[reassoc (attr := simp)]
theorem jj_fst : jj f X' ≫ pullback.fst f f = pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) ≫ X'.ι :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem jj_snd : jj f X' ≫ pullback.snd f f = pullback.snd (X'.ι ≫ f) (X'.ι ≫ f) ≫ X'.ι :=
  pullback.lift_snd _ _ _

scoped instance isOpenImmersion_jj : IsOpenImmersion (jj f X') :=
  MorphismProperty.pullbackMap (P := @IsOpenImmersion) (f := X'.ι ≫ f) (g := X'.ι ≫ f) (f' := f) (g'
    := f)
    (i₁ := X'.ι) (i₂ := X'.ι) inferInstance inferInstance rfl rfl

theorem range_jj : Set.range (jj f X').base =
    {q | (pullback.fst f f).base q ∈ X' ∧ (pullback.snd f f).base q ∈ X'} := by
  rw [jj, Scheme.Pullback.range_map, Scheme.Opens.range_ι]
  rfl

theorem jj_injective : Function.Injective (jj f X').base := (jj f X').isOpenEmbedding.injective

theorem fst_jj_apply (q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f))) :
    (pullback.fst f f).base ((jj f X').base q) = X'.ι.base ((pullback.fst (X'.ι ≫ f) (X'.ι ≫
      f)).base q) := by
  rw [← Scheme.Hom.comp_apply, jj_fst, Scheme.Hom.comp_apply]

theorem snd_jj_apply (q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f))) :
    (pullback.snd f f).base ((jj f X').base q) = X'.ι.base ((pullback.snd (X'.ι ≫ f) (X'.ι ≫
      f)).base q) := by
  rw [← Scheme.Hom.comp_apply, jj_snd, Scheme.Hom.comp_apply]

/-- The multiplication domain pulled back to the chosen open subscheme product. -/
def UY : (pullback (X'.ι ≫ f) (X'.ι ≫ f)).Opens := jj f X' ⁻¹ᵁ U

theorem mem_UY (q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f))) : q ∈ UY f X' U ↔ (jj f X').base q ∈ U :=
    Iff.rfl

theorem coe_UY : (UY f X' U : Set ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f))) = (jj f X').base ⁻¹' (U : Set
    _) := rfl

theorem range_UYι_jj : Set.range ((UY f X' U).ι ≫ jj f X').base ⊆ Set.range U.ι.base := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨z, rfl⟩
  rw [Scheme.Hom.comp_apply]
  exact z.2

/-- Restrict the product inclusion to the chosen multiplication domain. -/
def w₀ : (UY f X' U : Scheme.{u}) ⟶ (U : Scheme.{u}) :=
  IsOpenImmersion.lift U.ι ((UY f X' U).ι ≫ jj f X') (range_UYι_jj f X' U)

@[reassoc (attr := simp)]
theorem w₀_ι : w₀ f X' U ≫ U.ι = (UY f X' U).ι ≫ jj f X' := IsOpenImmersion.lift_fac _ _ _

scoped instance isOpenImmersion_w₀ : IsOpenImmersion (w₀ f X' U) := by
  have : IsOpenImmersion (w₀ f X' U ≫ U.ι) := by rw [w₀_ι]; infer_instance
  exact IsOpenImmersion.of_comp _ U.ι

/-- Map the restricted multiplication domain into the original domain. -/
def θ : (UY f X' U : Scheme.{u}) ⟶ (W : Scheme.{u}) := w₀ f X' U ≫ (pullback f f).homOfLE hUW

@[reassoc (attr := simp)]
theorem θ_ι : θ f W X' U hUW ≫ W.ι = (UY f X' U).ι ≫ jj f X' := by
  rw [θ, Category.assoc, Scheme.homOfLE_ι, w₀_ι]

scoped instance isOpenImmersion_θ : IsOpenImmersion (θ f W X' U hUW) := by
  unfold θ; infer_instance

theorem θ_apply_coe (z : ↥(UY f X' U)) :
    ((θ f W X' U hUW).base z).1 = (jj f X').base z.1 := by
  exact congrArg (fun g : (UY f X' U : Scheme.{u}) ⟶ pullback f f => g.base z)
    (θ_ι f W X' U hUW)

variable (hU₂ : ∀ (q : ↑(pullback f f)) (hq : q ∈ U), (pullback.fst f f).base q ∈ X' ∧
  (pullback.snd f f).base q ∈ X' ∧ m.1.base ⟨q, hUW hq⟩ ∈ X')

include hU₂ in
theorem U_subset_range_jj : (U : Set ↑(pullback f f)) ⊆ Set.range (jj f X').base := by
  intro q hq
  rw [range_jj]
  exact ⟨(hU₂ q hq).1, (hU₂ q hq).2.1⟩

include hU₂ in
theorem range_θ : Set.range (θ f W X' U hUW).base = {w | W.ι.base w ∈ U} := by
  ext w
  constructor
  · rintro ⟨z, rfl⟩
    change ((θ f W X' U hUW).base z).1 ∈ U
    exact (θ_apply_coe f W X' U hUW z).symm ▸ z.2
  · intro hw
    obtain ⟨q', hq'⟩ := U_subset_range_jj f W m X' U hUW hU₂ hw
    have hq'U : q' ∈ UY f X' U := by
      change (jj f X').base q' ∈ U
      rw [hq']
      exact hw
    refine ⟨⟨q', hq'U⟩, ?_⟩
    apply Subtype.ext
    rw [θ_apply_coe]
    exact hq'

include hU₂ in
theorem range_θm : Set.range (θ f W X' U hUW ≫ m.1).base ⊆ Set.range X'.ι.base := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨z, rfl⟩
  rw [Scheme.Hom.comp_apply]
  have hz : (jj f X').base z.1 ∈ U := z.2
  have key := (hU₂ _ hz).2.2
  have hθz : (θ f W X' U hUW).base z = ⟨(jj f X').base z.1, hUW hz⟩ := Subtype.ext (θ_apply_coe f W
    X' U hUW z)
  rw [hθz]
  exact key

/-- The multiplication map with codomain restricted to the chosen open subscheme. -/
def mY₁ : (UY f X' U : Scheme.{u}) ⟶ (X' : Scheme.{u}) :=
  IsOpenImmersion.lift X'.ι (θ f W X' U hUW ≫ m.1) (range_θm f W m X' U hUW hU₂)

@[reassoc (attr := simp)]
theorem mY₁_ι : mY₁ f W m X' U hUW hU₂ ≫ X'.ι = θ f W X' U hUW ≫ m.1 := IsOpenImmersion.lift_fac _ _
    _

theorem mY₁_over : mY₁ f W m X' U hUW hU₂ ≫ (X'.ι ≫ f) =
    (UY f X' U).ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) ≫ (X'.ι ≫ f) := by
  rw [mY₁_ι_assoc, m.2, θ_ι_assoc, jj_fst_assoc]

/-- The restricted multiplication map as a morphism over the base. -/
def mY : SchemeHomOver ((UY f X' U).ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) ≫ (X'.ι ≫ f)) (X'.ι ≫ f)
    :=
  ⟨mY₁ f W m X' U hUW hU₂, mY₁_over f W m X' U hUW hU₂⟩

theorem mY_coe : (mY f W m X' U hUW hU₂).1 = mY₁ f W m X' U hUW hU₂ := rfl

/-- The first-input and product map for the restricted multiplication. -/
def PhiY : (UY f X' U : Scheme.{u}) ⟶ pullback (X'.ι ≫ f) (X'.ι ≫ f) :=
  pullback.lift (f := (X'.ι ≫ f)) (g := (X'.ι ≫ f)) ((UY f X' U).ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫
    f))
    (mY f W m X' U hUW hU₂).1 ((Category.assoc _ _ _).trans (mY f W m X' U hUW hU₂).2.symm)

/-- The product and second-input map for the restricted multiplication. -/
def PsiY : (UY f X' U : Scheme.{u}) ⟶ pullback (X'.ι ≫ f) (X'.ι ≫ f) :=
  pullback.lift (f := (X'.ι ≫ f)) (g := (X'.ι ≫ f)) (mY f W m X' U hUW hU₂).1
    ((UY f X' U).ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f))
    ((mY f W m X' U hUW hU₂).2.trans (by rw [Category.assoc, pullback.condition]))

@[reassoc (attr := simp)]
theorem PhiY_fst : PhiY f W m X' U hUW hU₂ ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) =
    (UY f X' U).ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem PhiY_snd : PhiY f W m X' U hUW hU₂ ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f) =
    mY₁ f W m X' U hUW hU₂ := pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem PsiY_fst : PsiY f W m X' U hUW hU₂ ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) =
    mY₁ f W m X' U hUW hU₂ := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem PsiY_snd : PsiY f W m X' U hUW hU₂ ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f) =
    (UY f X' U).ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f) := pullback.lift_snd _ _ _

/-- The chart map recording the first input and its product. -/
def Phi : (W : Scheme.{u}) ⟶ pullback f f :=
  pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1 ((Category.assoc _ _ _).trans
    m.2.symm)

/-- The chart map recording the product and the second input. -/
def Psi : (W : Scheme.{u}) ⟶ pullback f f :=
  pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
    (m.2.trans (by rw [Category.assoc, pullback.condition]))

@[reassoc (attr := simp)]
theorem Phi_fst : Phi f W m ≫ pullback.fst f f = W.ι ≫ pullback.fst f f := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem Phi_snd : Phi f W m ≫ pullback.snd f f = m.1 := pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem Psi_fst : Psi f W m ≫ pullback.fst f f = m.1 := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem Psi_snd : Psi f W m ≫ pullback.snd f f = W.ι ≫ pullback.snd f f := pullback.lift_snd _ _ _

theorem PhiY_jj : PhiY f W m X' U hUW hU₂ ≫ jj f X' = θ f W X' U hUW ≫ Phi f W m := by
  apply pullback.hom_ext
  · rw [Category.assoc, jj_fst, PhiY_fst_assoc, Category.assoc, Phi_fst, θ_ι_assoc, jj_fst]
  · rw [Category.assoc, jj_snd, PhiY_snd_assoc, mY₁_ι, Category.assoc, Phi_snd]

theorem PsiY_jj : PsiY f W m X' U hUW hU₂ ≫ jj f X' = θ f W X' U hUW ≫ Psi f W m := by
  apply pullback.hom_ext
  · rw [Category.assoc, jj_fst, PsiY_fst_assoc, mY₁_ι, Category.assoc, Psi_fst]
  · rw [Category.assoc, jj_snd, PsiY_snd_assoc, Category.assoc, Psi_snd, θ_ι_assoc, jj_snd]

theorem isOpenImmersion_PhiY (hΦ : IsOpenImmersion (Phi f W m)) : IsOpenImmersion (PhiY f W m X' U
    hUW hU₂) := by
  have : IsOpenImmersion (PhiY f W m X' U hUW hU₂ ≫ jj f X') := by rw [PhiY_jj]; infer_instance
  exact IsOpenImmersion.of_comp _ (jj f X')

theorem isOpenImmersion_PsiY (hΨ : IsOpenImmersion (Psi f W m)) : IsOpenImmersion (PsiY f W m X' U
    hUW hU₂) := by
  have : IsOpenImmersion (PsiY f W m X' U hUW hU₂ ≫ jj f X') := by rw [PsiY_jj]; infer_instance
  exact IsOpenImmersion.of_comp _ (jj f X')

theorem range_comp_base {A B C : Scheme.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) :
    Set.range (φ ≫ ψ).base = ψ.base '' Set.range φ.base := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]

include hU₂ in
theorem image_Phi_eq : (Phi f W m).base '' {w | W.ι.base w ∈ U} =
    (jj f X').base '' Set.range (PhiY f W m X' U hUW hU₂).base := by
  rw [← range_θ f W m X' U hUW hU₂, ← range_comp_base, ← range_comp_base, PhiY_jj]

include hU₂ in
theorem image_Psi_eq : (Psi f W m).base '' {w | W.ι.base w ∈ U} =
    (jj f X').base '' Set.range (PsiY f W m X' U hUW hU₂).base := by
  rw [← range_θ f W m X' U hUW hU₂, ← range_comp_base, ← range_comp_base, PsiY_jj]

variable (hU₃ : ∀ x : X, x ∈ X' →
    Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = x} → ↑(pullback f f))
      ⁻¹'
        (U : Set ↑(pullback f f))) ∧
    Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.snd f f).base q = x} → ↑(pullback f f))
      ⁻¹'
        (U : Set ↑(pullback f f))) ∧
    Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = x} → ↑(pullback f f))
      ⁻¹'
        ((Phi f W m).base '' {w | W.ι.base w ∈ U})) ∧
    Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.snd f f).base q = x} → ↑(pullback f f))
      ⁻¹'
        ((Phi f W m).base '' {w | W.ι.base w ∈ U})) ∧
    Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = x} → ↑(pullback f f))
      ⁻¹'
        ((Psi f W m).base '' {w | W.ι.base w ∈ U})) ∧
    Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.snd f f).base q = x} → ↑(pullback f f))
      ⁻¹'
        ((Psi f W m).base '' {w | W.ι.base w ∈ U})))

theorem X'ι_injective : Function.Injective X'.ι.base := X'.ι.isOpenEmbedding.injective

include hU₂ hU₃ in
theorem dense_UY_fst (x : ↥X') :
    Dense ((Subtype.val : {q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f)) //
      (pullback.fst (X'.ι ≫ f) (X'.ι ≫ f)).base q = x} → _) ⁻¹' (UY f X' U : Set _)) :=
  dense_fibre_transfer (jj f X').isOpenEmbedding _ _ X'.ι.base (X'ι_injective X') (fst_jj_apply f
    X')
    (U_subset_range_jj f W m X' U hUW hU₂) (coe_UY f X' U) x (hU₃ x.1 x.2).1

include hU₂ hU₃ in
theorem dense_UY_snd (x : ↥X') :
    Dense ((Subtype.val : {q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f)) //
      (pullback.snd (X'.ι ≫ f) (X'.ι ≫ f)).base q = x} → _) ⁻¹' (UY f X' U : Set _)) :=
  dense_fibre_transfer (jj f X').isOpenEmbedding _ _ X'.ι.base (X'ι_injective X') (snd_jj_apply f
    X')
    (U_subset_range_jj f W m X' U hUW hU₂) (coe_UY f X' U) x (hU₃ x.1 x.2).2.1

theorem range_PhiY_eq : Set.range (PhiY f W m X' U hUW hU₂).base =
    (jj f X').base ⁻¹' ((Phi f W m).base '' {w | W.ι.base w ∈ U}) := by
  rw [image_Phi_eq f W m X' U hUW hU₂, Set.preimage_image_eq _ (jj_injective f X')]

theorem range_PsiY_eq : Set.range (PsiY f W m X' U hUW hU₂).base =
    (jj f X').base ⁻¹' ((Psi f W m).base '' {w | W.ι.base w ∈ U}) := by
  rw [image_Psi_eq f W m X' U hUW hU₂, Set.preimage_image_eq _ (jj_injective f X')]

include hUW hU₂ in
theorem image_Phi_subset : (Phi f W m).base '' {w | W.ι.base w ∈ U} ⊆ Set.range (jj f X').base := by
  rw [image_Phi_eq f W m X' U hUW hU₂]
  exact Set.image_subset_range _ _

include hUW hU₂ in
theorem image_Psi_subset : (Psi f W m).base '' {w | W.ι.base w ∈ U} ⊆ Set.range (jj f X').base := by
  rw [image_Psi_eq f W m X' U hUW hU₂]
  exact Set.image_subset_range _ _

include hU₃ in
theorem dense_PhiY_fst (x : ↥X') :
    Dense ((Subtype.val : {q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f)) //
      (pullback.fst (X'.ι ≫ f) (X'.ι ≫ f)).base q = x} → _) ⁻¹' Set.range (PhiY f W m X' U hUW
        hU₂).base) :=
  dense_fibre_transfer (jj f X').isOpenEmbedding _ _ X'.ι.base (X'ι_injective X') (fst_jj_apply f
    X')
    (image_Phi_subset f W m X' U hUW hU₂) (range_PhiY_eq f W m X' U hUW hU₂) x (hU₃ x.1 x.2).2.2.1

include hU₃ in
theorem dense_PhiY_snd (x : ↥X') :
    Dense ((Subtype.val : {q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f)) //
      (pullback.snd (X'.ι ≫ f) (X'.ι ≫ f)).base q = x} → _) ⁻¹' Set.range (PhiY f W m X' U hUW
        hU₂).base) :=
  dense_fibre_transfer (jj f X').isOpenEmbedding _ _ X'.ι.base (X'ι_injective X') (snd_jj_apply f
    X')
    (image_Phi_subset f W m X' U hUW hU₂) (range_PhiY_eq f W m X' U hUW hU₂) x (hU₃ x.1 x.2).2.2.2.1

include hU₃ in
theorem dense_PsiY_fst (x : ↥X') :
    Dense ((Subtype.val : {q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f)) //
      (pullback.fst (X'.ι ≫ f) (X'.ι ≫ f)).base q = x} → _) ⁻¹' Set.range (PsiY f W m X' U hUW
        hU₂).base) :=
  dense_fibre_transfer (jj f X').isOpenEmbedding _ _ X'.ι.base (X'ι_injective X') (fst_jj_apply f
    X')
    (image_Psi_subset f W m X' U hUW hU₂) (range_PsiY_eq f W m X' U hUW hU₂) x
    (hU₃ x.1 x.2).2.2.2.2.1

include hU₃ in
theorem dense_PsiY_snd (x : ↥X') :
    Dense ((Subtype.val : {q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f)) //
      (pullback.snd (X'.ι ≫ f) (X'.ι ≫ f)).base q = x} → _) ⁻¹' Set.range (PsiY f W m X' U hUW
        hU₂).base) :=
  dense_fibre_transfer (jj f X').isOpenEmbedding _ _ X'.ι.base (X'ι_injective X') (snd_jj_apply f
    X')
    (image_Psi_subset f W m X' U hUW hU₂) (range_PsiY_eq f W m X' U hUW hU₂) x
    (hU₃ x.1 x.2).2.2.2.2.2

theorem mem_UY_of_ne_closedPoint [IsLocalRing R]
    (hU₁ : ∀ q : ↑(pullback f f), (pullback.fst f f ≫ f).base q ≠ IsLocalRing.closedPoint R → q ∈ U)
    (q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f)))
    (hq : (pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) ≫ (X'.ι ≫ f)).base q ≠ IsLocalRing.closedPoint R) :
    q ∈ UY f X' U := by
  change (jj f X').base q ∈ U
  apply hU₁
  have h : (pullback.fst f f ≫ f).base ((jj f X').base q) =
      (pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) ≫ (X'.ι ≫ f)).base q := by
    rw [← Scheme.Hom.comp_apply, ← Category.assoc, jj_fst, Category.assoc]
  rw [h]
  exact hq

theorem restrict_clause {T : Scheme.{u}} (w : T ⟶ (U : Scheme.{u})) (a b : T ⟶ (X' : Scheme.{u}))
    (ha : a ≫ X'.ι = w ≫ U.ι ≫ pullback.fst f f) (hb : b ≫ X'.ι = w ≫ U.ι ≫ pullback.snd f f) :
    ∃ v : T ⟶ (UY f X' U : Scheme.{u}),
      v ≫ (UY f X' U).ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) = a ∧
      v ≫ (UY f X' U).ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f) = b ∧
      v ≫ (mY f W m X' U hUW hU₂).1 ≫ X'.ι = w ≫ (pullback f f).homOfLE hUW ≫ m.1 := by
  have hab : a ≫ (X'.ι ≫ f) = b ≫ (X'.ι ≫ f) := by
    rw [reassoc_of% ha, reassoc_of% hb, pullback.condition]
  let v₀ : T ⟶ pullback (X'.ι ≫ f) (X'.ι ≫ f) := pullback.lift a b hab
  have hv₀ : v₀ ≫ jj f X' = w ≫ U.ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, jj_fst, pullback.lift_fst_assoc, ha, Category.assoc]
    · rw [Category.assoc, jj_snd, pullback.lift_snd_assoc, hb, Category.assoc]
  have hr : Set.range v₀.base ⊆ Set.range (UY f X' U).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change (jj f X').base (v₀.base x) ∈ U
    rw [← Scheme.Hom.comp_apply, hv₀, Scheme.Hom.comp_apply]
    exact (w.base x).2
  let v : T ⟶ (UY f X' U : Scheme.{u}) := IsOpenImmersion.lift (UY f X' U).ι v₀ hr
  have hv : v ≫ (UY f X' U).ι = v₀ := IsOpenImmersion.lift_fac _ _ _
  have hvw : v ≫ w₀ f X' U = w := by
    rw [← cancel_mono U.ι, Category.assoc, w₀_ι, reassoc_of% hv, hv₀]
  refine ⟨v, ?_, ?_, ?_⟩
  · rw [reassoc_of% hv, pullback.lift_fst]
  · rw [reassoc_of% hv, pullback.lift_snd]
  · rw [mY_coe, mY₁_ι, θ, Category.assoc, reassoc_of% hvw]

end Restrict

section AssocFrame

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
variable (D : (pullback y y).Opens) (M : SchemeHomOver (D.ι ≫ pullback.fst y y ≫ y) y)

/-- The space of two composable pairs in the partial multiplication domain. -/
abbrev DD : Scheme.{u} := pullback (D.ι ≫ pullback.snd y y) (D.ι ≫ pullback.fst y y)

/-- The first composable pair. -/
abbrev Q12 : DD y D ⟶ D := pullback.fst (D.ι ≫ pullback.snd y y) (D.ι ≫ pullback.fst y y)

/-- The second composable pair. -/
abbrev Q23 : DD y D ⟶ D := pullback.snd (D.ι ≫ pullback.snd y y) (D.ι ≫ pullback.fst y y)

@[reassoc]
theorem Q12_snd : Q12 y D ≫ D.ι ≫ pullback.snd y y = Q23 y D ≫ D.ι ≫ pullback.fst y y :=
  pullback.condition

@[reassoc]
theorem fst_y : pullback.fst y y ≫ y = pullback.snd y y ≫ y :=
  pullback.condition

@[reassoc]
theorem M_y : M.1 ≫ y = D.ι ≫ pullback.fst y y ≫ y := M.2

/-- Multiply the first pair and retain the remaining coordinate. -/
def mulFst : DD y D ⟶ pullback y y :=
  pullback.lift (f := y) (g := y) (Q12 y D ≫ M.1) (Q23 y D ≫ D.ι ≫ pullback.snd y y)
    (by simp only [Category.assoc, M_y, fst_y, Q12_snd_assoc])

/-- Retain the first coordinate and multiply the second pair. -/
def mulSnd : DD y D ⟶ pullback y y :=
  pullback.lift (f := y) (g := y) (Q12 y D ≫ D.ι ≫ pullback.fst y y) (Q23 y D ≫ M.1)
    (by simp only [Category.assoc, M_y, fst_y, Q12_snd_assoc])

@[reassoc (attr := simp)]
theorem mulFst_fst : mulFst y D M ≫ pullback.fst y y = Q12 y D ≫ M.1 := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem mulFst_snd : mulFst y D M ≫ pullback.snd y y = Q23 y D ≫ D.ι ≫ pullback.snd y y :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem mulSnd_fst : mulSnd y D M ≫ pullback.fst y y = Q12 y D ≫ D.ι ≫ pullback.fst y y :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem mulSnd_snd : mulSnd y D M ≫ pullback.snd y y = Q23 y D ≫ M.1 := pullback.lift_snd _ _ _

/-- The open locus on which both iterated products are defined. -/
def A : (DD y D).Opens := mulFst y D M ⁻¹ᵁ D ⊓ mulSnd y D M ⁻¹ᵁ D

theorem mem_A (x : ↑(DD y D)) : x ∈ A y D M ↔ (mulFst y D M).base x ∈ D ∧ (mulSnd y D M).base x ∈ D
    := by
  simp only [A, TopologicalSpace.Opens.mem_inf, Scheme.Hom.mem_preimage]

theorem range_A_mulFst : Set.range ((A y D M).ι ≫ mulFst y D M).base ⊆ Set.range D.ι.base := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨x, rfl⟩
  exact ((mem_A y D M x.1).mp x.2).1

theorem range_A_mulSnd : Set.range ((A y D M).ι ≫ mulSnd y D M).base ⊆ Set.range D.ι.base := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨x, rfl⟩
  exact ((mem_A y D M x.1).mp x.2).2

/-- The first intermediate product viewed in the multiplication domain. -/
def dF : (A y D M : Scheme.{u}) ⟶ D :=
  IsOpenImmersion.lift D.ι ((A y D M).ι ≫ mulFst y D M) (range_A_mulFst y D M)

/-- The second intermediate product viewed in the multiplication domain. -/
def dG : (A y D M : Scheme.{u}) ⟶ D :=
  IsOpenImmersion.lift D.ι ((A y D M).ι ≫ mulSnd y D M) (range_A_mulSnd y D M)

@[reassoc (attr := simp)]
theorem dF_ι : dF y D M ≫ D.ι = (A y D M).ι ≫ mulFst y D M := IsOpenImmersion.lift_fac _ _ _

@[reassoc (attr := simp)]
theorem dG_ι : dG y D M ≫ D.ι = (A y D M).ι ≫ mulSnd y D M := IsOpenImmersion.lift_fac _ _ _

/-- The first of the two iterated multiplication maps being compared. -/
def FF : (A y D M : Scheme.{u}) ⟶ Y := dF y D M ≫ M.1

/-- The second of the two iterated multiplication maps being compared. -/
def GG : (A y D M : Scheme.{u}) ⟶ Y := dG y D M ≫ M.1

/-- The structure map of the common iterated-multiplication domain. -/
def tA : (A y D M : Scheme.{u}) ⟶ Spec (CommRingCat.of R) :=
  (A y D M).ι ≫ Q12 y D ≫ D.ι ≫ pullback.fst y y ≫ y

scoped instance smooth_tA [Smooth y] : Smooth (tA y D M) := by
  unfold tA; infer_instance

theorem FF_y : FF y D M ≫ y = tA y D M := by
  simp only [FF, tA, Category.assoc, M_y, dF_ι_assoc, mulFst_fst_assoc]

theorem GG_y : GG y D M ≫ y = tA y D M := by
  simp only [GG, tA, Category.assoc, M_y, dG_ι_assoc, mulSnd_fst_assoc]

theorem assoc_of_FF_eq_GG (hFG : FF y D M = GG y D M)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (u v p q : SchemeHomOver t (D.ι ≫ pullback.fst y y ≫ y))
    (h₁ : u.1 ≫ D.ι ≫ pullback.snd y y = v.1 ≫ D.ι ≫ pullback.fst y y)
    (h₂ : p.1 ≫ D.ι ≫ pullback.fst y y = u.1 ≫ M.1)
    (h₃ : p.1 ≫ D.ι ≫ pullback.snd y y = v.1 ≫ D.ι ≫ pullback.snd y y)
    (h₄ : q.1 ≫ D.ι ≫ pullback.fst y y = u.1 ≫ D.ι ≫ pullback.fst y y)
    (h₅ : q.1 ≫ D.ι ≫ pullback.snd y y = v.1 ≫ M.1) :
    p.1 ≫ M.1 = q.1 ≫ M.1 := by
  let τ₀ : T ⟶ DD y D := pullback.lift u.1 v.1 h₁
  have hF : τ₀ ≫ mulFst y D M = p.1 ≫ D.ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, mulFst_fst, pullback.lift_fst_assoc, Category.assoc, h₂]
    · rw [Category.assoc, mulFst_snd, pullback.lift_snd_assoc, Category.assoc, h₃]
  have hG : τ₀ ≫ mulSnd y D M = q.1 ≫ D.ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, mulSnd_fst, pullback.lift_fst_assoc, Category.assoc, h₄]
    · rw [Category.assoc, mulSnd_snd, pullback.lift_snd_assoc, Category.assoc, h₅]
  have hr : Set.range τ₀.base ⊆ Set.range (A y D M).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    refine (mem_A y D M _).mpr ⟨?_, ?_⟩
    · rw [← Scheme.Hom.comp_apply, hF]
      exact (p.1.base x).2
    · rw [← Scheme.Hom.comp_apply, hG]
      exact (q.1.base x).2
  let τ : T ⟶ A y D M := IsOpenImmersion.lift (A y D M).ι τ₀ hr
  have hτ : τ ≫ (A y D M).ι = τ₀ := IsOpenImmersion.lift_fac _ _ _
  have hp : p.1 = τ ≫ dF y D M := by
    rw [← cancel_mono D.ι, Category.assoc, dF_ι, reassoc_of% hτ, hF]
  have hq : q.1 = τ ≫ dG y D M := by
    rw [← cancel_mono D.ι, Category.assoc, dG_ι, reassoc_of% hτ, hG]
  have key := congrArg (fun φ => τ ≫ φ) hFG
  simp only [FF, GG] at key
  rw [hp, hq, Category.assoc, Category.assoc]
  exact key

end AssocFrame

section Assoc

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
variable {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
variable [Smooth f] [IsSeparated f]
variable (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsIso e.1]
variable (W : (pullback f f).Opens) (m : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f)
variable (hmK : (NeronModelInfra.schemeHomOverComp
        (genericFibreRestrict R K f (W.ι ≫ pullback.fst f f ≫ f) m) e).1 =
      pullback.map (W.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
          (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) W.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
        (LXK.mul (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩) e)
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (pullback.fst f f ≫ f)
              ⟨pullback.snd f f, pullback.condition.symm⟩) e)).1)
variable (X' : X.Opens) (U : (pullback f f).Opens) (hUW : U ≤ W)
variable (hU₂ : ∀ (q : ↑(pullback f f)) (hq : q ∈ U), (pullback.fst f f).base q ∈ X' ∧
  (pullback.snd f f).base q ∈ X' ∧ m.1.base ⟨q, hUW hq⟩ ∈ X')

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [Smooth f] [IsSeparated f] [IsIso
    e.1] in
include hmK in
theorem mulRel_UY {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (z : T ⟶ (UY f X' U : Scheme.{u})) (a b τ : SchemeHomOver t f)
    (ha : a.1 = z ≫ (UY f X' U).ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) ≫ X'.ι)
    (hb : b.1 = z ≫ (UY f X' U).ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f) ≫ X'.ι)
    (hτ : τ.1 = z ≫ (mY f W m X' U hUW hU₂).1 ≫ X'.ι) : MulRel K LXK f e a b τ := by
  have hw : (z ≫ θ f W X' U hUW) ≫ W.ι ≫ pullback.fst f f ≫ f = t := by
    rw [← a.2, ha]
    simp only [Category.assoc, θ_ι_assoc, jj_fst_assoc]
  refine mulRel_of_display W m hmK ⟨z ≫ θ f W X' U hUW, hw⟩ a b τ ?_ ?_ ?_
  · rw [ha, Category.assoc, θ_ι_assoc, jj_fst]
  · rw [hb, Category.assoc, θ_ι_assoc, jj_snd]
  · rw [hτ, mY_coe, mY₁_ι, Category.assoc]

include hmK in
theorem FF_eq_GG :
    FF (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂) = GG (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW
      hU₂) := by
  have : IsReduced (A (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂) : Scheme.{u}) :=
    AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian
      (tA (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂))
  have : IsDominant (pullback.fst (tA (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂))
      (specGenericFibreInclusion R K)) :=
    isDominant_fst_specGenericFibreInclusion _
  refine ext_of_isDominant_of_isSeparated (X'.ι ≫ f) ?_
    (pullback.fst (tA (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂)) (specGenericFibreInclusion R
      K)) ?_
  · rw [FF_y, GG_y]
  let t : (A (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂) : Scheme.{u}) ⟶ Spec (CommRingCat.of R)
    :=
    tA (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂)
  have ht : t = (A (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂)).ι ≫ Q12 (X'.ι ≫ f) (UY f X' U) ≫
      (UY f X' U).ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) ≫ X'.ι ≫ f := rfl
  let a : SchemeHomOver t f :=
    ⟨(A (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂)).ι ≫ Q12 (X'.ι ≫ f) (UY f X' U) ≫ (UY f X'
      U).ι ≫
      pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) ≫ X'.ι, by simp only [Category.assoc, ht]⟩
  have ha : a.1 = (A (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂)).ι ≫ Q12 (X'.ι ≫ f) (UY f X' U)
    ≫
      (UY f X' U).ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) ≫ X'.ι := rfl
  let b : SchemeHomOver t f :=
    ⟨(A (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂)).ι ≫ Q12 (X'.ι ≫ f) (UY f X' U) ≫ (UY f X'
      U).ι ≫
      pullback.snd (X'.ι ≫ f) (X'.ι ≫ f) ≫ X'.ι, by
        simp only [Category.assoc, ht]
        rw [← fst_y (X'.ι ≫ f)]⟩
  have hb : b.1 = (A (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂)).ι ≫ Q12 (X'.ι ≫ f) (UY f X' U)
    ≫
      (UY f X' U).ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f) ≫ X'.ι := rfl
  let c : SchemeHomOver t f :=
    ⟨(A (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂)).ι ≫ Q23 (X'.ι ≫ f) (UY f X' U) ≫ (UY f X'
      U).ι ≫
      pullback.snd (X'.ι ≫ f) (X'.ι ≫ f) ≫ X'.ι, by
        simp only [Category.assoc, ht]
        rw [← fst_y (X'.ι ≫ f), ← Q12_snd_assoc (X'.ι ≫ f) (UY f X' U), ← fst_y (X'.ι ≫ f)]⟩
  have hc : c.1 = (A (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂)).ι ≫ Q23 (X'.ι ≫ f) (UY f X' U)
    ≫
      (UY f X' U).ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f) ≫ X'.ι := rfl
  let ab : SchemeHomOver t f :=
    ⟨(A (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂)).ι ≫ Q12 (X'.ι ≫ f) (UY f X' U) ≫
      (mY f W m X' U hUW hU₂).1 ≫ X'.ι, by
        simp only [Category.assoc, ht]
        rw [M_y (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂)]⟩
  have hab : ab.1 = (A (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂)).ι ≫ Q12 (X'.ι ≫ f) (UY f X'
    U) ≫
      (mY f W m X' U hUW hU₂).1 ≫ X'.ι := rfl
  let bc : SchemeHomOver t f :=
    ⟨(A (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂)).ι ≫ Q23 (X'.ι ≫ f) (UY f X' U) ≫
      (mY f W m X' U hUW hU₂).1 ≫ X'.ι, by
        simp only [Category.assoc, ht]
        rw [M_y (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂), ← Q12_snd_assoc (X'.ι ≫ f) (UY f X'
          U),
          ← fst_y (X'.ι ≫ f)]⟩
  have hbc : bc.1 = (A (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂)).ι ≫ Q23 (X'.ι ≫ f) (UY f X'
    U) ≫
      (mY f W m X' U hUW hU₂).1 ≫ X'.ι := rfl
  let abc₁ : SchemeHomOver t f :=
    ⟨FF (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂) ≫ X'.ι, by rw [Category.assoc, FF_y]⟩
  have habc₁ : abc₁.1 = FF (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂) ≫ X'.ι := rfl
  let abc₂ : SchemeHomOver t f :=
    ⟨GG (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂) ≫ X'.ι, by rw [Category.assoc, GG_y]⟩
  have habc₂ : abc₂.1 = GG (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂) ≫ X'.ι := rfl
  have r₁ : MulRel K LXK f e a b ab :=
    mulRel_UY K LXK f e W m hmK X' U hUW hU₂
      ((A (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂)).ι ≫ Q12 (X'.ι ≫ f) (UY f X' U)) a b ab
      (by rw [ha, Category.assoc]) (by rw [hb, Category.assoc]) (by rw [hab, Category.assoc])
  have r₂ : MulRel K LXK f e b c bc :=
    mulRel_UY K LXK f e W m hmK X' U hUW hU₂
      ((A (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂)).ι ≫ Q23 (X'.ι ≫ f) (UY f X' U)) b c bc
      (by rw [hb, Category.assoc, Q12_snd_assoc]) (by rw [hc, Category.assoc]) (by rw [hbc,
        Category.assoc])
  have r₃ : MulRel K LXK f e ab c abc₁ :=
    mulRel_UY K LXK f e W m hmK X' U hUW hU₂ (dF (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂)) ab
      c abc₁
      (by rw [hab, dF_ι_assoc, mulFst_fst_assoc]) (by rw [hc, dF_ι_assoc, mulFst_snd_assoc])
      (by rw [habc₁, FF, Category.assoc])
  have r₄ : MulRel K LXK f e a bc abc₂ :=
    mulRel_UY K LXK f e W m hmK X' U hUW hU₂ (dG (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂)) a
      bc abc₂
      (by rw [ha, dG_ι_assoc, mulSnd_fst_assoc]) (by rw [hbc, dG_ι_assoc, mulSnd_snd_assoc])
      (by rw [habc₂, GG, Category.assoc])
  have key := fst_comp_eq_of_gfr_eq (MulRel.gfr_assoc r₁ r₂ r₃ r₄)
  rw [habc₁, habc₂] at key
  rw [← cancel_mono X'.ι, Category.assoc, Category.assoc]
  exact key

include hmK in
theorem hassocY {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (u v p q : SchemeHomOver t ((UY f X' U).ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) ≫ (X'.ι ≫ f)))
    (h₁ : u.1 ≫ (UY f X' U).ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f) =
      v.1 ≫ (UY f X' U).ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f))
    (h₂ : p.1 ≫ (UY f X' U).ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) = u.1 ≫ (mY f W m X' U hUW
      hU₂).1)
    (h₃ : p.1 ≫ (UY f X' U).ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f) =
      v.1 ≫ (UY f X' U).ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f))
    (h₄ : q.1 ≫ (UY f X' U).ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) =
      u.1 ≫ (UY f X' U).ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f))
    (h₅ : q.1 ≫ (UY f X' U).ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f) = v.1 ≫ (mY f W m X' U hUW
      hU₂).1) :
    p.1 ≫ (mY f W m X' U hUW hU₂).1 = q.1 ≫ (mY f W m X' U hUW hU₂).1 :=
  assoc_of_FF_eq_GG (X'.ι ≫ f) (UY f X' U) (mY f W m X' U hUW hU₂)
    (FF_eq_GG K LXK f e W m hmK X' U hUW hU₂) t u v p q h₁ h₂ h₃ h₄ h₅

end Assoc

end PartialMultiplication

end

end AbelianVarieties.NOSProofs.AssociativityRestriction

namespace NeronModelInfra

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian
open AbelianVarieties.NOSProofs.AssociativityRestriction

theorem
  exists_forall_dense_preimage_fibre_comp_eq_comp_of_forall_dense_preimage_fibre_of_relativeGroupLaw
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Smooth f] [IsSeparated f] [QuasiCompact f]
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsIso e.1]
    (W : (pullback f f).Opens) (m : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f)
    (hmK : (NeronModelInfra.schemeHomOverComp
        (genericFibreRestrict R K f (W.ι ≫ pullback.fst f f ≫ f) m) e).1 =
      pullback.map (W.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
          (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) W.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
        (LXK.mul (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩) e)
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (pullback.fst f f ≫ f)
              ⟨pullback.snd f f, pullback.condition.symm⟩) e)).1)
    (hΦ : IsOpenImmersion
      (pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
        ((Category.assoc _ _ _).trans m.2.symm)))
    (hΨ : IsOpenImmersion
      (pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
        (m.2.trans (by rw [Category.assoc, pullback.condition]))))
    (X' : X.Opens) (U : (pullback f f).Opens) (hUW : U ≤ W)
    (hU₁ : ∀ q : ↑(pullback f f), (pullback.fst f f ≫ f).base q ≠ IsLocalRing.closedPoint R → q ∈ U)
    (hU₂ : ∀ (q : ↑(pullback f f)) (hq : q ∈ U), (pullback.fst f f).base q ∈ X' ∧ (pullback.snd f
      f).base q ∈ X' ∧
      m.1.base ⟨q, hUW hq⟩ ∈ X')
    (hU₃ : ∀ x : X, x ∈ X' →
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = x} → ↑(pullback f
          f)) ⁻¹'
            (U : Set ↑(pullback f f))) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.snd f f).base q = x} → ↑(pullback f
          f)) ⁻¹'
            (U : Set ↑(pullback f f))) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = x} → ↑(pullback f
          f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base '' {w | W.ι.base w ∈ U})) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.snd f f).base q = x} → ↑(pullback f
          f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base '' {w | W.ι.base w ∈ U})) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = x} → ↑(pullback f
          f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base '' {w | W.ι.base w ∈ U}))
              ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.snd f f).base q = x} → ↑(pullback f
          f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base '' {w | W.ι.base w ∈
              U}))) :
    ∃ (UY : (pullback (X'.ι ≫ f) (X'.ι ≫ f)).Opens)
      (mY : SchemeHomOver (UY.ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) ≫ (X'.ι ≫ f)) (X'.ι ≫ f)),
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f)) // (pullback.fst (X'.ι ≫ f)
        (X'.ι ≫ f)).base q = x} → ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f))) ⁻¹'
          (UY : Set ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f))))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f)) // (pullback.snd (X'.ι ≫ f)
        (X'.ι ≫ f)).base q = x} → ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f))) ⁻¹'
          (UY : Set ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f))))) ∧
      IsOpenImmersion
          (pullback.lift (f := (X'.ι ≫ f)) (g := (X'.ι ≫ f)) (UY.ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫
            f)) mY.1
            ((Category.assoc _ _ _).trans mY.2.symm)) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f)) // (pullback.fst (X'.ι ≫ f)
        (X'.ι ≫ f)).base q = x} → ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f))) ⁻¹'
          (Set.range (pullback.lift (f := (X'.ι ≫ f)) (g := (X'.ι ≫ f)) (UY.ι ≫ pullback.fst (X'.ι ≫
            f) (X'.ι ≫ f)) mY.1
            ((Category.assoc _ _ _).trans mY.2.symm)).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f)) // (pullback.snd (X'.ι ≫ f)
        (X'.ι ≫ f)).base q = x} → ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f))) ⁻¹'
          (Set.range (pullback.lift (f := (X'.ι ≫ f)) (g := (X'.ι ≫ f)) (UY.ι ≫ pullback.fst (X'.ι ≫
            f) (X'.ι ≫ f)) mY.1
            ((Category.assoc _ _ _).trans mY.2.symm)).base))) ∧
      IsOpenImmersion
          (pullback.lift (f := (X'.ι ≫ f)) (g := (X'.ι ≫ f)) mY.1 (UY.ι ≫ pullback.snd (X'.ι ≫ f)
            (X'.ι ≫ f))
            (mY.2.trans (by rw [Category.assoc, pullback.condition]))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f)) // (pullback.fst (X'.ι ≫ f)
        (X'.ι ≫ f)).base q = x} → ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f))) ⁻¹'
          (Set.range (pullback.lift (f := (X'.ι ≫ f)) (g := (X'.ι ≫ f)) mY.1 (UY.ι ≫ pullback.snd
            (X'.ι ≫ f) (X'.ι ≫ f))
            (mY.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f)) // (pullback.snd (X'.ι ≫ f)
        (X'.ι ≫ f)).base q = x} → ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f))) ⁻¹'
          (Set.range (pullback.lift (f := (X'.ι ≫ f)) (g := (X'.ι ≫ f)) mY.1 (UY.ι ≫ pullback.snd
            (X'.ι ≫ f) (X'.ι ≫ f))
            (mY.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
          (u v p q : SchemeHomOver t (UY.ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) ≫ (X'.ι ≫ f))),
        u.1 ≫ UY.ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f) = v.1 ≫ UY.ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι
          ≫ f) →
        p.1 ≫ UY.ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) = u.1 ≫ mY.1 →
        p.1 ≫ UY.ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f) = v.1 ≫ UY.ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι
          ≫ f) →
        q.1 ≫ UY.ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) = u.1 ≫ UY.ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι
          ≫ f) →
        q.1 ≫ UY.ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f) = v.1 ≫ mY.1 →
        p.1 ≫ mY.1 = q.1 ≫ mY.1) ∧
      (∀ q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f)),
        (pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) ≫ (X'.ι ≫ f)).base q ≠ IsLocalRing.closedPoint R → q ∈
          UY) ∧
      (∀ {T : Scheme.{u}} (w : T ⟶ (U : Scheme.{u})) (a b : T ⟶ (X' : Scheme.{u})),
        a ≫ X'.ι = w ≫ U.ι ≫ pullback.fst f f → b ≫ X'.ι = w ≫ U.ι ≫ pullback.snd f f →
        ∃ v : T ⟶ (UY : Scheme.{u}),
          v ≫ UY.ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) = a ∧ v ≫ UY.ι ≫ pullback.snd (X'.ι ≫ f)
            (X'.ι ≫ f) = b ∧
          v ≫ mY.1 ≫ X'.ι = w ≫ (pullback f f).homOfLE hUW ≫ m.1) := by
  refine ⟨PartialMultiplication.UY f X' U, PartialMultiplication.mY f W m X' U hUW hU₂, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · exact fun x => PartialMultiplication.dense_UY_fst f W m X' U hUW hU₂ hU₃ x
  · exact fun x => PartialMultiplication.dense_UY_snd f W m X' U hUW hU₂ hU₃ x
  · exact PartialMultiplication.isOpenImmersion_PhiY f W m X' U hUW hU₂ hΦ
  · exact fun x => PartialMultiplication.dense_PhiY_fst f W m X' U hUW hU₂ hU₃ x
  · exact fun x => PartialMultiplication.dense_PhiY_snd f W m X' U hUW hU₂ hU₃ x
  · exact PartialMultiplication.isOpenImmersion_PsiY f W m X' U hUW hU₂ hΨ
  · exact fun x => PartialMultiplication.dense_PsiY_fst f W m X' U hUW hU₂ hU₃ x
  · exact fun x => PartialMultiplication.dense_PsiY_snd f W m X' U hUW hU₂ hU₃ x
  · intro T t u v p q h₁ h₂ h₃ h₄ h₅
    exact PartialMultiplication.hassocY K LXK f e W m hmK X' U hUW hU₂ t u v p q h₁ h₂ h₃ h₄ h₅
  · exact fun q hq => PartialMultiplication.mem_UY_of_ne_closedPoint f X' U hU₁ q hq
  · intro T w a b ha hb
    exact PartialMultiplication.restrict_clause f W m X' U hUW hU₂ w a b ha hb

end NeronModelInfra
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_lift_forall_dense_preimage_fibre_of_isPullback_of_forall_dense_preimage_fibre.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.DensityBaseChange


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace FibreDensity

theorem dense_fibre_iff {P Y : Scheme.{u}} (f : P ⟶ Y) (x : Y) (S : Set P) :
    Dense ((Subtype.val : {p : P // f p = x} → P) ⁻¹' S) ↔ Dense ((f.fiberι x) ⁻¹' S) := by
  have hpre : (f.fiberι x) ⁻¹' S = (f.fiberHomeo x) ⁻¹' ((Subtype.val : {p : P // f p = x} → P) ⁻¹'
    S) := by
    ext z
    rfl
  constructor
  · intro hS
    rw [hpre]
    exact hS.preimage (f.fiberHomeo x).isOpenMap
  · intro hS
    rw [hpre] at hS
    have := hS.preimage (f.fiberHomeo x).symm.isOpenMap
    rwa [← Set.preimage_comp, show ((f.fiberHomeo x) ∘ (f.fiberHomeo x).symm) = id from
      funext fun z => (f.fiberHomeo x).apply_symm_apply z, Set.preimage_id] at this

theorem dense_preimage_of_isPullback {P Y W T : Scheme.{u}} (f : P ⟶ Y) (x : Y)
    (k : T ⟶ Spec (Y.residueField x)) (g : T ⟶ Y) (hgk : g = k ≫ Y.fromSpecResidueField x)
    {lam : W ⟶ P} {q : W ⟶ T} (sq : IsPullback q lam g f)
    (S : Set P) (hS : Dense ((Subtype.val : {p : P // f p = x} → P) ⁻¹' S)) :
    Dense (lam ⁻¹' S) := by
  subst hgk
  have hF : IsPullback (f.fiberι x) (f.fiberToSpecResidueField x) f (Y.fromSpecResidueField x) :=
    IsPullback.of_hasPullback f (Y.fromSpecResidueField x)
  let e : W ⟶ f.fiber x := hF.lift lam (q ≫ k) (by rw [Category.assoc, ← sq.w])
  have he₁ : e ≫ f.fiberι x = lam := hF.lift_fst _ _ _
  have he₂ : e ≫ f.fiberToSpecResidueField x = q ≫ k := hF.lift_snd _ _ _
  have sq' : IsPullback e q (f.fiberToSpecResidueField x) k := by
    refine IsPullback.of_right (h₁₂ := f.fiberι x) (v₁₃ := f) (h₂₂ := Y.fromSpecResidueField x) ?_
      he₂ hF
    rw [he₁]
    exact sq.flip
  have : UniversallyOpen e :=
    MorphismProperty.of_isPullback (P := @UniversallyOpen) sq'.flip inferInstance
  have h1 : Dense ((f.fiberι x) ⁻¹' S) := (dense_fibre_iff f x S).mp hS
  have h2 : lam ⁻¹' S = e ⁻¹' ((f.fiberι x) ⁻¹' S) := by
    rw [← he₁, ← Set.preimage_comp]
    rfl
  rw [h2]
  exact h1.preimage e.isOpenMap

theorem dense_fibre_of_isPullback {X X' Z Z' : Scheme.{u}} (f : X ⟶ Z) (f' : X' ⟶ Z') (c : X' ⟶ X)
    (p : Z' ⟶ Z)
    (h : IsPullback c f' f p) (x' : Z') (S : Set X)
    (hS : Dense ((Subtype.val : {q : X // f q = p x'} → X) ⁻¹' S)) :
    Dense ((Subtype.val : {q : X' // f' q = x'} → X') ⁻¹' (c ⁻¹' S)) := by
  have sq := (IsPullback.of_hasPullback f' (Z'.fromSpecResidueField x')).paste_horiz h
  have hd := dense_preimage_of_isPullback f (p x') (Spec.map (p.residueFieldMap x'))
    (Z'.fromSpecResidueField x' ≫ p) (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField p
      x').symm sq.flip S hS
  rw [dense_fibre_iff]
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp] at hd
  exact hd

theorem range_eq_of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y
    ⟶ Z}
    (h : IsPullback fst snd f g) : Set.range fst = f ⁻¹' Set.range g := by
  rw [← Scheme.Pullback.range_fst, ← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp]
  have hs : Function.Surjective h.isoPullback.hom := (Scheme.homeoOfIso h.isoPullback).surjective
  rw [Set.range_eq_univ.mpr hs, Set.image_univ]

end FibreDensity

end AbelianVarieties.NOSProofs.DensityBaseChange

namespace NeronModelInfra

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian
open AbelianVarieties.NOSProofs.DensityBaseChange

theorem exists_lift_forall_dense_preimage_fibre_of_isPullback_of_forall_dense_preimage_fibre
    {R : Type u} [CommRing R] {R' : Type u} [CommRing R']
    (g : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
    (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
    (hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y
        y)) ⁻¹'
          (U : Set ↑(pullback y y))))
    (hU₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y
        y)) ⁻¹'
          (U : Set ↑(pullback y y))))
    (hΦ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)))
    (hΦ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y
        y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base)))
    (hΦ₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y
        y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base)))
    (hΨ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))))
    (hΨ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y
        y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base)))
    (hΨ₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y
        y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base)))
    (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
      p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫
        pullback.snd y y →
      q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y =
        v.1 ≫ m.1 →
      p.1 ≫ m.1 = q.1 ≫ m.1)
    {Y' : Scheme.{u}} (y' : Y' ⟶ Spec (CommRingCat.of R')) (p : Y' ⟶ Y) (hp : IsPullback p y' y g)
    (c : pullback y' y' ⟶ pullback y y)
    (hc₁ : c ≫ pullback.fst y y = pullback.fst y' y' ≫ p) (hc₂ : c ≫ pullback.snd y y = pullback.snd
      y' y' ≫ p) :
    ∃ m' : SchemeHomOver ((c ⁻¹ᵁ U).ι ≫ pullback.fst y' y' ≫ y') y',
      m'.1 ≫ p = c.resLE U (c ⁻¹ᵁ U) le_rfl ≫ m.1 ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          ((c ⁻¹ᵁ U) : Set ↑(pullback y' y')))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          ((c ⁻¹ᵁ U) : Set ↑(pullback y' y')))) ∧
      IsOpenImmersion
          (pullback.lift (f := y') (g := y') ((c ⁻¹ᵁ U).ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') ((c ⁻¹ᵁ U).ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') ((c ⁻¹ᵁ U).ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)).base))) ∧
      IsOpenImmersion
          (pullback.lift (f := y') (g := y') m'.1 ((c ⁻¹ᵁ U).ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') m'.1 ((c ⁻¹ᵁ U).ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} →
        ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') m'.1 ((c ⁻¹ᵁ U).ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R'))
          (u v p q : SchemeHomOver t ((c ⁻¹ᵁ U).ι ≫ pullback.fst y' y' ≫ y')),
        u.1 ≫ (c ⁻¹ᵁ U).ι ≫ pullback.snd y' y' = v.1 ≫ (c ⁻¹ᵁ U).ι ≫ pullback.fst y' y' →
        p.1 ≫ (c ⁻¹ᵁ U).ι ≫ pullback.fst y' y' = u.1 ≫ m'.1 →
        p.1 ≫ (c ⁻¹ᵁ U).ι ≫ pullback.snd y' y' = v.1 ≫ (c ⁻¹ᵁ U).ι ≫ pullback.snd y' y' →
        q.1 ≫ (c ⁻¹ᵁ U).ι ≫ pullback.fst y' y' = u.1 ≫ (c ⁻¹ᵁ U).ι ≫ pullback.fst y' y' →
        q.1 ≫ (c ⁻¹ᵁ U).ι ≫ pullback.snd y' y' = v.1 ≫ m'.1 →
        p.1 ≫ m'.1 = q.1 ≫ m'.1) := by
  have hcU : c.resLE U (c ⁻¹ᵁ U) le_rfl ≫ U.ι = (c ⁻¹ᵁ U).ι ≫ c := Scheme.Hom.resLE_comp_ι _ _
  have hA : c.resLE U (c ⁻¹ᵁ U) le_rfl ≫ U.ι ≫ pullback.fst y y = (c ⁻¹ᵁ U).ι ≫ pullback.fst y' y' ≫
    p := by
    rw [← Category.assoc, hcU, Category.assoc, hc₁]
  have hB : c.resLE U (c ⁻¹ᵁ U) le_rfl ≫ U.ι ≫ pullback.snd y y = (c ⁻¹ᵁ U).ι ≫ pullback.snd y' y' ≫
    p := by
    rw [← Category.assoc, hcU, Category.assoc, hc₂]
  have hw : (c.resLE U (c ⁻¹ᵁ U) le_rfl ≫ m.1) ≫ y = ((c ⁻¹ᵁ U).ι ≫ pullback.fst y' y' ≫ y') ≫ g :=
    by
    rw [Category.assoc, m.2, reassoc_of% hA]
    simp only [Category.assoc, hp.w]
  have hm'p : hp.lift _ _ hw ≫ p = c.resLE U (c ⁻¹ᵁ U) le_rfl ≫ m.1 := hp.lift_fst _ _ _
  have hm'y : hp.lift _ _ hw ≫ y' = (c ⁻¹ᵁ U).ι ≫ pullback.fst y' y' ≫ y' := hp.lift_snd _ _ _
  let m' : SchemeHomOver ((c ⁻¹ᵁ U).ι ≫ pullback.fst y' y' ≫ y') y' := ⟨hp.lift _ _ hw, hm'y⟩
  have sq₁ : IsPullback c (pullback.fst y' y') (pullback.fst y y) p := by
    have outer := (IsPullback.of_hasPullback y' y').flip.paste_horiz hp
    rw [← hc₂, ← hp.w] at outer
    exact outer.of_right hc₁ (IsPullback.of_hasPullback y y).flip
  have sq₂ : IsPullback c (pullback.snd y' y') (pullback.snd y y) p := by
    have outer := (IsPullback.of_hasPullback y' y').paste_horiz hp
    rw [← hc₁, ← hp.w] at outer
    exact outer.of_right hc₂ (IsPullback.of_hasPullback y y)
  have presq : IsPullback (c ⁻¹ᵁ U).ι (c.resLE U (c ⁻¹ᵁ U) le_rfl) c U.ι := by
    have := (isPullback_morphismRestrict c U).flip
    rwa [← Scheme.Hom.resLE_eq_morphismRestrict] at this
  have sqΦ : IsPullback
      (pullback.lift (f := y') (g := y') ((c ⁻¹ᵁ U).ι ≫ pullback.fst y' y') m'.1
        ((Category.assoc _ _ _).trans m'.2.symm))
      (c.resLE U (c ⁻¹ᵁ U) le_rfl) c
      (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1 ((Category.assoc _ _ _).trans
        m.2.symm)) := by
    have outer := presq.paste_horiz sq₁.flip
    refine IsPullback.of_right (h₁₂ := pullback.fst y' y') (v₁₃ := p) (h₂₂ := pullback.fst y y) ?_
      ?_ sq₁.flip
    · simpa only [pullback.lift_fst] using outer
    · apply pullback.hom_ext
      · simp only [Category.assoc, hc₁, pullback.lift_fst, pullback.lift_fst_assoc]
        exact hA.symm
      · simp only [Category.assoc, hc₂, pullback.lift_snd, pullback.lift_snd_assoc]
        exact hm'p
  have sqΨ : IsPullback
      (pullback.lift (f := y') (g := y') m'.1 ((c ⁻¹ᵁ U).ι ≫ pullback.snd y' y')
        (m'.2.trans (by rw [Category.assoc, pullback.condition])))
      (c.resLE U (c ⁻¹ᵁ U) le_rfl) c
      (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
        (m.2.trans (by rw [Category.assoc, pullback.condition]))) := by
    have outer := presq.paste_horiz sq₂.flip
    refine IsPullback.of_right (h₁₂ := pullback.snd y' y') (v₁₃ := p) (h₂₂ := pullback.snd y y) ?_
      ?_ sq₂.flip
    · simpa only [pullback.lift_snd] using outer
    · apply pullback.hom_ext
      · simp only [Category.assoc, hc₁, pullback.lift_fst, pullback.lift_fst_assoc]
        exact hm'p
      · simp only [Category.assoc, hc₂, pullback.lift_snd, pullback.lift_snd_assoc]
        exact hB.symm
  refine ⟨m', hm'p, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x'
    exact FibreDensity.dense_fibre_of_isPullback _ _ c p sq₁ x' _ (hU₁ (p.base x'))
  · intro x'
    exact FibreDensity.dense_fibre_of_isPullback _ _ c p sq₂ x' _ (hU₂ (p.base x'))
  · exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) sqΦ.flip hΦ
  · intro x'
    have h := FibreDensity.dense_fibre_of_isPullback _ _ c p sq₁ x' _ (hΦ₁ (p.base x'))
    rwa [← FibreDensity.range_eq_of_isPullback sqΦ] at h
  · intro x'
    have h := FibreDensity.dense_fibre_of_isPullback _ _ c p sq₂ x' _ (hΦ₂ (p.base x'))
    rwa [← FibreDensity.range_eq_of_isPullback sqΦ] at h
  · exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) sqΨ.flip hΨ
  · intro x'
    have h := FibreDensity.dense_fibre_of_isPullback _ _ c p sq₁ x' _ (hΨ₁ (p.base x'))
    rwa [← FibreDensity.range_eq_of_isPullback sqΨ] at h
  · intro x'
    have h := FibreDensity.dense_fibre_of_isPullback _ _ c p sq₂ x' _ (hΨ₂ (p.base x'))
    rwa [← FibreDensity.range_eq_of_isPullback sqΨ] at h
  · intro T t₀ u v pp qq h1 h2 h3 h4 h5
    have hbar : ∀ w : SchemeHomOver t₀ ((c ⁻¹ᵁ U).ι ≫ pullback.fst y' y' ≫ y'),
        (w.1 ≫ c.resLE U (c ⁻¹ᵁ U) le_rfl) ≫ U.ι ≫ pullback.fst y y ≫ y = t₀ ≫ g := fun w => by
      simp only [Category.assoc]
      rw [reassoc_of% hA, hp.w]
      have h2 := w.2
      rw [← Category.assoc, ← Category.assoc, ← Category.assoc]
      rw [← Category.assoc, ← Category.assoc] at h2
      rw [h2]
    let bar : SchemeHomOver t₀ ((c ⁻¹ᵁ U).ι ≫ pullback.fst y' y' ≫ y') → SchemeHomOver (t₀ ≫ g) (U.ι
      ≫ pullback.fst y y ≫ y) :=
      fun w => ⟨w.1 ≫ c.resLE U (c ⁻¹ᵁ U) le_rfl, hbar w⟩
    have post : ∀ {a b : T ⟶ Y'}, a = b → a ≫ p = b ≫ p := fun h => by rw [h]
    have H1 : (bar u).1 ≫ U.ι ≫ pullback.snd y y = (bar v).1 ≫ U.ι ≫ pullback.fst y y := by
      have e := post h1
      simp only [Category.assoc] at e
      change (u.1 ≫ _) ≫ _ = (v.1 ≫ _) ≫ _
      simp only [Category.assoc]; rw [hB, hA]; exact e
    have H2 : (bar pp).1 ≫ U.ι ≫ pullback.fst y y = (bar u).1 ≫ m.1 := by
      have e := post h2
      simp only [Category.assoc] at e
      change (pp.1 ≫ _) ≫ _ = (u.1 ≫ _) ≫ _
      simp only [Category.assoc]; rw [hA, ← hm'p]; exact e
    have H3 : (bar pp).1 ≫ U.ι ≫ pullback.snd y y = (bar v).1 ≫ U.ι ≫ pullback.snd y y := by
      have e := post h3
      simp only [Category.assoc] at e
      change (pp.1 ≫ _) ≫ _ = (v.1 ≫ _) ≫ _
      simp only [Category.assoc]; rw [hB]; exact e
    have H4 : (bar qq).1 ≫ U.ι ≫ pullback.fst y y = (bar u).1 ≫ U.ι ≫ pullback.fst y y := by
      have e := post h4
      simp only [Category.assoc] at e
      change (qq.1 ≫ _) ≫ _ = (u.1 ≫ _) ≫ _
      simp only [Category.assoc]; rw [hA]; exact e
    have H5 : (bar qq).1 ≫ U.ι ≫ pullback.snd y y = (bar v).1 ≫ m.1 := by
      have e := post h5
      simp only [Category.assoc] at e
      change (qq.1 ≫ _) ≫ _ = (v.1 ≫ _) ≫ _
      simp only [Category.assoc]; rw [hB, ← hm'p]; exact e
    have key := hassoc (t₀ ≫ g) (bar u) (bar v) (bar pp) (bar qq) H1 H2 H3 H4 H5
    apply hp.hom_ext
    · change pp.1 ≫ hp.lift _ _ hw ≫ p = qq.1 ≫ hp.lift _ _ hw ≫ p
      rw [hm'p]
      exact key
    · change pp.1 ≫ hp.lift _ _ hw ≫ y' = qq.1 ≫ hp.lift _ _ hw ≫ y'
      rw [hm'y, pp.2, qq.2]

end NeronModelInfra
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_eq_of_comp_eq_of_range_subset_closure_range_lift_of_forall_dense_preimage_fibre.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.GraphClosureRigidity


noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
    TopologicalSpace Topology

universe u

namespace GraphClosure

section Topology

theorem dense_of_forall_dense_fibre {X Y : Type*} [TopologicalSpace X] (p : X → Y) (S : Set X)
    (h : ∀ y : Y, Dense ((Subtype.val : {x : X // p x = y} → X) ⁻¹' S)) : Dense S := by
  intro x
  have hx : (⟨x, rfl⟩ : {x' : X // p x' = p x}) ∈ closure ((Subtype.val : {x' : X // p x' = p x} →
    X) ⁻¹' S) :=
    h (p x) ⟨x, rfl⟩
  rw [closure_subtype] at hx
  exact closure_mono (Set.image_preimage_subset _ _) hx

end Topology

section Family

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
variable (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)

/-- The triple fibre product containing the multiplication graph. -/
abbrev Y3 : Scheme.{u} := pullback (pullback.fst y y ≫ y) y

/-- The graph of the partial multiplication inside the triple fibre product. -/
abbrev gr : (U : Scheme.{u}) ⟶ Y3 y := pullback.lift (f := pullback.fst y y ≫ y) (g := y) U.ι m.1
    m.2.symm

/-- The projection onto the first two coordinates. -/
abbrev P12 : Y3 y ⟶ pullback y y := pullback.fst (pullback.fst y y ≫ y) y

/-- The structure map of the triple fibre product. -/
abbrev t3 : Y3 y ⟶ Spec (CommRingCat.of R) := pullback.snd (pullback.fst y y ≫ y) y ≫ y

/-- The topological closure of the partial multiplication graph. -/
def Zc : Closeds ↑(Y3 y) := ⟨closure (Set.range (gr y U m).base), isClosed_closure⟩

/-- The reduced closed subscheme supported on the multiplication-graph closure. -/
abbrev Gc : Scheme.{u} := (Scheme.IdealSheafData.vanishingIdeal (Zc y U m)).subscheme

/-- The inclusion of the reduced multiplication-graph closure. -/
abbrev γc : Gc y U m ⟶ Y3 y := (Scheme.IdealSheafData.vanishingIdeal (Zc y U m)).subschemeι

theorem range_γc : Set.range (γc y U m).base = closure (Set.range (gr y U m).base) := by
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

scoped instance isReduced_Gc : IsReduced (Gc y U m) :=
  (AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal_and_le_ker (Zc y U
    m)).1

theorem exists_comp_γc_eq {T : Scheme.{u}} [IsReduced T] (g : T ⟶ Y3 y)
    (hg : Set.range g.base ⊆ closure (Set.range (gr y U m).base)) :
    ∃ g₁ : T ⟶ Gc y U m, g₁ ≫ γc y U m = g := by
  have hker : (γc y U m).ker ≤ g.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact (AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal_and_le_ker
      (Zc y U m)).2 g hg
  exact ⟨IsClosedImmersion.lift (γc y U m) g hker, IsClosedImmersion.lift_fac _ _ _⟩

variable {y U m} in
theorem denseRange_g0 (g₀ : (U : Scheme.{u}) ⟶ Gc y U m) (hg₀ : g₀ ≫ γc y U m = gr y U m) :
    DenseRange g₀.base := by
  have hemb : IsInducing (γc y U m).base := (γc y U m).isClosedEmbedding.isInducing
  rw [DenseRange, Dense]
  intro p
  rw [hemb.closure_eq_preimage_closure_image, Set.mem_preimage, ← Set.range_comp]
  have : (⇑(γc y U m).base ∘ ⇑g₀.base) = ⇑(g₀ ≫ γc y U m).base := by
    ext u; rw [Scheme.Hom.comp_apply]; rfl
  rw [this, hg₀, ← range_γc]
  exact ⟨p, rfl⟩

/-- The graph closure with one additional coordinate over the base. -/
abbrev GY : Scheme.{u} := pullback (γc y U m ≫ t3 y) y

/-- The first pair of coordinates on the enlarged graph closure. -/
def cxy : GY y U m ⟶ pullback y y := pullback.fst (γc y U m ≫ t3 y) y ≫ γc y U m ≫ P12 y
/-- The first coordinate on the enlarged graph closure. -/
def cx : GY y U m ⟶ Y := cxy y U m ≫ pullback.fst y y
/-- The second coordinate on the enlarged graph closure. -/
def cy : GY y U m ⟶ Y := cxy y U m ≫ pullback.snd y y
/-- The product coordinate on the enlarged graph closure. -/
def cz : GY y U m ⟶ Y := pullback.fst (γc y U m ≫ t3 y) y ≫ γc y U m ≫ pullback.snd _ _
/-- The additional coordinate on the enlarged graph closure. -/
abbrev cw : GY y U m ⟶ Y := pullback.snd (γc y U m ≫ t3 y) y

theorem cz_y : cz y U m ≫ y = cw y U m ≫ y := by
  rw [cz]
  simp only [Category.assoc]
  exact pullback.condition

theorem P12_fst_y : P12 y ≫ pullback.fst y y ≫ y = t3 y := pullback.condition

theorem P12_snd_y : P12 y ≫ pullback.snd y y ≫ y = t3 y := by
  rw [← pullback.condition (f := y) (g := y)]
  exact pullback.condition

theorem cy_y : cy y U m ≫ y = cw y U m ≫ y := by
  rw [cy, cxy]
  simp only [Category.assoc]
  rw [P12_snd_y]
  exact pullback.condition

theorem cx_y : cx y U m ≫ y = cw y U m ≫ y := by
  rw [cx, cxy]
  simp only [Category.assoc]
  rw [P12_fst_y]
  exact pullback.condition

/-- The pair formed by the product coordinate and the additional coordinate. -/
abbrev zw : GY y U m ⟶ pullback y y := pullback.lift (cz y U m) (cw y U m) (cz_y y U m)

/-- The pair formed by the second coordinate and the additional coordinate. -/
abbrev yw : GY y U m ⟶ pullback y y := pullback.lift (cy y U m) (cw y U m) (cy_y y U m)

/-- The open locus where the product and additional coordinate can be multiplied. -/
def L1 : (GY y U m).Opens := zw y U m ⁻¹ᵁ U
/-- The open locus where the second and additional coordinate can be multiplied. -/
def L2 : (GY y U m).Opens := yw y U m ⁻¹ᵁ U

/-- The second-coordinate pair restricted to its multiplication domain. -/
def uyw : ((L2 y U m : (GY y U m).Opens) : Scheme.{u}) ⟶ (U : Scheme.{u}) :=
  IsOpenImmersion.lift U.ι ((L2 y U m).ι ≫ yw y U m) (by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact p.2)

@[reassoc]
theorem uyw_ι : uyw y U m ≫ U.ι = (L2 y U m).ι ≫ yw y U m := IsOpenImmersion.lift_fac _ _ _

/-- Multiply the second coordinate by the additional coordinate. -/
def myw : ((L2 y U m : (GY y U m).Opens) : Scheme.{u}) ⟶ Y := uyw y U m ≫ m.1

theorem cx_y' : ((L2 y U m).ι ≫ cx y U m) ≫ y = myw y U m ≫ y := by
  rw [myw, Category.assoc, Category.assoc, m.2, uyw_ι_assoc, pullback.lift_fst_assoc, cy_y, cx_y]

/-- Pair the first coordinate with the product of the last two coordinates. -/
abbrev xyw : ((L2 y U m : (GY y U m).Opens) : Scheme.{u}) ⟶ pullback y y :=
  pullback.lift ((L2 y U m).ι ≫ cx y U m) (myw y U m) (cx_y' y U m)

/-- The locus where the first coordinate can multiply the product of the last two. -/
def L3 : (GY y U m).Opens := (L2 y U m).ι ''ᵁ (xyw y U m ⁻¹ᵁ U)
/-- The common open domain of the two associated triple products. -/
def Om : (GY y U m).Opens := L1 y U m ⊓ L3 y U m

theorem Om_le_L1 : Om y U m ≤ L1 y U m := inf_le_left
theorem L3_le_L2 : L3 y U m ≤ L2 y U m := Scheme.Opens.ι_image_le _ _
theorem Om_le_L2 : Om y U m ≤ L2 y U m := inf_le_right.trans (L3_le_L2 y U m)

/-- Restrict the product-coordinate pair to the common domain. -/
def uzw : ((Om y U m : (GY y U m).Opens) : Scheme.{u}) ⟶ (U : Scheme.{u}) :=
  IsOpenImmersion.lift U.ι ((Om y U m).ι ≫ zw y U m) (by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact Om_le_L1 y U m p.2)

@[reassoc]
theorem uzw_ι : uzw y U m ≫ U.ι = (Om y U m).ι ≫ zw y U m := IsOpenImmersion.lift_fac _ _ _

/-- The first of the two iterated multiplication maps being compared. -/
def FF : ((Om y U m : (GY y U m).Opens) : Scheme.{u}) ⟶ Y := uzw y U m ≫ m.1

/-- Include the common associativity domain into the second-pair domain. -/
abbrev toL2 : ((Om y U m : (GY y U m).Opens) : Scheme.{u}) ⟶ ((L2 y U m : (GY y U m).Opens) :
    Scheme.{u}) :=
  (GY y U m).homOfLE (Om_le_L2 y U m)

theorem toL2_mem (p : ↥(Om y U m)) : (toL2 y U m).base p ∈ xyw y U m ⁻¹ᵁ U := by
  obtain ⟨q, hq, hqp⟩ := (show (Om y U m).ι.base p ∈ (L3 y U m : Set _) from p.2.2)
  have h1 : (L2 y U m).ι ((toL2 y U m) p) = (Om y U m).ι p :=
    Scheme.homOfLE_apply (Om_le_L2 y U m) p
  have : q = (toL2 y U m).base p := (L2 y U m).ι.isOpenEmbedding.injective (hqp.trans h1.symm)
  rw [← this]
  exact hq

/-- Map the common domain to the right-associated multiplication domain. -/
def uxyw : ((Om y U m : (GY y U m).Opens) : Scheme.{u}) ⟶ (U : Scheme.{u}) :=
  IsOpenImmersion.lift U.ι (toL2 y U m ≫ xyw y U m) (by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
    exact toL2_mem y U m p)

@[reassoc]
theorem uxyw_ι : uxyw y U m ≫ U.ι = toL2 y U m ≫ xyw y U m := IsOpenImmersion.lift_fac _ _ _

/-- The second of the two iterated multiplication maps being compared. -/
def GG : ((Om y U m : (GY y U m).Opens) : Scheme.{u}) ⟶ Y := uxyw y U m ≫ m.1

theorem FF_y' : FF y U m ≫ y = (Om y U m).ι ≫ cw y U m ≫ y := by
  rw [FF, Category.assoc, m.2, uzw_ι_assoc, pullback.lift_fst_assoc, cz_y]

theorem GG_y' : GG y U m ≫ y = (Om y U m).ι ≫ cw y U m ≫ y := by
  rw [GG, Category.assoc, m.2, uxyw_ι_assoc, pullback.lift_fst_assoc, Category.assoc, cx_y,
    Scheme.homOfLE_ι_assoc]

theorem FF_y : FF y U m ≫ y = GG y U m ≫ y := by rw [FF_y', GG_y']

/-- The multiplication domain pulled back to the chosen open subscheme product. -/
abbrev UY : Scheme.{u} := pullback (U.ι ≫ pullback.fst y y ≫ y) y

variable (g₀ : (U : Scheme.{u}) ⟶ Gc y U m) (hg₀ : g₀ ≫ γc y U m = gr y U m)

include hg₀ in
theorem g₀_t3 : (U.ι ≫ pullback.fst y y ≫ y) ≫ 𝟙 _ = g₀ ≫ γc y U m ≫ t3 y := by
  rw [Category.comp_id, ← Category.assoc g₀, hg₀, pullback.lift_snd_assoc]
  exact m.2.symm

/-- Map the original multiplication graph with one coordinate into its closure. -/
def kk : UY y U ⟶ GY y U m :=
  pullback.map (U.ι ≫ pullback.fst y y ≫ y) y (γc y U m ≫ t3 y) y g₀ (𝟙 Y) (𝟙 _) (g₀_t3 y U m g₀
    hg₀)
    (by rw [Category.comp_id, Category.id_comp])

@[reassoc]
theorem kk_fst : kk y U m g₀ hg₀ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ g₀ := pullback.lift_fst _ _
    _

@[reassoc]
theorem kk_cw : kk y U m g₀ hg₀ ≫ cw y U m = pullback.snd _ _ := by
  rw [kk, pullback.lift_snd, Category.comp_id]

include hg₀ in
@[reassoc]
theorem kk_cz : kk y U m g₀ hg₀ ≫ cz y U m = pullback.fst _ _ ≫ m.1 := by
  rw [cz, kk_fst_assoc, ← Category.assoc g₀, hg₀, pullback.lift_snd]

include hg₀ in
@[reassoc]
theorem kk_cxy : kk y U m g₀ hg₀ ≫ cxy y U m = pullback.fst _ _ ≫ U.ι := by
  rw [cxy, kk_fst_assoc, ← Category.assoc g₀, hg₀, pullback.lift_fst]

/-- Pair the original product with the additional coordinate. -/
abbrev mw : UY y U ⟶ pullback y y :=
  pullback.map (U.ι ≫ pullback.fst y y ≫ y) y y y m.1 (𝟙 Y) (𝟙 _) (by rw [Category.comp_id, m.2])
    (by rw [Category.comp_id, Category.id_comp])

theorem kk_zw : kk y U m g₀ hg₀ ≫ zw y U m = mw y U m := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, kk_cz, pullback.lift_fst]
  · rw [Category.assoc, pullback.lift_snd, kk_cw, pullback.lift_snd, Category.comp_id]

theorem UY_cond : (pullback.fst (U.ι ≫ pullback.fst y y ≫ y) y ≫ U.ι ≫ pullback.snd y y) ≫ y =
    pullback.snd (U.ι ≫ pullback.fst y y ≫ y) y ≫ y := by
  rw [Category.assoc, Category.assoc, ← pullback.condition (f := y) (g := y)]
  exact pullback.condition

@[reassoc]
theorem kk_cy : kk y U m g₀ hg₀ ≫ cy y U m = pullback.fst _ _ ≫ U.ι ≫ pullback.snd y y := by
  rw [cy, kk_cxy_assoc]

@[reassoc]
theorem kk_cx : kk y U m g₀ hg₀ ≫ cx y U m = pullback.fst _ _ ≫ U.ι ≫ pullback.fst y y := by
  rw [cx, kk_cxy_assoc]

theorem kk_yw : kk y U m g₀ hg₀ ≫ yw y U m =
    pullback.lift (pullback.fst _ _ ≫ U.ι ≫ pullback.snd y y) (pullback.snd _ _) (UY_cond y U) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, kk_cy]
  · rw [Category.assoc, pullback.lift_snd, kk_cw, pullback.lift_snd]

/-- The open locus where the original product can multiply the additional coordinate. -/
def E2 : (UY y U).Opens := mw y U m ⁻¹ᵁ U
/-- The common open domain used to test equality on the graph closure. -/
def EE : (UY y U).Opens := kk y U m g₀ hg₀ ⁻¹ᵁ Om y U m ⊓ E2 y U m

/-- The comparison map from the original graph domain to the closure domain. -/
def hh : ((EE y U m g₀ hg₀ : (UY y U).Opens) : Scheme.{u}) ⟶ ((Om y U m : (GY y U m).Opens) :
    Scheme.{u}) :=
  IsOpenImmersion.lift (Om y U m).ι ((EE y U m g₀ hg₀).ι ≫ kk y U m g₀ hg₀) (by
    rintro _ ⟨e, rfl⟩
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
    exact e.2.1)

@[reassoc]
theorem hh_ι : hh y U m g₀ hg₀ ≫ (Om y U m).ι = (EE y U m g₀ hg₀).ι ≫ kk y U m g₀ hg₀ :=
  IsOpenImmersion.lift_fac _ _ _

/-- The structure map of the comparison domain. -/
abbrev tE : ((EE y U m g₀ hg₀ : (UY y U).Opens) : Scheme.{u}) ⟶ Spec (CommRingCat.of R) :=
  (EE y U m g₀ hg₀).ι ≫ pullback.fst _ _ ≫ U.ι ≫ pullback.fst y y ≫ y

/-- The first pair in the associativity test over the comparison domain. -/
def uu : SchemeHomOver (tE y U m g₀ hg₀) (U.ι ≫ pullback.fst y y ≫ y) :=
  ⟨(EE y U m g₀ hg₀).ι ≫ pullback.fst _ _, by simp only [Category.assoc]⟩

theorem vv_aux : Set.range ((EE y U m g₀ hg₀).ι ≫ kk y U m g₀ hg₀ ≫ yw y U m).base ⊆ Set.range
    U.ι.base := by
  rintro _ ⟨e, rfl⟩
  rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  exact Om_le_L2 y U m e.2.1

/-- The second pair in the associativity test over the comparison domain. -/
def vv : SchemeHomOver (tE y U m g₀ hg₀) (U.ι ≫ pullback.fst y y ≫ y) :=
  ⟨IsOpenImmersion.lift U.ι ((EE y U m g₀ hg₀).ι ≫ kk y U m g₀ hg₀ ≫ yw y U m) (vv_aux y U m g₀
    hg₀), by
    rw [IsOpenImmersion.lift_fac_assoc, Category.assoc, Category.assoc, pullback.lift_fst_assoc,
      cy_y, kk_cw_assoc, ← pullback.condition]⟩

@[reassoc]
theorem vv_ι : (vv y U m g₀ hg₀).1 ≫ U.ι = (EE y U m g₀ hg₀).ι ≫ kk y U m g₀ hg₀ ≫ yw y U m :=
  IsOpenImmersion.lift_fac _ _ _

theorem pp_aux : Set.range ((EE y U m g₀ hg₀).ι ≫ mw y U m).base ⊆ Set.range U.ι.base := by
  rintro _ ⟨e, rfl⟩
  rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
  exact e.2.2

/-- The left-associated intermediate pair in the associativity test. -/
def pp : SchemeHomOver (tE y U m g₀ hg₀) (U.ι ≫ pullback.fst y y ≫ y) :=
  ⟨IsOpenImmersion.lift U.ι ((EE y U m g₀ hg₀).ι ≫ mw y U m) (pp_aux y U m g₀ hg₀), by
    rw [IsOpenImmersion.lift_fac_assoc, Category.assoc, pullback.lift_fst_assoc, Category.assoc,
      m.2]⟩

@[reassoc]
theorem pp_ι : (pp y U m g₀ hg₀).1 ≫ U.ι = (EE y U m g₀ hg₀).ι ≫ mw y U m :=
    IsOpenImmersion.lift_fac _ _ _

theorem qq_aux : Set.range ((hh y U m g₀ hg₀ ≫ toL2 y U m) ≫ xyw y U m).base ⊆ Set.range U.ι.base :=
    by
  rintro _ ⟨e, rfl⟩
  rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  exact toL2_mem y U m _

/-- The right-associated intermediate pair in the associativity test. -/
def qq : SchemeHomOver (tE y U m g₀ hg₀) (U.ι ≫ pullback.fst y y ≫ y) :=
  ⟨IsOpenImmersion.lift U.ι ((hh y U m g₀ hg₀ ≫ toL2 y U m) ≫ xyw y U m) (qq_aux y U m g₀ hg₀), by
    rw [IsOpenImmersion.lift_fac_assoc, Category.assoc, Category.assoc, pullback.lift_fst_assoc,
      Category.assoc, Scheme.homOfLE_ι_assoc, hh_ι_assoc, cx_y, kk_cw_assoc, ← pullback.condition]⟩

@[reassoc]
theorem qq_ι : (qq y U m g₀ hg₀).1 ≫ U.ι = hh y U m g₀ hg₀ ≫ toL2 y U m ≫ xyw y U m := by
  rw [qq, IsOpenImmersion.lift_fac, Category.assoc]

theorem hh_FF : hh y U m g₀ hg₀ ≫ FF y U m = (pp y U m g₀ hg₀).1 ≫ m.1 := by
  rw [FF, ← Category.assoc]
  congr 1
  rw [← cancel_mono U.ι, Category.assoc, uzw_ι, hh_ι_assoc, kk_zw, pp_ι]

theorem hh_GG : hh y U m g₀ hg₀ ≫ GG y U m = (qq y U m g₀ hg₀).1 ≫ m.1 := by
  rw [GG, ← Category.assoc]
  congr 1
  rw [← cancel_mono U.ι, Category.assoc, uxyw_ι, qq_ι]

variable (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
  u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
  p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.snd
    y y →
  q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫
    m.1 →
  p.1 ≫ m.1 = q.1 ≫ m.1)

include hassoc in
theorem hh_FF_eq_hh_GG : hh y U m g₀ hg₀ ≫ FF y U m = hh y U m g₀ hg₀ ≫ GG y U m := by
  rw [hh_FF, hh_GG]
  apply hassoc (tE y U m g₀ hg₀) (uu y U m g₀ hg₀) (vv y U m g₀ hg₀) (pp y U m g₀ hg₀) (qq y U m g₀
    hg₀)
  · rw [vv_ι_assoc, uu, pullback.lift_fst, kk_cy]
    rfl
  · rw [pp_ι_assoc, uu, pullback.lift_fst]
    rfl
  · rw [pp_ι_assoc, vv_ι_assoc, pullback.lift_snd, pullback.lift_snd, kk_cw, Category.comp_id]
  · rw [qq_ι_assoc, uu, pullback.lift_fst, Category.assoc, Scheme.homOfLE_ι_assoc, hh_ι_assoc,
      kk_cx]
  · rw [qq_ι_assoc, pullback.lift_snd, myw, ← Category.assoc, ← Category.assoc]
    congr 1
    rw [← cancel_mono U.ι, Category.assoc, Category.assoc, uyw_ι, Scheme.homOfLE_ι_assoc,
      hh_ι_assoc,
      vv_ι]

variable [IsDomain R] [IsNoetherianRing R] [Smooth y] [IsSeparated y]

scoped instance isReduced_GY : IsReduced (GY y U m) := by
  have : IsLocallyNoetherian (Gc y U m) := LocallyOfFiniteType.isLocallyNoetherian (γc y U m ≫ t3 y)
  exact AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian
    (pullback.fst (γc y U m ≫ t3 y) y)

omit [IsDomain R] [IsNoetherianRing R] [IsSeparated y] in
theorem denseRange_kk : DenseRange (kk y U m g₀ hg₀).base := by
  rw [DenseRange, kk, Scheme.Pullback.range_map]
  have h1 : Set.range (𝟙 Y : Y ⟶ Y).base = Set.univ := Set.range_eq_univ.mpr (fun x => ⟨x, rfl⟩)
  rw [h1, Set.preimage_univ, Set.inter_univ]
  exact (denseRange_g0 g₀ hg₀).preimage (pullback.fst (γc y U m ≫ t3 y) y).isOpenMap

omit [IsDomain R] [IsNoetherianRing R] [IsSeparated y] in
theorem universallyOpen_m (hΦ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1 ((Category.assoc _ _ _).trans
        m.2.symm))) :
    UniversallyOpen m.1 := by
  have h : m.1 = pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
      ((Category.assoc _ _ _).trans m.2.symm) ≫ pullback.snd y y := (pullback.lift_snd _ _ _).symm
  rw [h]
  infer_instance

omit [IsDomain R] [IsNoetherianRing R] [Smooth y] [IsSeparated y] in
theorem dense_E2 [UniversallyOpen m.1] (hU : Dense (U : Set ↑(pullback y y))) :
    Dense ((E2 y U m : (UY y U).Opens) : Set ↑(UY y U)) := by
  have : UniversallyOpen (mw y U m) :=
    MorphismProperty.pullbackMap (P := @UniversallyOpen) (i₁ := m.1) (i₂ := 𝟙 Y) inferInstance
      inferInstance m.2.symm (Category.id_comp _).symm
  exact hU.preimage (mw y U m).isOpenMap

omit [IsDomain R] [IsNoetherianRing R] [IsSeparated y] in
theorem denseRange_hh [UniversallyOpen m.1] (hU : Dense (U : Set ↑(pullback y y))) :
    DenseRange (hh y U m g₀ hg₀).base := by
  have hS : Dense ((kk y U m g₀ hg₀).base '' ((E2 y U m : (UY y U).Opens) : Set ↑(UY y U))) :=
    (denseRange_kk y U m g₀ hg₀).dense_image (kk y U m g₀ hg₀).base.hom.continuous (dense_E2 y U m
      hU)
  have hsub : (Om y U m).ι.base ⁻¹' ((kk y U m g₀ hg₀).base '' ((E2 y U m : (UY y U).Opens) : Set
    _)) ⊆
      Set.range (hh y U m g₀ hg₀).base := by
    rintro p ⟨e, he, hep⟩
    have heE : e ∈ EE y U m g₀ hg₀ := ⟨show (kk y U m g₀ hg₀).base e ∈ Om y U m by
      rw [hep]; exact p.2, he⟩
    refine ⟨⟨e, heE⟩, (Om y U m).ι.isOpenEmbedding.injective ?_⟩
    exact (congrArg
      (fun g : (EE y U m g₀ hg₀ : Scheme.{u}) ⟶ GY y U m => g.base ⟨e, heE⟩)
      (hh_ι y U m g₀ hg₀)).trans hep
  exact (hS.preimage (Om y U m).ι.isOpenMap).mono hsub

omit [IsDomain R] in
include hg₀ hassoc in
theorem FF_eq_GG [UniversallyOpen m.1] (hU : Dense (U : Set ↑(pullback y y))) : FF y U m = GG y U m
    := by
  have : IsDominant (hh y U m g₀ hg₀) := ⟨denseRange_hh y U m g₀ hg₀ hU⟩
  exact ext_of_isDominant_of_isSeparated y (FF_y y U m) (hh y U m g₀ hg₀) (hh_FF_eq_hh_GG y U m g₀
    hg₀ hassoc)

end Family

section Fibre

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
variable {K : Type u} [Field K] (k₀ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))

theorem eq_of_comp_eq_of_nonempty {W Z : Scheme.{u}} (h : W ⟶ Spec (CommRingCat.of K)) [Nonempty W]
    (c c' : Spec (CommRingCat.of K) ⟶ Z) (hcc : h ≫ c = h ≫ c') : c = c' := by
  obtain ⟨w⟩ := ‹Nonempty W›
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (W.fromSpecResidueField w ≫ h)
  have h1 : Spec.map φ ≫ c = Spec.map φ ≫ c' := by rw [hφ, Category.assoc, Category.assoc, hcc]
  have : Epi (Spec.map φ) := Flat.epi_of_flat_of_surjective (Spec.map φ)
  exact (cancel_epi (Spec.map φ)).mp h1

/-- The base change of the scheme to the chosen field-valued base point. -/
abbrev YK : Scheme.{u} := pullback k₀ y

variable (β : Spec (CommRingCat.of K) ⟶ Y) (hβ : β ≫ y = k₀)

/-- Pair a field-valued section with the variable coordinate. -/
abbrev rho : YK y k₀ ⟶ pullback y y :=
  pullback.lift (pullback.fst k₀ y ≫ β) (pullback.snd k₀ y) (by rw [Category.assoc, hβ,
    pullback.condition])

/-- The section of the field fibre induced by the chosen field-valued point. -/
abbrev secK : Spec (CommRingCat.of K) ⟶ YK y k₀ := pullback.lift (𝟙 _) β (by rw [Category.id_comp,
    hβ])

include hβ in
theorem nonempty_YK : Nonempty ↑(YK y k₀) := ⟨(secK y k₀ β hβ).base (IsLocalRing.closedPoint K)⟩

theorem dense_preimage_rho (O : (pullback y y).Opens)
    (hO : ∀ x : Y, Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} →
      ↑(pullback y y)) ⁻¹' (O : Set ↑(pullback y y)))) :
    Dense ((rho y k₀ β hβ ⁻¹ᵁ O : (YK y k₀).Opens) : Set ↑(YK y k₀)) := by
  set x : Y := β.base (IsLocalRing.closedPoint K) with hx
  let ιx := Y.fromSpecResidueField x
  let e : Spec (CommRingCat.of K) ⟶ Spec (Y.residueField x) :=
    Spec.map (Scheme.descResidueField (Scheme.stalkClosedPointTo β))
  have heβ : e ≫ ιx = β := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Y β
  let F := pullback (pullback.fst y y) ιx
  let G' := pullback (pullback.snd (pullback.fst y y) ιx) e
  let θ : YK y k₀ ≅ G' :=
    pullback.congrHom hβ.symm rfl ≪≫ (pullbackRightPullbackFstIso y y β).symm ≪≫ pullbackSymmetry _
      _ ≪≫
      pullback.congrHom rfl heβ.symm ≪≫ (pullbackLeftPullbackSndIso (pullback.fst y y) ιx e).symm
  have hθ : θ.hom ≫ pullback.fst _ _ ≫ pullback.fst _ _ = rho y k₀ β hβ := by
    apply pullback.hom_ext
    · simp only [θ, Iso.trans_hom, Iso.symm_hom, Category.assoc, pullback.lift_fst,
        pullbackLeftPullbackSndIso_inv_fst_assoc, pullback.congrHom_hom, pullback.lift_fst_assoc,
        Category.comp_id, pullbackSymmetry_hom_comp_fst_assoc,
          pullbackRightPullbackFstIso_inv_snd_fst]
    · simp only [θ, Iso.trans_hom, Iso.symm_hom, Category.assoc, pullback.lift_snd,
        pullbackLeftPullbackSndIso_inv_fst_assoc, pullback.congrHom_hom, pullback.lift_fst_assoc,
        Category.comp_id, pullbackSymmetry_hom_comp_fst_assoc,
          pullbackRightPullbackFstIso_inv_snd_snd]
  have hF : Dense ((pullback.fst (pullback.fst y y) ιx).base ⁻¹' (O : Set ↑(pullback y y))) := by
    have h1 : (pullback.fst (pullback.fst y y) ιx).base ⁻¹' (O : Set ↑(pullback y y)) =
        ((pullback.fst y y).fiberHomeo x) ⁻¹'
          ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y))
            ⁻¹'
            (O : Set ↑(pullback y y))) := by
      ext q
      simp only [Set.mem_preimage]
      rfl
    rw [h1]
    exact (hO x).preimage ((pullback.fst y y).fiberHomeo x).isOpenMap
  have hG' : Dense ((pullback.fst (pullback.snd (pullback.fst y y) ιx) e).base ⁻¹'
      ((pullback.fst (pullback.fst y y) ιx).base ⁻¹' (O : Set ↑(pullback y y)))) :=
    hF.preimage (pullback.fst (pullback.snd (pullback.fst y y) ιx) e).isOpenMap
  have h2 : ((rho y k₀ β hβ ⁻¹ᵁ O : (YK y k₀).Opens) : Set ↑(YK y k₀)) =
      θ.hom.base ⁻¹' ((pullback.fst (pullback.snd (pullback.fst y y) ιx) e).base ⁻¹'
        ((pullback.fst (pullback.fst y y) ιx).base ⁻¹' (O : Set ↑(pullback y y)))) := by
    rw [← hθ]
    rfl
  rw [h2]
  exact hG'.preimage (Scheme.homeoOfIso θ).isOpenMap

variable (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)

/-- The chart map recording the first input and its product. -/
abbrev Phi : (U : Scheme.{u}) ⟶ pullback y y :=
  pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1 ((Category.assoc _ _ _).trans
    m.2.symm)

/-- The chart map recording the product and the second input. -/
abbrev Psi : (U : Scheme.{u}) ⟶ pullback y y :=
  pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
    (m.2.trans (by rw [Category.assoc, pullback.condition]))

/-- The fibre of the first projection at a chosen field-valued point. -/
abbrev Sl : Scheme.{u} := pullback (pullback.fst y y) β
/-- The partial multiplication domain over a chosen first coordinate. -/
abbrev Ub : Scheme.{u} := pullback (U.ι ≫ pullback.fst y y) β

/-- The first-input and product chart map on the chosen fibre. -/
abbrev Phib : Ub y β U ⟶ Sl y β :=
  pullback.map (U.ι ≫ pullback.fst y y) β (pullback.fst y y) β (Phi y U m) (𝟙 _) (𝟙 Y)
    (by rw [Category.comp_id, pullback.lift_fst]) (by rw [Category.comp_id, Category.id_comp])

/-- The inclusion of the multiplication domain into the chosen fibre. -/
abbrev iotab : Ub y β U ⟶ Sl y β :=
  pullback.map (U.ι ≫ pullback.fst y y) β (pullback.fst y y) β U.ι (𝟙 _) (𝟙 Y)
    (by rw [Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])

/-- Identify the chosen projection fibre with the field fibre of the scheme. -/
def sig : Sl y β ≅ YK y k₀ :=
  pullbackSymmetry _ _ ≪≫ pullbackRightPullbackFstIso y y β ≪≫ pullback.congrHom hβ rfl

@[reassoc]
theorem sig_hom_fst : (sig y k₀ β hβ).hom ≫ pullback.fst k₀ y = pullback.snd _ _ := by
  rw [sig]
  simp only [Iso.trans_hom, Category.assoc]
  rw [pullback.congrHom_hom, pullback.lift_fst, Category.comp_id,
    pullbackRightPullbackFstIso_hom_fst,
    pullbackSymmetry_hom_comp_fst]

@[reassoc]
theorem sig_hom_snd : (sig y k₀ β hβ).hom ≫ pullback.snd k₀ y = pullback.fst _ _ ≫ pullback.snd y y
    := by
  rw [sig]
  simp only [Iso.trans_hom, Category.assoc]
  rw [pullback.congrHom_hom, pullback.lift_snd, Category.comp_id,
    pullbackRightPullbackFstIso_hom_snd,
    pullbackSymmetry_hom_comp_snd_assoc]

theorem sig_hom_rho : (sig y k₀ β hβ).hom ≫ rho y k₀ β hβ = pullback.fst _ _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, sig_hom_fst, pullback.condition]
  · rw [Category.assoc, pullback.lift_snd, sig_hom_snd]

include hβ in
theorem denseRange_iotab (hUβ : Dense ((rho y k₀ β hβ ⁻¹ᵁ U : (YK y k₀).Opens) : Set ↑(YK y k₀))) :
    DenseRange (iotab y β U).base := by
  rw [DenseRange, Scheme.Pullback.range_map]
  have h1 : Set.range (𝟙 (Spec (CommRingCat.of K)) : _ ⟶ _).base = Set.univ :=
    Set.range_eq_univ.mpr (fun t => ⟨t, rfl⟩)
  rw [h1, Set.preimage_univ, Set.inter_univ, Scheme.Opens.range_ι]
  have h2 : (pullback.fst (pullback.fst y y) β).base ⁻¹' (U : Set ↑(pullback y y)) =
      (sig y k₀ β hβ).hom.base ⁻¹' ((rho y k₀ β hβ ⁻¹ᵁ U : (YK y k₀).Opens) : Set ↑(YK y k₀)) := by
    rw [← sig_hom_rho y k₀ β hβ]
    rfl
  rw [h2]
  exact hUβ.preimage (Scheme.homeoOfIso (sig y k₀ β hβ)).isOpenMap

variable (α : Spec (CommRingCat.of K) ⟶ Y) (hα : α ≫ y = k₀)

/-- The common dense set on which the three comparison products are defined. -/
def D3 : Set ↑(YK y k₀) :=
  (sig y k₀ β hβ).hom.base '' ((iotab y β U).base '' ((Phib y β U m).base ⁻¹'
    ((sig y k₀ β hβ).hom.base ⁻¹' ((rho y k₀ α hα ⁻¹ᵁ U : (YK y k₀).Opens) : Set ↑(YK y k₀)))))

include hβ in
theorem dense_D3 [IsOpenImmersion (Phi y U m)]
    (hUβ : Dense ((rho y k₀ β hβ ⁻¹ᵁ U : (YK y k₀).Opens) : Set ↑(YK y k₀)))
    (hUα : Dense ((rho y k₀ α hα ⁻¹ᵁ U : (YK y k₀).Opens) : Set ↑(YK y k₀))) :
    Dense (D3 y k₀ β hβ U m α hα) := by
  have h1 := hUα.preimage (Scheme.homeoOfIso (sig y k₀ β hβ)).isOpenMap
  have h2 := h1.preimage (Phib y β U m).isOpenMap
  have h3 := (denseRange_iotab y k₀ β hβ U hUβ).dense_image (iotab y β U).base.hom.continuous h2
  exact (Scheme.homeoOfIso (sig y k₀ β hβ)).surjective.denseRange.dense_image
    (sig y k₀ β hβ).hom.base.hom.continuous h3

theorem Phib_sig_rho : Phib y β U m ≫ (sig y k₀ β hβ).hom ≫ rho y k₀ α hα =
    pullback.lift (pullback.snd _ _ ≫ α) (pullback.fst _ _ ≫ m.1)
      (by rw [Category.assoc, Category.assoc, hα, m.2, ← hβ, ← pullback.condition_assoc,
        Category.assoc]) := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.lift_fst, sig_hom_fst_assoc,
      pullback.lift_snd_assoc, Category.assoc, Category.id_comp]
  · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd, sig_hom_snd,
      pullback.lift_fst_assoc, Category.assoc, pullback.lift_snd]

end Fibre

section KPoints

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
variable (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
variable {K : Type u} [Field K] (k₀ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
variable (a b c : Spec (CommRingCat.of K) ⟶ Y) (ha : a ≫ y = k₀) (hb : b ≫ y = k₀) (hc : c ≫ y = k₀)

/-- The triple point formed from the prescribed field-valued coordinates. -/
abbrev gpt : Spec (CommRingCat.of K) ⟶ Y3 y :=
  pullback.lift (pullback.lift a b (ha.trans hb.symm)) c (by rw [pullback.lift_fst_assoc, ha, hc])

variable (gΓ : Spec (CommRingCat.of K) ⟶ Gc y U m) (hgΓ : gΓ ≫ γc y U m = gpt y k₀ a b c ha hb hc)

include hgΓ in
theorem gΓ_t3 : k₀ ≫ 𝟙 _ = gΓ ≫ γc y U m ≫ t3 y := by
  rw [Category.comp_id, ← Category.assoc gΓ, hgΓ, pullback.lift_snd_assoc, hc]

/-- Map the field fibre to the enlarged multiplication-graph closure. -/
def jg : YK y k₀ ⟶ GY y U m :=
  pullback.map k₀ y (γc y U m ≫ t3 y) y gΓ (𝟙 Y) (𝟙 _) (gΓ_t3 y U m k₀ a b c ha hb hc gΓ hgΓ)
    (by rw [Category.comp_id, Category.id_comp])

@[reassoc]
theorem jg_fst : jg y U m k₀ a b c ha hb hc gΓ hgΓ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ gΓ :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem jg_cw : jg y U m k₀ a b c ha hb hc gΓ hgΓ ≫ cw y U m = pullback.snd _ _ := by
  rw [jg, pullback.lift_snd, Category.comp_id]

include hgΓ in
@[reassoc]
theorem jg_cxy : jg y U m k₀ a b c ha hb hc gΓ hgΓ ≫ cxy y U m =
    pullback.fst _ _ ≫ pullback.lift a b (ha.trans hb.symm) := by
  rw [cxy, jg_fst_assoc, ← Category.assoc gΓ, hgΓ, pullback.lift_fst]

include hgΓ in
@[reassoc]
theorem jg_cx : jg y U m k₀ a b c ha hb hc gΓ hgΓ ≫ cx y U m = pullback.fst _ _ ≫ a := by
  rw [cx, jg_cxy_assoc, pullback.lift_fst]

include hgΓ in
@[reassoc]
theorem jg_cy : jg y U m k₀ a b c ha hb hc gΓ hgΓ ≫ cy y U m = pullback.fst _ _ ≫ b := by
  rw [cy, jg_cxy_assoc, pullback.lift_snd]

include hgΓ in
@[reassoc]
theorem jg_cz : jg y U m k₀ a b c ha hb hc gΓ hgΓ ≫ cz y U m = pullback.fst _ _ ≫ c := by
  rw [cz, jg_fst_assoc, ← Category.assoc gΓ, hgΓ, pullback.lift_snd]

theorem jg_zw : jg y U m k₀ a b c ha hb hc gΓ hgΓ ≫ zw y U m = rho y k₀ c hc := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, jg_cz]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, jg_cw]

theorem jg_yw : jg y U m k₀ a b c ha hb hc gΓ hgΓ ≫ yw y U m = rho y k₀ b hb := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, jg_cy]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, jg_cw]

/-- The associativity domain pulled back to the field fibre. -/
def OmK : (YK y k₀).Opens := jg y U m k₀ a b c ha hb hc gΓ hgΓ ⁻¹ᵁ Om y U m

theorem OmK_le_c : OmK y U m k₀ a b c ha hb hc gΓ hgΓ ≤ rho y k₀ c hc ⁻¹ᵁ U := by
  rw [← jg_zw y U m k₀ a b c ha hb hc gΓ hgΓ, Scheme.Hom.comp_preimage]
  exact (jg y U m k₀ a b c ha hb hc gΓ hgΓ).preimage_mono (Om_le_L1 y U m)

theorem OmK_le_b : OmK y U m k₀ a b c ha hb hc gΓ hgΓ ≤ rho y k₀ b hb ⁻¹ᵁ U := by
  rw [← jg_yw y U m k₀ a b c ha hb hc gΓ hgΓ, Scheme.Hom.comp_preimage]
  exact (jg y U m k₀ a b c ha hb hc gΓ hgΓ).preimage_mono (Om_le_L2 y U m)

variable (W : (YK y k₀).Opens) (hW : W ≤ OmK y U m k₀ a b c ha hb hc gΓ hgΓ)

/-- The product-coordinate pair on the selected comparison open. -/
def cwU : (W : Scheme.{u}) ⟶ (U : Scheme.{u}) :=
  IsOpenImmersion.lift U.ι (W.ι ≫ rho y k₀ c hc) (by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
    exact OmK_le_c y U m k₀ a b c ha hb hc gΓ hgΓ (hW w.2))

@[reassoc]
theorem cwU_ι : cwU y U m k₀ a b c ha hb hc gΓ hgΓ W hW ≫ U.ι = W.ι ≫ rho y k₀ c hc :=
  IsOpenImmersion.lift_fac _ _ _

/-- The second-coordinate pair on the selected comparison open. -/
def bwU : (W : Scheme.{u}) ⟶ (U : Scheme.{u}) :=
  IsOpenImmersion.lift U.ι (W.ι ≫ rho y k₀ b hb) (by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
    exact OmK_le_b y U m k₀ a b c ha hb hc gΓ hgΓ (hW w.2))

@[reassoc]
theorem bwU_ι : bwU y U m k₀ a b c ha hb hc gΓ hgΓ W hW ≫ U.ι = W.ι ≫ rho y k₀ b hb :=
  IsOpenImmersion.lift_fac _ _ _

/-- Map the comparison open into the common associativity domain. -/
def jW : (W : Scheme.{u}) ⟶ ((Om y U m : (GY y U m).Opens) : Scheme.{u}) :=
  IsOpenImmersion.lift (Om y U m).ι (W.ι ≫ jg y U m k₀ a b c ha hb hc gΓ hgΓ) (by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
    exact hW w.2)

@[reassoc]
theorem jW_ι : jW y U m k₀ a b c ha hb hc gΓ hgΓ W hW ≫ (Om y U m).ι = W.ι ≫ jg y U m k₀ a b c ha hb
    hc gΓ hgΓ :=
  IsOpenImmersion.lift_fac _ _ _

theorem jW_uzw : jW y U m k₀ a b c ha hb hc gΓ hgΓ W hW ≫ uzw y U m = cwU y U m k₀ a b c ha hb hc gΓ
    hgΓ W hW := by
  rw [← cancel_mono U.ι, Category.assoc, uzw_ι, jW_ι_assoc, jg_zw, cwU_ι]

theorem jW_uyw : (jW y U m k₀ a b c ha hb hc gΓ hgΓ W hW ≫ toL2 y U m) ≫ uyw y U m =
    bwU y U m k₀ a b c ha hb hc gΓ hgΓ W hW := by
  rw [← cancel_mono U.ι, Category.assoc, Category.assoc, uyw_ι, Scheme.homOfLE_ι_assoc, jW_ι_assoc,
    jg_yw,
    bwU_ι]

/-- The first coordinate paired with the product of the second and extra coordinates. -/
def abwU : (W : Scheme.{u}) ⟶ (U : Scheme.{u}) := jW y U m k₀ a b c ha hb hc gΓ hgΓ W hW ≫ uxyw y U
    m

theorem abwU_ι_fst : abwU y U m k₀ a b c ha hb hc gΓ hgΓ W hW ≫ U.ι ≫ pullback.fst y y =
    W.ι ≫ pullback.fst k₀ y ≫ a := by
  rw [abwU, Category.assoc, uxyw_ι_assoc, pullback.lift_fst, Scheme.homOfLE_ι_assoc, jW_ι_assoc,
    jg_cx]

theorem abwU_ι_snd : abwU y U m k₀ a b c ha hb hc gΓ hgΓ W hW ≫ U.ι ≫ pullback.snd y y =
    bwU y U m k₀ a b c ha hb hc gΓ hgΓ W hW ≫ m.1 := by
  rw [abwU, Category.assoc, uxyw_ι_assoc, pullback.lift_snd, myw, ← Category.assoc, ←
    Category.assoc,
    jW_uyw]

theorem lemma2W (hFG : FF y U m = GG y U m) :
    cwU y U m k₀ a b c ha hb hc gΓ hgΓ W hW ≫ m.1 = abwU y U m k₀ a b c ha hb hc gΓ hgΓ W hW ≫ m.1
      := by
  have h1 : jW y U m k₀ a b c ha hb hc gΓ hgΓ W hW ≫ FF y U m = cwU y U m k₀ a b c ha hb hc gΓ hgΓ W
    hW ≫ m.1 := by
    rw [FF, ← Category.assoc, jW_uzw]
  have h2 : jW y U m k₀ a b c ha hb hc gΓ hgΓ W hW ≫ GG y U m = abwU y U m k₀ a b c ha hb hc gΓ hgΓ
    W hW ≫ m.1 := by
    rw [GG, ← Category.assoc]
    rfl
  rw [← h1, ← h2, hFG]

omit hW in
theorem eq_of_snd_eq_of_mul_eq [Mono (Psi y U m)] (P Q : (W : Scheme.{u}) ⟶ (U : Scheme.{u}))
    (h2 : P ≫ U.ι ≫ pullback.snd y y = Q ≫ U.ι ≫ pullback.snd y y) (hm : P ≫ m.1 = Q ≫ m.1) : P = Q
      := by
  rw [← cancel_mono (Psi y U m)]
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, pullback.lift_fst, hm]
  · rw [Category.assoc, Category.assoc, pullback.lift_snd, h2]

omit hW in
theorem eq_of_fst_eq_of_mul_eq [Mono (Phi y U m)] (P Q : (W : Scheme.{u}) ⟶ (U : Scheme.{u}))
    (h1 : P ≫ U.ι ≫ pullback.fst y y = Q ≫ U.ι ≫ pullback.fst y y) (hm : P ≫ m.1 = Q ≫ m.1) : P = Q
      := by
  rw [← cancel_mono (Phi y U m)]
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, pullback.lift_fst]
    simpa only [Category.assoc] using h1
  · rw [Category.assoc, Category.assoc, pullback.lift_snd, hm]

/-- Map the fibre of the second-pair domain to its open subscheme. -/
def nuL2 : Ub y b U ⟶ ((L2 y U m : (GY y U m).Opens) : Scheme.{u}) :=
  IsOpenImmersion.lift (L2 y U m).ι (iotab y b U ≫ (sig y k₀ b hb).hom ≫ jg y U m k₀ a b c ha hb hc
    gΓ hgΓ) (by
    rintro _ ⟨u', rfl⟩
    rw [Scheme.Opens.range_ι]
    change _ ∈ yw y U m ⁻¹ᵁ U
    change (yw y U m).base _ ∈ U
    rw [← Scheme.Hom.comp_apply, Category.assoc, Category.assoc, jg_yw, sig_hom_rho,
      pullback.lift_fst,
      Scheme.Hom.comp_apply]
    exact ((pullback.fst (U.ι ≫ pullback.fst y y) b).base u').2)

@[reassoc]
theorem nuL2_ι : nuL2 y U m k₀ a b c ha hb hc gΓ hgΓ ≫ (L2 y U m).ι =
    iotab y b U ≫ (sig y k₀ b hb).hom ≫ jg y U m k₀ a b c ha hb hc gΓ hgΓ :=
  IsOpenImmersion.lift_fac _ _ _

theorem nuL2_uyw : nuL2 y U m k₀ a b c ha hb hc gΓ hgΓ ≫ uyw y U m = pullback.fst _ _ := by
  rw [← cancel_mono U.ι, Category.assoc, uyw_ι, nuL2_ι_assoc, jg_yw, sig_hom_rho, pullback.lift_fst]

theorem nuL2_xyw :
    nuL2 y U m k₀ a b c ha hb hc gΓ hgΓ ≫ xyw y U m =
      Phib y b U m ≫ (sig y k₀ b hb).hom ≫ rho y k₀ a ha := by
  rw [Phib_sig_rho]
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, nuL2_ι_assoc, jg_cx,
    sig_hom_fst_assoc,
      pullback.lift_snd_assoc, Category.assoc, Category.id_comp]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, myw, ← Category.assoc, nuL2_uyw]

theorem D3_subset : D3 y k₀ b hb U m a ha ⊆
    ((jg y U m k₀ a b c ha hb hc gΓ hgΓ ⁻¹ᵁ L3 y U m : (YK y k₀).Opens) : Set ↑(YK y k₀)) := by
  rintro _ ⟨_, ⟨u', hu', rfl⟩, rfl⟩
  change (jg y U m k₀ a b c ha hb hc gΓ hgΓ).base ((sig y k₀ b hb).hom.base ((iotab y b U).base u'))
    ∈ L3 y U m
  refine ⟨(nuL2 y U m k₀ a b c ha hb hc gΓ hgΓ).base u', ?_, ?_⟩
  · change (xyw y U m).base ((nuL2 y U m k₀ a b c ha hb hc gΓ hgΓ).base u') ∈ U
    rw [← Scheme.Hom.comp_apply, nuL2_xyw y U m k₀ a b c ha hb hc gΓ hgΓ, Scheme.Hom.comp_apply,
      Scheme.Hom.comp_apply]
    exact hu'
  · change ((nuL2 y U m k₀ a b c ha hb hc gΓ hgΓ) ≫ (L2 y U m).ι) u' =
      ((iotab y b U) ≫ (sig y k₀ b hb).hom ≫ jg y U m k₀ a b c ha hb hc gΓ hgΓ) u'
    rw [nuL2_ι]

theorem dense_OmK [IsOpenImmersion (Phi y U m)]
    (hU₁ : ∀ x : Y, Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} →
      ↑(pullback y y)) ⁻¹' (U : Set ↑(pullback y y)))) :
    Dense ((OmK y U m k₀ a b c ha hb hc gΓ hgΓ : (YK y k₀).Opens) : Set ↑(YK y k₀)) := by
  have hc' := dense_preimage_rho y k₀ c hc U hU₁
  have hb' := dense_preimage_rho y k₀ b hb U hU₁
  have ha' := dense_preimage_rho y k₀ a ha U hU₁
  have h3 : Dense ((jg y U m k₀ a b c ha hb hc gΓ hgΓ ⁻¹ᵁ L3 y U m : (YK y k₀).Opens) : Set ↑(YK y
    k₀)) :=
    (dense_D3 y k₀ b hb U m a ha hb' ha').mono (D3_subset y U m k₀ a b c ha hb hc gΓ hgΓ)
  have h1 : Dense ((jg y U m k₀ a b c ha hb hc gΓ hgΓ ⁻¹ᵁ L1 y U m : (YK y k₀).Opens) : Set ↑(YK y
    k₀)) := by
    rw [L1, ← Scheme.Hom.comp_preimage, jg_zw]
    exact hc'
  have : OmK y U m k₀ a b c ha hb hc gΓ hgΓ =
      jg y U m k₀ a b c ha hb hc gΓ hgΓ ⁻¹ᵁ L1 y U m ⊓ jg y U m k₀ a b c ha hb hc gΓ hgΓ ⁻¹ᵁ L3 y U
        m := rfl
  rw [this]
  exact h1.inter_of_isOpen_right h3 (jg y U m k₀ a b c ha hb hc gΓ hgΓ ⁻¹ᵁ L3 y U m).isOpen

end KPoints

section Clauses

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
variable (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
variable {K : Type u} [Field K] (k₀ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
variable [IsOpenImmersion (Phi y U m)] [IsOpenImmersion (Psi y U m)]
variable (hU₁ : ∀ x : Y, Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q =
    x} →
      ↑(pullback y y)) ⁻¹' (U : Set ↑(pullback y y))))
variable (hFG : FF y U m = GG y U m)

include hU₁ hFG in
theorem clause12 (a b c c' : Spec (CommRingCat.of K) ⟶ Y) (ha : a ≫ y = k₀) (hb : b ≫ y = k₀)
    (hc : c ≫ y = k₀) (hc' : c' ≫ y = k₀)
    (gΓ : Spec (CommRingCat.of K) ⟶ Gc y U m) (hgΓ : gΓ ≫ γc y U m = gpt y k₀ a b c ha hb hc)
    (gΓ' : Spec (CommRingCat.of K) ⟶ Gc y U m) (hgΓ' : gΓ' ≫ γc y U m = gpt y k₀ a b c' ha hb hc') :
    c = c' := by
  let W : (YK y k₀).Opens := OmK y U m k₀ a b c ha hb hc gΓ hgΓ ⊓ OmK y U m k₀ a b c' ha hb hc' gΓ'
    hgΓ'
  have hW1 : W ≤ OmK y U m k₀ a b c ha hb hc gΓ hgΓ := inf_le_left
  have hW2 : W ≤ OmK y U m k₀ a b c' ha hb hc' gΓ' hgΓ' := inf_le_right
  have : Nonempty ↑(YK y k₀) := nonempty_YK y k₀ a ha
  have hWd : Dense ((W : (YK y k₀).Opens) : Set ↑(YK y k₀)) :=
    (dense_OmK y U m k₀ a b c ha hb hc gΓ hgΓ hU₁).inter_of_isOpen_right
      (dense_OmK y U m k₀ a b c' ha hb hc' gΓ' hgΓ' hU₁) (OmK y U m k₀ a b c' ha hb hc' gΓ'
        hgΓ').isOpen
  have : Nonempty (W : Scheme.{u}) := by obtain ⟨w, hw⟩ := hWd.nonempty; exact ⟨⟨w, hw⟩⟩
  have hbw : bwU y U m k₀ a b c ha hb hc gΓ hgΓ W hW1 = bwU y U m k₀ a b c' ha hb hc' gΓ' hgΓ' W hW2
    := by
    rw [← cancel_mono U.ι, bwU_ι, bwU_ι]
  have habw : abwU y U m k₀ a b c ha hb hc gΓ hgΓ W hW1 = abwU y U m k₀ a b c' ha hb hc' gΓ' hgΓ' W
    hW2 := by
    rw [← cancel_mono U.ι]
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, abwU_ι_fst, abwU_ι_fst]
    · rw [Category.assoc, Category.assoc, abwU_ι_snd, abwU_ι_snd, hbw]
  have hm : cwU y U m k₀ a b c ha hb hc gΓ hgΓ W hW1 ≫ m.1 = cwU y U m k₀ a b c' ha hb hc' gΓ' hgΓ'
    W hW2 ≫ m.1 := by
    rw [lemma2W y U m k₀ a b c ha hb hc gΓ hgΓ W hW1 hFG, lemma2W y U m k₀ a b c' ha hb hc' gΓ' hgΓ'
      W hW2 hFG,
      habw]
  have h2 : cwU y U m k₀ a b c ha hb hc gΓ hgΓ W hW1 ≫ U.ι ≫ pullback.snd y y =
      cwU y U m k₀ a b c' ha hb hc' gΓ' hgΓ' W hW2 ≫ U.ι ≫ pullback.snd y y := by
    rw [cwU_ι_assoc, cwU_ι_assoc, pullback.lift_snd, pullback.lift_snd]
  have hPQ := eq_of_snd_eq_of_mul_eq y U m k₀ W _ _ h2 hm
  have h1 := congrArg (fun P => P ≫ U.ι ≫ pullback.fst y y) hPQ
  simp only [cwU_ι_assoc, pullback.lift_fst] at h1
  exact eq_of_comp_eq_of_nonempty (W.ι ≫ pullback.fst k₀ y) c c' (by simpa only [Category.assoc]
    using h1)

include hU₁ hFG in
theorem clause13 (a b b' c : Spec (CommRingCat.of K) ⟶ Y) (ha : a ≫ y = k₀) (hb : b ≫ y = k₀)
    (hb' : b' ≫ y = k₀) (hc : c ≫ y = k₀)
    (gΓ : Spec (CommRingCat.of K) ⟶ Gc y U m) (hgΓ : gΓ ≫ γc y U m = gpt y k₀ a b c ha hb hc)
    (gΓ' : Spec (CommRingCat.of K) ⟶ Gc y U m) (hgΓ' : gΓ' ≫ γc y U m = gpt y k₀ a b' c ha hb' hc) :
    b = b' := by
  let W : (YK y k₀).Opens := OmK y U m k₀ a b c ha hb hc gΓ hgΓ ⊓ OmK y U m k₀ a b' c ha hb' hc gΓ'
    hgΓ'
  have hW1 : W ≤ OmK y U m k₀ a b c ha hb hc gΓ hgΓ := inf_le_left
  have hW2 : W ≤ OmK y U m k₀ a b' c ha hb' hc gΓ' hgΓ' := inf_le_right
  have : Nonempty ↑(YK y k₀) := nonempty_YK y k₀ a ha
  have hWd : Dense ((W : (YK y k₀).Opens) : Set ↑(YK y k₀)) :=
    (dense_OmK y U m k₀ a b c ha hb hc gΓ hgΓ hU₁).inter_of_isOpen_right
      (dense_OmK y U m k₀ a b' c ha hb' hc gΓ' hgΓ' hU₁) (OmK y U m k₀ a b' c ha hb' hc gΓ'
        hgΓ').isOpen
  have : Nonempty (W : Scheme.{u}) := by obtain ⟨w, hw⟩ := hWd.nonempty; exact ⟨⟨w, hw⟩⟩
  have hcw : cwU y U m k₀ a b c ha hb hc gΓ hgΓ W hW1 = cwU y U m k₀ a b' c ha hb' hc gΓ' hgΓ' W hW2
    := by
    rw [← cancel_mono U.ι, cwU_ι, cwU_ι]
  have hm : abwU y U m k₀ a b c ha hb hc gΓ hgΓ W hW1 ≫ m.1 = abwU y U m k₀ a b' c ha hb' hc gΓ'
    hgΓ' W hW2 ≫ m.1 := by
    rw [← lemma2W y U m k₀ a b c ha hb hc gΓ hgΓ W hW1 hFG, ← lemma2W y U m k₀ a b' c ha hb' hc gΓ'
      hgΓ' W hW2 hFG,
      hcw]
  have h1 : abwU y U m k₀ a b c ha hb hc gΓ hgΓ W hW1 ≫ U.ι ≫ pullback.fst y y =
      abwU y U m k₀ a b' c ha hb' hc gΓ' hgΓ' W hW2 ≫ U.ι ≫ pullback.fst y y := by
    rw [abwU_ι_fst, abwU_ι_fst]
  have hPQ := eq_of_fst_eq_of_mul_eq y U m k₀ W _ _ h1 hm
  have h3 := congrArg (fun P => P ≫ U.ι ≫ pullback.snd y y) hPQ
  simp only [abwU_ι_snd] at h3
  have h4 : bwU y U m k₀ a b c ha hb hc gΓ hgΓ W hW1 ≫ U.ι ≫ pullback.snd y y =
      bwU y U m k₀ a b' c ha hb' hc gΓ' hgΓ' W hW2 ≫ U.ι ≫ pullback.snd y y := by
    rw [bwU_ι_assoc, bwU_ι_assoc, pullback.lift_snd, pullback.lift_snd]
  have hPQ' := eq_of_snd_eq_of_mul_eq y U m k₀ W _ _ h4 h3
  have h5 := congrArg (fun P => P ≫ U.ι ≫ pullback.fst y y) hPQ'
  simp only [bwU_ι_assoc, pullback.lift_fst] at h5
  exact eq_of_comp_eq_of_nonempty (W.ι ≫ pullback.fst k₀ y) b b' (by simpa only [Category.assoc]
    using h5)

include hU₁ hFG in
theorem clause23 (a a' b c : Spec (CommRingCat.of K) ⟶ Y) (ha : a ≫ y = k₀) (ha' : a' ≫ y = k₀)
    (hb : b ≫ y = k₀) (hc : c ≫ y = k₀)
    (gΓ : Spec (CommRingCat.of K) ⟶ Gc y U m) (hgΓ : gΓ ≫ γc y U m = gpt y k₀ a b c ha hb hc)
    (gΓ' : Spec (CommRingCat.of K) ⟶ Gc y U m) (hgΓ' : gΓ' ≫ γc y U m = gpt y k₀ a' b c ha' hb hc) :
    a = a' := by
  let W : (YK y k₀).Opens := OmK y U m k₀ a b c ha hb hc gΓ hgΓ ⊓ OmK y U m k₀ a' b c ha' hb hc gΓ'
    hgΓ'
  have hW1 : W ≤ OmK y U m k₀ a b c ha hb hc gΓ hgΓ := inf_le_left
  have hW2 : W ≤ OmK y U m k₀ a' b c ha' hb hc gΓ' hgΓ' := inf_le_right
  have : Nonempty ↑(YK y k₀) := nonempty_YK y k₀ a ha
  have hWd : Dense ((W : (YK y k₀).Opens) : Set ↑(YK y k₀)) :=
    (dense_OmK y U m k₀ a b c ha hb hc gΓ hgΓ hU₁).inter_of_isOpen_right
      (dense_OmK y U m k₀ a' b c ha' hb hc gΓ' hgΓ' hU₁) (OmK y U m k₀ a' b c ha' hb hc gΓ'
        hgΓ').isOpen
  have : Nonempty (W : Scheme.{u}) := by obtain ⟨w, hw⟩ := hWd.nonempty; exact ⟨⟨w, hw⟩⟩
  have hcw : cwU y U m k₀ a b c ha hb hc gΓ hgΓ W hW1 = cwU y U m k₀ a' b c ha' hb hc gΓ' hgΓ' W hW2
    := by
    rw [← cancel_mono U.ι, cwU_ι, cwU_ι]
  have hbw : bwU y U m k₀ a b c ha hb hc gΓ hgΓ W hW1 = bwU y U m k₀ a' b c ha' hb hc gΓ' hgΓ' W hW2
    := by
    rw [← cancel_mono U.ι, bwU_ι, bwU_ι]
  have hm : abwU y U m k₀ a b c ha hb hc gΓ hgΓ W hW1 ≫ m.1 = abwU y U m k₀ a' b c ha' hb hc gΓ'
    hgΓ' W hW2 ≫ m.1 := by
    rw [← lemma2W y U m k₀ a b c ha hb hc gΓ hgΓ W hW1 hFG, ← lemma2W y U m k₀ a' b c ha' hb hc gΓ'
      hgΓ' W hW2 hFG,
      hcw]
  have h2 : abwU y U m k₀ a b c ha hb hc gΓ hgΓ W hW1 ≫ U.ι ≫ pullback.snd y y =
      abwU y U m k₀ a' b c ha' hb hc gΓ' hgΓ' W hW2 ≫ U.ι ≫ pullback.snd y y := by
    rw [abwU_ι_snd, abwU_ι_snd, hbw]
  have hPQ := eq_of_snd_eq_of_mul_eq y U m k₀ W _ _ h2 hm
  have h1 := congrArg (fun P => P ≫ U.ι ≫ pullback.fst y y) hPQ
  simp only [abwU_ι_fst] at h1
  exact eq_of_comp_eq_of_nonempty (W.ι ≫ pullback.fst k₀ y) a a' (by simpa only [Category.assoc]
    using h1)

end Clauses

section Main

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
variable {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R)) [Smooth y] [IsSeparated y]
variable (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)

theorem injK
    (hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y
        y)) ⁻¹'
        (U : Set ↑(pullback y y))))
    (hΦ : IsOpenImmersion (Phi y U m)) (hΨ : IsOpenImmersion (Psi y U m))
    (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
      p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫
        pullback.snd y y →
      q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y =
        v.1 ≫ m.1 →
      p.1 ≫ m.1 = q.1 ≫ m.1)
    {K : Type u} [Field K] (g g' : Spec (CommRingCat.of K) ⟶ Y3 y)
    (hg : Set.range g.base ⊆ closure (Set.range (gr y U m).base))
    (hg' : Set.range g'.base ⊆ closure (Set.range (gr y U m).base)) :
    (g ≫ P12 y = g' ≫ P12 y → g = g') ∧
    (g ≫ pullback.lift (f := y) (g := y)
        (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.fst y y) (pullback.snd (pullback.fst y y ≫
          y) y)
        (by rw [Category.assoc]; exact pullback.condition) =
      g' ≫ pullback.lift (f := y) (g := y)
        (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.fst y y) (pullback.snd (pullback.fst y y ≫
          y) y)
        (by rw [Category.assoc]; exact pullback.condition) → g = g') ∧
    (g ≫ pullback.lift (f := y) (g := y)
        (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.snd y y) (pullback.snd (pullback.fst y y ≫
          y) y)
        (by rw [Category.assoc, ← pullback.condition (f := y) (g := y)]; exact pullback.condition) =
      g' ≫ pullback.lift (f := y) (g := y)
        (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.snd y y) (pullback.snd (pullback.fst y y ≫
          y) y)
        (by rw [Category.assoc, ← pullback.condition (f := y) (g := y)]; exact pullback.condition) →
          g = g') := by
  have : IsOpenImmersion (Phi y U m) := hΦ
  have : IsOpenImmersion (Psi y U m) := hΨ
  have : UniversallyOpen m.1 := universallyOpen_m y U m hΦ
  have hU : Dense (U : Set ↑(pullback y y)) := dense_of_forall_dense_fibre _ _ hU₁
  have : IsReduced (U : Scheme.{u}) :=
    AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian (U.ι ≫ pullback.fst y y ≫
      y)
  obtain ⟨g₀, hg₀⟩ := exists_comp_γc_eq y U m (gr y U m) subset_closure
  have hFG : FF y U m = GG y U m := FF_eq_GG y U m g₀ hg₀ hassoc hU
  let k₀ := g ≫ t3 y
  let a := g ≫ P12 y ≫ pullback.fst y y
  let b := g ≫ P12 y ≫ pullback.snd y y
  let c := g ≫ pullback.snd (pullback.fst y y ≫ y) y
  have ha : a ≫ y = k₀ := by simp only [a, k₀, Category.assoc, P12_fst_y]
  have hb : b ≫ y = k₀ := by simp only [b, k₀, Category.assoc, P12_snd_y]
  have hc : c ≫ y = k₀ := by simp only [c, k₀, Category.assoc]
  let a' := g' ≫ P12 y ≫ pullback.fst y y
  let b' := g' ≫ P12 y ≫ pullback.snd y y
  let c' := g' ≫ pullback.snd (pullback.fst y y ≫ y) y
  obtain ⟨gΓ, hgΓ0⟩ := exists_comp_γc_eq y U m g hg
  obtain ⟨gΓ', hgΓ0'⟩ := exists_comp_γc_eq y U m g' hg'
  have key : ∀ (h : Spec (CommRingCat.of K) ⟶ Y3 y) (α β γ : Spec (CommRingCat.of K) ⟶ Y)
      (hα : α ≫ y = k₀) (hβ : β ≫ y = k₀) (hγ : γ ≫ y = k₀),
      h ≫ P12 y ≫ pullback.fst y y = α → h ≫ P12 y ≫ pullback.snd y y = β →
      h ≫ pullback.snd (pullback.fst y y ≫ y) y = γ → h = gpt y k₀ α β γ hα hβ hγ := by
    intro h α β γ hα hβ hγ h1 h2 h3
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · rw [pullback.lift_fst, pullback.lift_fst, ← h1, Category.assoc]
      · rw [pullback.lift_fst, pullback.lift_snd, ← h2, Category.assoc]
    · rw [pullback.lift_snd, ← h3]
  refine ⟨fun h12 => ?_, fun h13 => ?_, fun h23 => ?_⟩
  · have e1 : a' = a := by simp only [a', a, ← Category.assoc, h12]
    have e2 : b' = b := by simp only [b', b, ← Category.assoc, h12]
    have hc' : c' ≫ y = k₀ := by
      simp only [c', k₀, Category.assoc]
      change g' ≫ t3 y = g ≫ t3 y
      rw [← P12_fst_y, ← Category.assoc, ← h12, Category.assoc]
    have hgΓ : gΓ ≫ γc y U m = gpt y k₀ a b c ha hb hc := hgΓ0.trans (key g a b c ha hb hc rfl rfl
      rfl)
    have hgΓ' : gΓ' ≫ γc y U m = gpt y k₀ a b c' ha hb hc' := hgΓ0'.trans (key g' a b c' ha hb hc'
      e1 e2 rfl)
    have hcc := clause12 y U m k₀ hU₁ hFG a b c c' ha hb hc hc' gΓ hgΓ gΓ' hgΓ'
    rw [key g a b c ha hb hc rfl rfl rfl, key g' a b c' ha hb hc' e1 e2 rfl]
    simp only [hcc]
  · have e1 : a' = a := by
      have := congrArg (fun t => t ≫ pullback.fst y y) h13
      simpa only [Category.assoc, pullback.lift_fst] using this.symm
    have e3 : c' = c := by
      have := congrArg (fun t => t ≫ pullback.snd y y) h13
      simpa only [Category.assoc, pullback.lift_snd] using this.symm
    have hb' : b' ≫ y = k₀ := by
      simp only [b', k₀, Category.assoc, P12_snd_y]
      change g' ≫ pullback.snd _ _ ≫ y = g ≫ pullback.snd _ _ ≫ y
      rw [← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ y) e3
    have hgΓ : gΓ ≫ γc y U m = gpt y k₀ a b c ha hb hc := hgΓ0.trans (key g a b c ha hb hc rfl rfl
      rfl)
    have hgΓ' : gΓ' ≫ γc y U m = gpt y k₀ a b' c ha hb' hc := hgΓ0'.trans (key g' a b' c ha hb' hc
      e1 rfl e3)
    have hbb := clause13 y U m k₀ hU₁ hFG a b b' c ha hb hb' hc gΓ hgΓ gΓ' hgΓ'
    rw [key g a b c ha hb hc rfl rfl rfl, key g' a b' c ha hb' hc e1 rfl e3]
    simp only [hbb]
  · have e2 : b' = b := by
      have := congrArg (fun t => t ≫ pullback.fst y y) h23
      simpa only [Category.assoc, pullback.lift_fst] using this.symm
    have e3 : c' = c := by
      have := congrArg (fun t => t ≫ pullback.snd y y) h23
      simpa only [Category.assoc, pullback.lift_snd] using this.symm
    have ha' : a' ≫ y = k₀ := by
      simp only [a', k₀, Category.assoc, P12_fst_y]
      change g' ≫ pullback.snd _ _ ≫ y = g ≫ pullback.snd _ _ ≫ y
      rw [← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ y) e3
    have hgΓ : gΓ ≫ γc y U m = gpt y k₀ a b c ha hb hc := hgΓ0.trans (key g a b c ha hb hc rfl rfl
      rfl)
    have hgΓ' : gΓ' ≫ γc y U m = gpt y k₀ a' b c ha' hb hc := hgΓ0'.trans (key g' a' b c ha' hb hc
      rfl e2 e3)
    have haa := clause23 y U m k₀ hU₁ hFG a a' b c ha ha' hb hc gΓ hgΓ gΓ' hgΓ'
    rw [key g a b c ha hb hc rfl rfl rfl, key g' a' b c ha' hb hc rfl e2 e3]
    simp only [haa]

end Main

end GraphClosure

end
end AbelianVarieties.NOSProofs.GraphClosureRigidity

namespace NeronModelInfra

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian
open AbelianVarieties.NOSProofs.GraphClosureRigidity

theorem eq_of_comp_eq_of_range_subset_closure_range_lift_of_forall_dense_preimage_fibre
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
    [Smooth y] [IsSeparated y]
    (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
    (hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y
        y)) ⁻¹'
        (U : Set ↑(pullback y y))))
    (hΦ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1 ((Category.assoc _ _ _).trans
        m.2.symm)))
    (hΨ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
        (m.2.trans (by rw [Category.assoc, pullback.condition]))))
    (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
      p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫
        pullback.snd y y →
      q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y =
        v.1 ≫ m.1 →
      p.1 ≫ m.1 = q.1 ≫ m.1)
    {K : Type u} [Field K] (g g' : Spec (CommRingCat.of K) ⟶ pullback (pullback.fst y y ≫ y) y)
    (hg : Set.range g.base ⊆
      closure (Set.range (pullback.lift (f := pullback.fst y y ≫ y) (g := y) U.ι m.1
        m.2.symm).base))
    (hg' : Set.range g'.base ⊆
      closure (Set.range (pullback.lift (f := pullback.fst y y ≫ y) (g := y) U.ι m.1
        m.2.symm).base)) :
    (g ≫ pullback.fst (pullback.fst y y ≫ y) y = g' ≫ pullback.fst (pullback.fst y y ≫ y) y → g =
      g') ∧
    (g ≫ pullback.lift (f := y) (g := y)
        (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.fst y y) (pullback.snd (pullback.fst y y ≫
          y) y)
        (by rw [Category.assoc]; exact pullback.condition) =
      g' ≫ pullback.lift (f := y) (g := y)
        (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.fst y y) (pullback.snd (pullback.fst y y ≫
          y) y)
        (by rw [Category.assoc]; exact pullback.condition) → g = g') ∧
    (g ≫ pullback.lift (f := y) (g := y)
        (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.snd y y) (pullback.snd (pullback.fst y y ≫
          y) y)
        (by rw [Category.assoc, ← pullback.condition (f := y) (g := y)]; exact pullback.condition) =
      g' ≫ pullback.lift (f := y) (g := y)
        (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.snd y y) (pullback.snd (pullback.fst y y ≫
          y) y)
        (by rw [Category.assoc, ← pullback.condition (f := y) (g := y)]; exact pullback.condition) →
          g = g') :=
  GraphClosure.injK y U m hU₁ hΦ hΨ hassoc g g' hg hg'

end NeronModelInfra
end
