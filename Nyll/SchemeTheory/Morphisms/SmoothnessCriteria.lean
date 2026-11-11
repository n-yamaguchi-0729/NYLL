/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.RingTheory.Etale.Descent
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Set
public import Nyll.SchemeTheory.BaseChange.SchemeHomOver
public import Nyll.SchemeTheory.RingTheory.Smooth.DifferentialCriteria
public import Nyll.SchemeTheory.Descent.FlatMorphisms
public import Nyll.SchemeTheory.RingTheory.FieldExtensions.DVRFractionFieldAway

/-!
# Smoothness and relative dimension

Descent of smoothness and its relative dimension, subtraction of relative dimensions,
and spreading a fixed smooth relative dimension from the generic fiber of a DVR.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Smooth_exists_mem_and_smoothOfRelativeDimension_opensInclusion_comp.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.Smoothness.LocalRelativeDimension
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u
private theorem exists_relativeDimension
    {R S : Type u} [CommRing R] [CommRing S] {φ : R →+* S} (h : φ.IsStandardSmooth) :
    ∃ n : ℕ, φ.IsStandardSmoothOfRelativeDimension n := by
  let : Algebra R S := φ.toAlgebra
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := h.out
  exact ⟨P.dimension, P.isStandardSmoothOfRelativeDimension rfl⟩

end SchemeTheory.Smoothness.LocalRelativeDimension

namespace AlgebraicGeometry

universe u
open CategoryTheory CategoryTheory.Limits NeronModelInfra
open SchemeTheory.Smoothness.LocalRelativeDimension

theorem Smooth.exists_mem_and_smoothOfRelativeDimension_opensInclusion_comp
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] (x : X) :
    ∃ (V : X.Opens) (d : ℕ), x ∈ V ∧ SmoothOfRelativeDimension d (V.ι ≫ f) := by
  obtain ⟨U, hU, V, hV, hx, e, hstd⟩ := Smooth.exists_isStandardSmooth f x
  obtain ⟨d, hd⟩ := exists_relativeDimension hstd
  refine ⟨V, d, hx, ?_⟩
  have hres : SmoothOfRelativeDimension d (f.resLE U V e) := by
    have : IsAffine V := hV
    have : IsAffine U := hU
    rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension d)]
    have := (RingHom.toMorphismProperty_respectsIso_iff.mp
      (RingHom.locally_respectsIso
        (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := d))))
    refine ((MorphismProperty.arrow_mk_iso_iff (RingHom.toMorphismProperty
      (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension d)))
      (arrowResLEAppIso f U V e)).mpr ?_)
    exact RingHom.locally_of (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := d)) _ hd
  rw [← Scheme.Hom.resLE_comp_ι f e]
  have : SmoothOfRelativeDimension (d + 0) (f.resLE U V e ≫ U.ι) := inferInstance
  simpa only [Nat.add_zero] using this

end AlgebraicGeometry
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_SmoothOfRelativeDimension_of_isPullback_of_flat_of_surjective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.Smoothness.RelativeDimensionDescent

universe u

open TensorProduct

namespace RelDimDescent

theorem rank_baseChange_eq {A : Type u} (B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Nontrivial B] (N : Type u) [AddCommGroup N] [Module A N] [Module.Free A N] :
    Module.rank B (B ⊗[A] N) = Module.rank A N := by
  have : Nontrivial A := (algebraMap A B).domain_nontrivial
  simpa only [Cardinal.lift_id] using (Module.rank_baseChange (R := B) (S := A) (M' := N))

theorem rank_eq_of_equiv {A : Type u} [CommRing A] {M N : Type u} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (e : M ≃ₗ[A] N) : Module.rank A M = Module.rank A N :=
  e.rank_eq

section Key

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

/-- Localization of Kähler differentials, with the existing localization algebra. -/
noncomputable def omegaLocEquiv (T' : Type u) [CommRing T']
    [Algebra T T'] [Algebra R T'] [IsScalarTower R T T']
    (M : Submonoid T) [IsLocalization M T'] :
    Ω[T'⁄R] ≃ₗ[T'] T' ⊗[T] Ω[T⁄R] :=
  have : Algebra.FormallyEtale T T' := Algebra.FormallyEtale.of_isLocalization M
  (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R T T').symm

end Key

theorem isStandardSmoothOfRelativeDimension_of_faithfullyFlat
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [Module.FaithfullyFlat R S] (n : ℕ)
    (hloc : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)
      (algebraMap S (S ⊗[R] T)))
    (Tt : Type u) [CommRing Tt] [Algebra T Tt] [Algebra R Tt] [IsScalarTower R T Tt] (t : T)
    [IsLocalization.Away t Tt] [Nontrivial Tt] [Algebra.IsStandardSmooth R Tt] :
    Algebra.IsStandardSmoothOfRelativeDimension n R Tt := by
  classical
  rw [Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth]
  let : Algebra T (S ⊗[R] T) := Algebra.TensorProduct.rightAlgebra
  have : Nontrivial (S ⊗[R] Tt) := by
    rw [Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right]; infer_instance
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal (S ⊗[R] Tt)
  let φ : S ⊗[R] T →ₐ[S] S ⊗[R] Tt :=
    Algebra.TensorProduct.map (AlgHom.id S S) (IsScalarTower.toAlgHom R T Tt)
  let 𝔮 : Ideal (S ⊗[R] T) := 𝔪.comap φ
  have h𝔮 : 𝔮.IsPrime := Ideal.comap_isPrime φ 𝔪
  have ha : ((1 : S) ⊗ₜ[R] t : S ⊗[R] T) ∉ 𝔮 := by
    intro h
    have hu : IsUnit (φ ((1 : S) ⊗ₜ[R] t)) := by
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.coe_toAlgHom']
      exact ((IsLocalization.Away.algebraMap_isUnit t).map
        (Algebra.TensorProduct.includeRight : Tt →ₐ[R] S ⊗[R] Tt))
    exact h𝔪.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
  obtain ⟨sA, hsA, hP⟩ := hloc
  obtain ⟨u, hu, hu𝔮⟩ : ∃ u ∈ sA, u ∉ 𝔮 := by
    by_contra hcon
    push Not at hcon
    have : Ideal.span sA ≤ 𝔮 := Ideal.span_le.mpr hcon
    rw [hsA, top_le_iff] at this
    exact h𝔮.ne_top this
  let Au := Localization.Away u
  let C := Localization.AtPrime 𝔮
  have hAu : Algebra.IsStandardSmoothOfRelativeDimension n S Au := by
    have := hP u hu
    rwa [← IsScalarTower.algebraMap_eq (R := S) (S := S ⊗[R] T) (A := Au),
      RingHom.isStandardSmoothOfRelativeDimension_algebraMap] at this
  have : Algebra.IsStandardSmooth S Au := hAu.isStandardSmooth
  have hCt : IsUnit (algebraMap T C t) := by
    rw [IsScalarTower.algebraMap_apply T (S ⊗[R] T) C]
    exact IsLocalization.map_units C (⟨(1 : S) ⊗ₜ[R] t, ha⟩ : 𝔮.primeCompl)
  have hCu : IsUnit (algebraMap (S ⊗[R] T) C u) :=
    IsLocalization.map_units C (⟨u, hu𝔮⟩ : 𝔮.primeCompl)
  let algTtC : Algebra Tt C := (IsLocalization.Away.lift t hCt).toAlgebra
  have : IsScalarTower T Tt C := IsScalarTower.of_algebraMap_eq fun x =>
    (IsLocalization.Away.lift_eq t hCt x).symm
  let algAuC : Algebra Au C := (IsLocalization.Away.lift u hCu).toAlgebra
  have : IsScalarTower (S ⊗[R] T) Au C := IsScalarTower.of_algebraMap_eq fun x =>
    (IsLocalization.Away.lift_eq u hCu x).symm
  have : IsScalarTower T Au C := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply T (S ⊗[R] T) Au,
      IsScalarTower.algebraMap_apply T (S ⊗[R] T) C,
      ← IsScalarTower.algebraMap_apply (S ⊗[R] T) Au C]
  have : Nontrivial Au := (algebraMap Au C).domain_nontrivial
  have eT : Ω[Tt⁄R] ≃ₗ[Tt] Tt ⊗[T] Ω[T⁄R] := omegaLocEquiv (R := R) Tt (Submonoid.powers t)
  have eA : Ω[(S ⊗[R] T)⁄S] ≃ₗ[S ⊗[R] T] (S ⊗[R] T) ⊗[T] Ω[T⁄R] :=
    (KaehlerDifferential.tensorKaehlerEquiv R S T (S ⊗[R] T)).symm
  have : Algebra.FormallyEtale (S ⊗[R] T) Au :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers u)
  have eAu : Ω[Au⁄S] ≃ₗ[Au] Au ⊗[T] Ω[T⁄R] :=
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale S (S ⊗[R] T) Au).symm
      ≪≫ₗ TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl Au Au) eA
      ≪≫ₗ TensorProduct.AlgebraTensorModule.cancelBaseChange T (S ⊗[R] T) Au Au Ω[T⁄R]
  have e1 : C ⊗[T] Ω[T⁄R] ≃ₗ[C] C ⊗[Tt] Ω[Tt⁄R] :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange T Tt C C Ω[T⁄R]).symm
      ≪≫ₗ TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl C C) eT.symm
  have e2 : C ⊗[T] Ω[T⁄R] ≃ₗ[C] C ⊗[Au] Ω[Au⁄S] :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange T Au C C Ω[T⁄R]).symm
      ≪≫ₗ TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl C C) eAu.symm
  have h1 : Module.rank C (C ⊗[Tt] Ω[Tt⁄R]) = Module.rank Tt Ω[Tt⁄R] := rank_baseChange_eq C Ω[Tt⁄R]
  have h2 : Module.rank C (C ⊗[Au] Ω[Au⁄S]) = Module.rank Au Ω[Au⁄S] := rank_baseChange_eq C Ω[Au⁄S]
  have h3 : Module.rank Au Ω[Au⁄S] = n :=
    Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n
  rw [← h1, ← e1.rank_eq, e2.rank_eq, h2, h3]

theorem nontrivial_localization_away {T : Type u} [CommRing T] {t : T} (ht : ¬ IsNilpotent t) :
    Nontrivial (Localization.Away t) := by
  by_contra h
  have hs : Subsingleton (Localization.Away t) := not_nontrivial_iff_subsingleton.mp h
  have h01 : algebraMap T (Localization.Away t) 1 = algebraMap T (Localization.Away t) 0 :=
    hs.elim _ _
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers t) _).mp h01
  obtain ⟨m, hm⟩ := c.2
  apply ht
  refine ⟨m, ?_⟩
  have hm' : t ^ m = (c : T) := hm
  rw [hm']
  simpa only [mul_one, mul_zero] using hc

theorem span_not_isNilpotent_eq_top {T : Type u} [CommRing T] {s : Set T} (hs : Ideal.span s = ⊤) :
    Ideal.span {t ∈ s | ¬ IsNilpotent t} = ⊤ := by
  rw [← Ideal.radical_eq_top, eq_top_iff, ← hs]
  refine Ideal.span_le.mpr fun t ht => ?_
  by_cases hn : IsNilpotent t
  · obtain ⟨m, hm⟩ := hn
    exact ⟨m, by rw [hm]; exact Ideal.zero_mem _⟩
  · exact Ideal.le_radical (Ideal.subset_span ⟨ht, hn⟩)

theorem codescendsAlong (n : ℕ) :
    RingHom.CodescendsAlong (fun {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) =>
        RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) f)
      (fun {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) => RingHom.FaithfullyFlat f) := by
  refine RingHom.CodescendsAlong.mk _
    (RingHom.locally_respectsIso RingHom.isStandardSmoothOfRelativeDimension_respectsIso) ?_
  intro R S T _ _ _ _ _ h h'
  have : Module.FaithfullyFlat R S := (RingHom.faithfullyFlat_algebraMap_iff).mp h
  have hsm : Algebra.Smooth R T := by
    have hST : (algebraMap S (S ⊗[R] T)).Smooth := by
      rw [RingHom.smooth_iff_locally_isStandardSmooth]
      exact RingHom.locally_of_locally
        (fun {R' S' : Type u} [CommRing R'] [CommRing S'] (f : R' →+* S')
          (hf : RingHom.IsStandardSmoothOfRelativeDimension n f) =>
          RingHom.IsStandardSmoothOfRelativeDimension.isStandardSmooth n f hf) h'
    rw [RingHom.smooth_algebraMap] at hST
    exact Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat S
  have hls : RingHom.Locally RingHom.IsStandardSmooth (algebraMap R T) := by
    rw [← RingHom.smooth_iff_locally_isStandardSmooth, RingHom.smooth_algebraMap]; exact hsm
  obtain ⟨s, hs, hstd⟩ := hls
  refine ⟨{t ∈ s | ¬ IsNilpotent t}, span_not_isNilpotent_eq_top hs, ?_⟩
  intro t ht
  have : Nontrivial (Localization.Away t) := nontrivial_localization_away ht.2
  have h1 := hstd t ht.1
  rw [← IsScalarTower.algebraMap_eq (R := R) (S := T) (A := Localization.Away t)] at h1 ⊢
  rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  have : Algebra.IsStandardSmooth R (Localization.Away t) :=
    (RingHom.isStandardSmooth_algebraMap).mp h1
  exact isStandardSmoothOfRelativeDimension_of_faithfullyFlat n h' (Localization.Away t) t

end RelDimDescent

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

end SchemeTheory.Smoothness.RelativeDimensionDescent

namespace AlgebraicGeometry

universe u
open CategoryTheory CategoryTheory.Limits NeronModelInfra
open SchemeTheory.Smoothness.RelativeDimensionDescent

theorem SmoothOfRelativeDimension.of_isPullback_of_flat_of_surjective (n : ℕ)
    {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (H : IsPullback fst snd f g) [Flat f] [Surjective f] [QuasiCompact f]
    [SmoothOfRelativeDimension n fst] : SmoothOfRelativeDimension n g := by
  have : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension n) :=
    smoothOfRelativeDimension_isStableUnderBaseChange n
  have : MorphismProperty.DescendsAlong (@SmoothOfRelativeDimension n)
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
    HasRingHomProperty.descendsAlong_flat (RelDimDescent.codescendsAlong n)
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @SmoothOfRelativeDimension n)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) H ⟨⟨‹_›, ‹_›⟩, ‹_›⟩ ‹_›

end AlgebraicGeometry
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_SmoothOfRelativeDimension_of_comp_of_smoothOfRelativeDimension_of_surjective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.Smoothness.RelativeDimensionComposition

universe u

open TensorProduct

namespace RelDimSub

open SchemeTheory.Smoothness.RelativeDimensionDescent.RelDimDescent
  (rank_baseChange_eq omegaLocEquiv)

theorem exists_kaehler_equiv_prod (R S C : Type u)
    [CommRing R] [CommRing S] [CommRing C] [Algebra R S]
    [Algebra S C] [Algebra R C] [IsScalarTower R S C] [Algebra.FormallySmooth S C]
    [Module.Projective C Ω[C⁄S]] :
    Nonempty (Ω[C⁄R] ≃ₗ[C] (C ⊗[S] Ω[S⁄R]) × Ω[C⁄S]) := by
  have hex : Function.Exact (KaehlerDifferential.mapBaseChange R S C)
      (KaehlerDifferential.map R S C C) :=
    KaehlerDifferential.exact_mapBaseChange_map R S C
  have hinj : Function.Injective (KaehlerDifferential.mapBaseChange R S C) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R S C x).mp hx
    have : Subsingleton (Algebra.H1Cotangent S C) := Algebra.FormallySmooth.subsingleton_h1Cotangent
    rw [Subsingleton.elim y 0, map_zero]
  have hsurj : Function.Surjective (KaehlerDifferential.map R S C C) :=
    KaehlerDifferential.map_surjective R S C
  obtain ⟨l, hl⟩ :=
    Module.projective_lifting_property (KaehlerDifferential.map R S C C) LinearMap.id hsurj
  exact ⟨(hex.splitSurjectiveEquiv hinj ⟨l, hl⟩).1⟩

theorem rank_kaehler_eq_sub {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
    [Algebra S T] [Algebra R T] [IsScalarTower R S T] [Algebra.IsStandardSmooth R S] [Nontrivial T]
    (a b : ℕ)
    (hb : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension b) (algebraMap S T))
    (ha : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension a) (algebraMap R T)) :
    Module.rank S Ω[S⁄R] = ((a - b : ℕ) : Cardinal) ∧ b ≤ a := by
  classical
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal T
  obtain ⟨sb, hsb, hPb⟩ := hb
  obtain ⟨sa, hsa, hPa⟩ := ha
  obtain ⟨t, ht, ht𝔪⟩ : ∃ t ∈ sb, t ∉ 𝔪 := by
    by_contra hcon; push Not at hcon
    exact h𝔪.ne_top (top_le_iff.mp (hsb ▸ Ideal.span_le.mpr hcon))
  obtain ⟨t', ht', ht'𝔪⟩ : ∃ t' ∈ sa, t' ∉ 𝔪 := by
    by_contra hcon; push Not at hcon
    exact h𝔪.ne_top (top_le_iff.mp (hsa ▸ Ideal.span_le.mpr hcon))
  let Tb := Localization.Away t
  let Ta := Localization.Away t'
  let C := Localization.AtPrime 𝔪
  have hTb : Algebra.IsStandardSmoothOfRelativeDimension b S Tb := by
    have := hPb t ht
    rwa [← IsScalarTower.algebraMap_eq (R := S) (S := T) (A := Tb),
      RingHom.isStandardSmoothOfRelativeDimension_algebraMap] at this
  have hTa : Algebra.IsStandardSmoothOfRelativeDimension a R Ta := by
    have := hPa t' ht'
    rwa [← IsScalarTower.algebraMap_eq (R := R) (S := T) (A := Ta),
      RingHom.isStandardSmoothOfRelativeDimension_algebraMap] at this
  have : Algebra.IsStandardSmooth S Tb := hTb.isStandardSmooth
  have : Algebra.IsStandardSmooth R Ta := hTa.isStandardSmooth
  have hCt : IsUnit (algebraMap T C t) := IsLocalization.map_units C (⟨t, ht𝔪⟩ : 𝔪.primeCompl)
  have hCt' : IsUnit (algebraMap T C t') := IsLocalization.map_units C (⟨t', ht'𝔪⟩ : 𝔪.primeCompl)
  let : Algebra Tb C := (IsLocalization.Away.lift t hCt).toAlgebra
  have : IsScalarTower T Tb C := IsScalarTower.of_algebraMap_eq fun x =>
    (IsLocalization.Away.lift_eq t hCt x).symm
  let : Algebra Ta C := (IsLocalization.Away.lift t' hCt').toAlgebra
  have : IsScalarTower T Ta C := IsScalarTower.of_algebraMap_eq fun x =>
    (IsLocalization.Away.lift_eq t' hCt' x).symm
  have : Nontrivial Tb := (algebraMap Tb C).domain_nontrivial
  have : Nontrivial Ta := (algebraMap Ta C).domain_nontrivial
  have hTS : Algebra.Smooth S T := by
    rw [← RingHom.smooth_algebraMap, RingHom.smooth_iff_locally_isStandardSmooth]
    exact RingHom.locally_of_locally
      (fun {R' S' : Type u} [CommRing R'] [CommRing S'] (f : R' →+* S')
        (hf : RingHom.IsStandardSmoothOfRelativeDimension b f) =>
        RingHom.IsStandardSmoothOfRelativeDimension.isStandardSmooth b f hf) ⟨sb, hsb, hPb⟩
  have : Algebra.FormallySmooth S T := hTS.formallySmooth
  have : Algebra.FormallySmooth T C := Algebra.FormallySmooth.of_isLocalization 𝔪.primeCompl
  have : Algebra.FormallySmooth S C := Algebra.FormallySmooth.comp S T C
  have eb : Ω[C⁄S] ≃ₗ[C] C ⊗[Tb] Ω[Tb⁄S] :=
    omegaLocEquiv (R := S) C 𝔪.primeCompl
      ≪≫ₗ (TensorProduct.AlgebraTensorModule.cancelBaseChange T Tb C C Ω[T⁄S]).symm
      ≪≫ₗ TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl C C)
            (omegaLocEquiv (R := S) Tb (Submonoid.powers t)).symm
  have ea : Ω[C⁄R] ≃ₗ[C] C ⊗[Ta] Ω[Ta⁄R] :=
    omegaLocEquiv (R := R) C 𝔪.primeCompl
      ≪≫ₗ (TensorProduct.AlgebraTensorModule.cancelBaseChange T Ta C C Ω[T⁄R]).symm
      ≪≫ₗ TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl C C)
            (omegaLocEquiv (R := R) Ta (Submonoid.powers t')).symm
  have : Module.Free C Ω[C⁄S] := Module.Free.of_equiv eb.symm
  have : Module.Projective C Ω[C⁄S] := Module.Projective.of_free
  obtain ⟨e⟩ := exists_kaehler_equiv_prod R S C
  have hrb : Module.rank C Ω[C⁄S] = b := by
    rw [eb.rank_eq, rank_baseChange_eq C Ω[Tb⁄S]]
    exact Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential b
  have hra : Module.rank C Ω[C⁄R] = a := by
    rw [ea.rank_eq, rank_baseChange_eq C Ω[Ta⁄R]]
    exact Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential a
  have hsum : (a : Cardinal) = Module.rank S Ω[S⁄R] + b := by
    rw [← hra, e.rank_eq, rank_prod', rank_baseChange_eq C Ω[S⁄R], hrb]
  obtain ⟨r, hr⟩ : ∃ r : ℕ, Module.rank S Ω[S⁄R] = r := by
    refine Cardinal.lt_aleph0.mp ?_
    calc Module.rank S Ω[S⁄R] ≤ Module.rank S Ω[S⁄R] + b := self_le_add_right _ _
      _ = a := hsum.symm
      _ < Cardinal.aleph0 := Cardinal.natCast_lt_aleph0 (n := a)
  rw [hr] at hsum ⊢
  norm_cast at hsum
  refine ⟨?_, by omega⟩
  congr 1
  omega

end RelDimSub

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

end SchemeTheory.Smoothness.RelativeDimensionComposition

namespace AlgebraicGeometry

universe u
open CategoryTheory CategoryTheory.Limits NeronModelInfra
open SchemeTheory.Smoothness.RelativeDimensionComposition

theorem SmoothOfRelativeDimension.of_comp_of_smoothOfRelativeDimension_of_surjective
    {X Y Z : Scheme.{u}} [Nonempty X] (f : X ⟶ Y) (g : Y ⟶ Z) (a b : ℕ)
    [SmoothOfRelativeDimension a (f ≫ g)] [SmoothOfRelativeDimension b f]
    [Surjective f] [Smooth g] :
    SmoothOfRelativeDimension (a - b) g ∧ b ≤ a := by
  have key : ∀ (y : Y) (U : Z.Opens) (hU : IsAffineOpen U) (V : Y.Opens) (hV : IsAffineOpen V)
      (hy : y ∈ V) (e : V ≤ g ⁻¹ᵁ U), (g.appLE U V e).hom.IsStandardSmooth →
      (g.appLE U V e).hom.IsStandardSmoothOfRelativeDimension (a - b) ∧ b ≤ a := by
    intro y U hU V hV hy e hstd
    obtain ⟨x, hx⟩ := f.surjective y
    obtain ⟨W, hW, hxW, hWV⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x ∈ f ⁻¹ᵁ V by change f x ∈ V; rwa [hx])
    have hb : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension b)
        (f.appLE V W hWV).hom :=
      HasRingHomProperty.appLE (P := @SmoothOfRelativeDimension b) f inferInstance
        ⟨V, hV⟩ ⟨W, hW⟩ hWV
    have ha : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension a)
        ((f.appLE V W hWV).hom.comp (g.appLE U V e).hom) := by
      rw [← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]
      exact HasRingHomProperty.appLE (P := @SmoothOfRelativeDimension a) (f ≫ g)
        inferInstance ⟨U, hU⟩ ⟨W, hW⟩ _
    have : Nontrivial Γ(X, W) := (X.presheaf.germ W x hxW).hom.domain_nontrivial
    have : Nontrivial Γ(Y, V) := (Y.presheaf.germ V y hy).hom.domain_nontrivial
    let algRS : Algebra Γ(Z, U) Γ(Y, V) := (g.appLE U V e).hom.toAlgebra
    let algST : Algebra Γ(Y, V) Γ(X, W) := (f.appLE V W hWV).hom.toAlgebra
    let algRT : Algebra Γ(Z, U) Γ(X, W) :=
      ((f.appLE V W hWV).hom.comp (g.appLE U V e).hom).toAlgebra
    have : IsScalarTower Γ(Z, U) Γ(Y, V) Γ(X, W) := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have : Algebra.IsStandardSmooth Γ(Z, U) Γ(Y, V) := hstd
    obtain ⟨hr, hle⟩ := RelDimSub.rank_kaehler_eq_sub
      (R := Γ(Z, U)) (S := Γ(Y, V)) (T := Γ(X, W)) a b hb ha
    exact ⟨(Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth
      (a - b)).mpr hr, hle⟩
  obtain ⟨x₀⟩ := ‹Nonempty X›
  refine ⟨⟨fun y => ?_⟩, ?_⟩
  · obtain ⟨U, hU, V, hV, hy, e, hstd⟩ := Smooth.exists_isStandardSmooth g y
    exact ⟨U, hU, V, hV, hy, e, (key y U hU V hV hy e hstd).1⟩
  · obtain ⟨U, hU, V, hV, hy, e, hstd⟩ := Smooth.exists_isStandardSmooth g (f.base x₀)
    exact (key _ U hU V hV hy e hstd).2

end AlgebraicGeometry
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_smoothOfRelativeDimension_of_smooth_of_genericFibre.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.Smoothness.GenericRelativeDimension

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

namespace GenericSpread

open RingHom in
theorem appLE_basicOpen_of_appLE
    {P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    (hPa : StableUnderCompositionWithLocalizationAwayTarget P) (hPl : LocalizationAwayPreserves P)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.affineOpens) (V : X.affineOpens) (e : V.1 ≤ f ⁻¹ᵁ U.1)
    (h : P (f.appLE U V e).hom) (r : Γ(Y, U)) (s : Γ(X, V))
    (e' : X.basicOpen s ≤ f ⁻¹ᵁ Y.basicOpen r) :
    P (f.appLE (Y.basicOpen r) (X.basicOpen s) e').hom := by
  have hle : X.basicOpen s ≤ X.basicOpen (f.appLE U V e r) := by
    rw [Scheme.basicOpen_appLE]
    exact le_inf (X.basicOpen_le s) e'
  have ha : IsAffineOpen (X.basicOpen (f.appLE U V e r)) := V.2.basicOpen _
  set s' := X.presheaf.map (homOfLE (X.basicOpen_le (f.appLE U V e r))).op s with hs'
  have hBss' : X.basicOpen s = X.basicOpen s' := by
    rw [hs', Scheme.basicOpen_res]
    exact (inf_eq_right.mpr hle).symm
  have : IsLocalization.Away (f.appLE U V e r)
      Γ(X, X.basicOpen (f.appLE U V e r)) := V.2.isLocalization_basicOpen _
  have : IsLocalization.Away r Γ(Y, Y.basicOpen r) := U.2.isLocalization_basicOpen r
  have : IsLocalization.Away s' Γ(X, X.basicOpen s') := ha.isLocalization_basicOpen s'
  have heq : f.appLE (Y.basicOpen r) (X.basicOpen s') (hBss' ▸ e') =
      f.appLE (Y.basicOpen r) (X.basicOpen (f.appLE U V e r))
        (by rw [Scheme.basicOpen_appLE]; exact inf_le_right) ≫
        CommRingCat.ofHom (algebraMap _ _) := by
    change _ = _ ≫ X.presheaf.map (homOfLE (X.basicOpen_le s')).op
    exact (f.appLE_map _ _).symm
  rw [f.appLE_congr _ rfl hBss' (fun f => P f.hom), heq]
  apply hPa _ s' _
  rw [U.2.appLE_eq_away_map f V.2]
  exact hPl _ _ _ _ h

theorem bot_mem_of_isOpen {R : Type u} [CommRing R] [IsDomain R] {O : Set (PrimeSpectrum R)}
    (hO : IsOpen O) {p : PrimeSpectrum R} (hp : p ∈ O) :
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∈ O := by
  by_contra hc
  have hcl : p ∈ closure ({⟨⊥, Ideal.isPrime_bot⟩} : Set (PrimeSpectrum R)) :=
    (PrimeSpectrum.le_iff_mem_closure ⟨⊥, Ideal.isPrime_bot⟩ p).mp bot_le
  exact (closure_minimal (Set.singleton_subset_iff.mpr hc) hO.isClosed_compl) hcl hp

end GenericSpread

open GenericSpread

end SchemeTheory.Smoothness.GenericRelativeDimension

namespace AlgebraicGeometry

universe u
open CategoryTheory CategoryTheory.Limits NeronModelInfra
open SchemeTheory.Smoothness.GenericRelativeDimension
open SchemeTheory.Smoothness.GenericRelativeDimension.GenericSpread

theorem smoothOfRelativeDimension_of_smooth_of_genericFibre
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) [Smooth f] (d : ℕ)
    [SmoothOfRelativeDimension d (pullback.snd f (specGenericFibreInclusion R K))] :
    SmoothOfRelativeDimension d f := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have : IsLocalization.Away ϖ K :=
    SchemeTheory.isLocalizationAway_fractionField_of_isDiscreteValuationRing
      R K ϖ hϖ.ne_zero hϖ.not_isUnit
  have : IsOpenImmersion (specGenericFibreInclusion R K) := by
    rw [specGenericFibreInclusion_eq]; exact IsOpenImmersion.of_isLocalization ϖ
  have hι : SmoothOfRelativeDimension 0 (specGenericFibreInclusion R K) := by
    rw [specGenericFibreInclusion_eq,
      HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 0)]
    apply RingHom.locally_of (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := 0))
    change (algebraMap R K).IsStandardSmoothOfRelativeDimension 0
    rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
    exact Algebra.IsStandardSmoothOfRelativeDimension.localization_away ϖ
  have ho : SmoothOfRelativeDimension d (pullback.fst f (specGenericFibreInclusion R K) ≫ f) := by
    rw [pullback.condition]
    exact (inferInstance : SmoothOfRelativeDimension (d + 0)
      (pullback.snd f (specGenericFibreInclusion R K) ≫ specGenericFibreInclusion R K))
  have hopen : IsOpenMap f.base := f.isOpenMap
  have hPa := fun n =>
    (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway
      (n := n)).2
  have hPl := fun n =>
    (RingHom.isStandardSmoothOfRelativeDimension_localizationPreserves (n := n)).away
  refine ⟨fun x => ?_⟩
  obtain ⟨U₂, hU₂, V₂, hV₂, hxV₂, e₂, h₂⟩ := Smooth.exists_isStandardSmooth f x
  obtain ⟨m, hm⟩ :=
    SchemeTheory.Smoothness.LocalRelativeDimension.exists_relativeDimension h₂
  have hη := bot_mem_of_isOpen (hopen _ V₂.isOpen) ⟨x, hxV₂, rfl⟩
  obtain ⟨y, hyV₂, hy⟩ := hη
  have hιpt : f.base y = (specGenericFibreInclusion R K).base ⟨⊥, Ideal.isPrime_bot⟩ := by
    rw [hy]
    apply PrimeSpectrum.ext
    simp only [specGenericFibreInclusion_eq]
    exact (Ideal.comap_bot_of_injective (algebraMap R K) (IsFractionRing.injective R K)).symm
  obtain ⟨y', hy'1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f)
    (g := specGenericFibreInclusion R K) y ⟨⊥, Ideal.isPrime_bot⟩ hιpt
  obtain ⟨U₃, hU₃, V₃, hV₃, hy'V₃, e₃, h₃⟩ :=
    ho.exists_isStandardSmoothOfRelativeDimension y'
  set o := pullback.fst f (specGenericFibreInclusion R K) with hodef
  have : IsOpenImmersion o := by rw [hodef]; infer_instance
  have hW : IsAffineOpen (o ''ᵁ V₃) := hV₃.image_of_isOpenImmersion o
  have hyW : y ∈ o ''ᵁ V₃ := ⟨y', hy'V₃, hy'1⟩
  have eW : o ''ᵁ V₃ ≤ f ⁻¹ᵁ U₃ := by
    rintro _ ⟨v, hv, rfl⟩
    exact e₃ hv
  have h₃' : (f.appLE U₃ (o ''ᵁ V₃) eW).hom.IsStandardSmoothOfRelativeDimension d := by
    have hiso := RingHom.toMorphismProperty_respectsIso_iff.mp
      (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := d))
    have key : RingHom.toMorphismProperty (fun g => g.IsStandardSmoothOfRelativeDimension d)
        (f.appLE U₃ (o ''ᵁ V₃) eW ≫ (o.appIso V₃).hom) := by
      rw [Scheme.Hom.appIso_hom', Scheme.Hom.appLE_comp_appLE]
      exact h₃
    exact (MorphismProperty.cancel_right_of_respectsIso
      (RingHom.toMorphismProperty (fun g => g.IsStandardSmoothOfRelativeDimension d))
      (f.appLE U₃ (o ''ᵁ V₃) eW) (o.appIso V₃).hom).mp key
  obtain ⟨r, s, hys, ers, hd⟩ := exists_basicOpen_le_appLE_of_appLE_of_isAffine (hPa d) (hPl d) y
    ⟨U₂, hU₂⟩ ⟨U₃, hU₃⟩ ⟨V₂, hV₂⟩ ⟨o ''ᵁ V₃, hW⟩ hyV₂ hyW eW h₃' (e₂ hyV₂)
  have hm' : RingHom.IsStandardSmoothOfRelativeDimension m
      (f.appLE (Scheme.basicOpen _ r) (Y.basicOpen s) ers).hom :=
    appLE_basicOpen_of_appLE (hPa m) (hPl m) f ⟨U₂, hU₂⟩ ⟨V₂, hV₂⟩ e₂ hm r s ers
  have : Nontrivial Γ(Y, Y.basicOpen s) :=
    (Y.presheaf.germ (Y.basicOpen s) y hys).hom.domain_nontrivial
  have hmd : m = d := by
    let alg : Algebra Γ(Spec (CommRingCat.of R), Scheme.basicOpen _ r)
        Γ(Y, Y.basicOpen s) :=
      (f.appLE (Scheme.basicOpen _ r) (Y.basicOpen s) ers).hom.toAlgebra
    have h1 := @Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
      _ _ _ _ alg _ m hm'
    have h2 := @Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
      _ _ _ _ alg _ d hd
    exact_mod_cast h1.symm.trans h2
  exact ⟨U₂, hU₂, V₂, hV₂, hxV₂, e₂, hmd ▸ hm⟩

end AlgebraicGeometry
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Smooth_of_comp_of_smooth_of_surjective_of_locallyOfFinitePresentation.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.Smoothness.SmoothDescent

universe u

open TensorProduct

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

end SchemeTheory.Smoothness.SmoothDescent

namespace AlgebraicGeometry

universe u
open CategoryTheory CategoryTheory.Limits NeronModelInfra
open SchemeTheory.Smoothness.SmoothDescent

theorem Smooth.of_comp_of_smooth_of_surjective_of_locallyOfFinitePresentation
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [Smooth f] [Surjective f] [QuasiCompact f]
    [Smooth (f ≫ g)] [LocallyOfFinitePresentation g] : Smooth g := by
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← top_le_iff]
  rintro y -
  obtain ⟨x, rfl⟩ := f.surjective y
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g (f x))) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hyU (U.2.preimage g.continuous)
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ f ⁻¹ᵁ V from hyV)
      (V.2.preimage f.continuous)
  have hWU : W ≤ (f ≫ g) ⁻¹ᵁ U := fun w hw => hVU (hWV hw)
  have hfp := g.finitePresentation_appLE hU hV hVU
  have hsm := f.smooth_appLE hV hW hWV
  let algRS : Algebra Γ(Z, U) Γ(Y, V) := (g.appLE U V hVU).hom.toAlgebra
  let algST : Algebra Γ(Y, V) Γ(X, W) := (f.appLE V W hWV).hom.toAlgebra
  let algRT : Algebra Γ(Z, U) Γ(X, W) := ((f ≫ g).appLE U W hWU).hom.toAlgebra
  have : IsScalarTower Γ(Z, U) Γ(Y, V) Γ(X, W) := IsScalarTower.of_algebraMap_eq fun r => by
    simp only [RingHom.algebraMap_toAlgebra]
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE f g U V W hVU hWV]
  have : Algebra.FinitePresentation Γ(Z, U) Γ(Y, V) := hfp
  have : Algebra.Smooth Γ(Y, V) Γ(X, W) := hsm
  have hx' : Algebra.IsSmoothAt Γ(Z, U) (hW.primeIdealOf ⟨x, hxW⟩).asIdeal := by
    have H : ((f ≫ g).stalkMap x).hom.FormallySmooth :=
      (Scheme.Hom.mem_smoothLocus (f := f ≫ g)).mp (by rw [Scheme.Hom.smoothLocus_eq_top]; trivial)
    exact (formallySmooth_stalkMap_iff U hU W hW hWU hxW).mp H
  rw [Scheme.Hom.mem_smoothLocus, formallySmooth_stalkMap_iff U hU V hV hVU hyV]
  have hunder : (hW.primeIdealOf ⟨x, hxW⟩).asIdeal.under Γ(Y, V) =
      (hV.primeIdealOf ⟨f x, hyV⟩).asIdeal := by
    rw [Ideal.under_def]
    exact congr($(IsAffineOpen.comap_primeIdealOf_appLE V hV W hW hWV hxW).1)
  exact Algebra.IsSmoothAt.of_isSmoothAt_of_smooth Γ(Z, U) Γ(Y, V) Γ(X, W) _ hx' _ hunder

end AlgebraicGeometry
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Smooth_of_comp_of_smooth_of_surjective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.Smoothness.SmoothComposition

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

end SchemeTheory.Smoothness.SmoothComposition

namespace AlgebraicGeometry

universe u
open CategoryTheory CategoryTheory.Limits NeronModelInfra
open SchemeTheory.Smoothness.SmoothComposition

theorem Smooth.of_comp_of_smooth_of_surjective
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [Smooth f] [Surjective f] [QuasiCompact f]
    [Smooth (f ≫ g)] : Smooth g := by
  have : LocallyOfFinitePresentation g :=
    AlgebraicGeometry.LocallyOfFinitePresentation.of_comp_of_flat_of_surjective f g
  exact AlgebraicGeometry.Smooth.of_comp_of_smooth_of_surjective_of_locallyOfFinitePresentation f g

end AlgebraicGeometry
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_SmoothOfRelativeDimension_of_comp_of_surjective_of_field.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.Smoothness.RelativeDimensionOverField

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

end SchemeTheory.Smoothness.RelativeDimensionOverField

namespace AlgebraicGeometry

universe u
open CategoryTheory CategoryTheory.Limits NeronModelInfra
open SchemeTheory.Smoothness.RelativeDimensionOverField

theorem SmoothOfRelativeDimension.of_comp_of_surjective_of_field
    {k : Type u} [Field k] {G Q : Scheme.{u}} [Nonempty G]
    (fQ : Q ⟶ Spec (CommRingCat.of k)) (q : G ⟶ Q)
    (g h : ℕ) [SmoothOfRelativeDimension g (q ≫ fQ)] [SmoothOfRelativeDimension h q] [Surjective q]
    [QuasiCompact q] : SmoothOfRelativeDimension (g - h) fQ ∧ h ≤ g := by
  have : Smooth q := SmoothOfRelativeDimension.smooth h q
  have : Smooth (q ≫ fQ) := SmoothOfRelativeDimension.smooth g (q ≫ fQ)
  have : Smooth fQ := AlgebraicGeometry.Smooth.of_comp_of_smooth_of_surjective q fQ
  exact SmoothOfRelativeDimension.of_comp_of_smoothOfRelativeDimension_of_surjective q fQ g h

end AlgebraicGeometry
end
