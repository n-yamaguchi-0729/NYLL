/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.Data.Int.GCD
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Nyll.AbelianVarieties.Geometry.GroupLaw
public import Nyll.AbelianVarieties.Geometry.PartialActions.Affineness
public import Nyll.AbelianVarieties.Geometry.PartialActions.Basic
public import Nyll.AbelianVarieties.Geometry.PartialActions.StableLocus
public import Nyll.AbelianVarieties.Geometry.Quotients.Action
public import Nyll.AbelianVarieties.Geometry.Quotients.Descent
public import Nyll.AbelianVarieties.Geometry.Subgroups
public import Nyll.AbelianVarieties.Geometry.Torsion.Degree
public import Nyll.AbelianVarieties.Geometry.Torsion.Trace
public import Nyll.AbelianVarieties.NeronModels.Endomorphisms
public import Nyll.SchemeTheory.Etale.Neighborhoods
public import Nyll.SchemeTheory.Descent.FlatMorphisms
public import Nyll.SchemeTheory.LocalGeometry.Points
public import Nyll.AbelianVarieties.Basic
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.EndDegree
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.Kernel
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.GeometricallyConnectedIdentityComponent
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.IrreducibleIdentityComponentIndex
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.Basic
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-!
# Proper subgroups and the affine part of a commutative algebraic group

Lift affine subgroups through a quotient, construct a Rosenlicht complement,
and deduce the proper quotient from a maximal connected affine subgroup.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_isAffine_isClosedImmersion_of_isAffine_of_comp_eq_one_iff.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace GoodReductionJacobian.RelativeGroupLaw

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

open AbelianVarieties.NOSProofs.KernelTorsor

theorem exists_isAffine_isClosedImmersion_of_isAffine_of_comp_eq_one_iff
    (k : Type u) [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f)
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] [IsAffine N] [GeometricallyConnected (i ≫ f)]
    {Q : Scheme.{u}} (fQ : Q ⟶ Spec (CommRingCat.of k)) (LQ : RelativeGroupLaw k fQ)
    (q : SchemeHomOver f fQ) (h : ℕ) [SmoothOfRelativeDimension h q.1] [Surjective q.1]
    [QuasiCompact q.1]
    (hq : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) q =
        LQ.mul t (NeronModelInfra.schemeHomOverComp x q) (NeronModelInfra.schemeHomOverComp y q))
    (hker : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp x q = LQ.one t ↔
        ∃ y : SchemeHomOver t (i ≫ f),
          NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) = x)
    {M : Scheme.{u}} (j : M ⟶ Q) [IsClosedImmersion j] [IsAffine M] [ConnectedSpace M]
    (LM : RelativeGroupLaw k (j ≫ fQ)) (m : ℕ) [SmoothOfRelativeDimension m (j ≫ fQ)]
    (hj : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (j ≫ fQ)),
      NeronModelInfra.schemeHomOverComp (LM.mul t x y) (⟨j, rfl⟩ : SchemeHomOver (j ≫ fQ) fQ) =
        LQ.mul t (NeronModelInfra.schemeHomOverComp x (⟨j, rfl⟩ : SchemeHomOver (j ≫ fQ) fQ))
          (NeronModelInfra.schemeHomOverComp y (⟨j, rfl⟩ : SchemeHomOver (j ≫ fQ) fQ))) :
    ∃ (P : Scheme.{u}) (ι : P ⟶ G) (LP : RelativeGroupLaw k (ι ≫ f)),
      IsClosedImmersion ι ∧ IsAffine P ∧ ConnectedSpace P ∧
      SmoothOfRelativeDimension (h + m) (ι ≫ f) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (ι ≫ f)),
        NeronModelInfra.schemeHomOverComp (LP.mul t x y) (⟨ι, rfl⟩ : SchemeHomOver (ι ≫ f) f) =
          L.mul t (NeronModelInfra.schemeHomOverComp x (⟨ι, rfl⟩ : SchemeHomOver (ι ≫ f) f))
            (NeronModelInfra.schemeHomOverComp y (⟨ι, rfl⟩ : SchemeHomOver (ι ≫ f) f))) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
        (∃ y : SchemeHomOver t (ι ≫ f),
            NeronModelInfra.schemeHomOverComp y (⟨ι, rfl⟩ : SchemeHomOver (ι ≫ f) f) = x) ↔
          ∃ z : SchemeHomOver t (j ≫ fQ),
            NeronModelInfra.schemeHomOverComp z (⟨j, rfl⟩ : SchemeHomOver (j ≫ fQ) fQ) =
              NeronModelInfra.schemeHomOverComp x q) := by
  classical
  let P : Scheme.{u} := pullback q.1 j
  let ι : P ⟶ G := pullback.fst q.1 j
  let π : P ⟶ M := pullback.snd q.1 j
  have hιf : ι ≫ f = π ≫ j ≫ fQ := by
    change pullback.fst q.1 j ≫ f = pullback.snd q.1 j ≫ j ≫ fQ
    calc pullback.fst q.1 j ≫ f = (pullback.fst q.1 j ≫ q.1) ≫ fQ := by rw [Category.assoc, q.2]
      _ = (pullback.snd q.1 j ≫ j) ≫ fQ := by rw [pullback.condition]
      _ = pullback.snd q.1 j ≫ j ≫ fQ := by rw [Category.assoc]
  have : Flat q.1 := by
    have : Smooth q.1 := SmoothOfRelativeDimension.smooth h q.1
    infer_instance
  have hqaff : IsAffineHom q.1 := by
    have : MorphismProperty.DescendsAlong (@IsAffineHom : MorphismProperty Scheme.{u})
        (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
      AlgebraicGeometry.IsAffineHom.descendsAlong_surjective_inf_flat_inf_quasiCompact
    obtain ⟨e, he⟩ :=
      exists_pullback_iso_pullback_of_comp_eq_one_iff k f L i fQ LQ q hq hker
    have : IsAffineHom (pullback.snd (i ≫ f) f) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := (@IsAffineHom : MorphismProperty Scheme.{u}))
        (IsPullback.of_hasPullback (i ≫ f) f) inferInstance
    have hsnd : IsAffineHom (pullback.snd q.1 q.1) := by
      rw [← he]; infer_instance
    exact MorphismProperty.of_pullback_snd_of_descendsAlong (P := @IsAffineHom)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (f := q.1) (g := q.1)
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hsnd
  have : IsAffineHom π :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (@IsAffineHom : MorphismProperty Scheme.{u}))
      (IsPullback.of_hasPullback q.1 j) hqaff
  have hPaff : IsAffine P := isAffine_of_isAffineHom π
  let toG : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}, SchemeHomOver t (ι ≫ f) →
      SchemeHomOver t f :=
    fun a => NeronModelInfra.schemeHomOverComp a (⟨ι, rfl⟩ : SchemeHomOver (ι ≫ f) f)
  let toM : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}, SchemeHomOver t (ι ≫ f) →
      SchemeHomOver t (j ≫ fQ) :=
    fun a => ⟨a.1 ≫ π, by rw [Category.assoc, ← hιf, ← Category.assoc]; exact a.2⟩
  have hGM : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (a : SchemeHomOver t (ι ≫ f)),
      NeronModelInfra.schemeHomOverComp (toG a) q =
        NeronModelInfra.schemeHomOverComp (toM a) (⟨j, rfl⟩ : SchemeHomOver (j ≫ fQ) fQ) := by
    intro T t a
    apply Subtype.ext
    change (a.1 ≫ ι) ≫ q.1 = (a.1 ≫ π) ≫ j
    rw [Category.assoc, Category.assoc, pullback.condition]
  let mkP : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x : SchemeHomOver t f) (z :
      SchemeHomOver t (j ≫ fQ)),
      NeronModelInfra.schemeHomOverComp x q = NeronModelInfra.schemeHomOverComp z (⟨j, rfl⟩ :
          SchemeHomOver (j ≫ fQ) fQ) →
      SchemeHomOver t (ι ≫ f) :=
    fun x z hxz => ⟨pullback.lift x.1 z.1 (congrArg Subtype.val hxz), by
      rw [← Category.assoc]; erw [pullback.lift_fst]; exact x.2⟩
  have toG_mkP : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x : SchemeHomOver t f) (z :
      SchemeHomOver t (j ≫ fQ))
      (hxz : NeronModelInfra.schemeHomOverComp x q = NeronModelInfra.schemeHomOverComp z (⟨j, rfl⟩ :
          SchemeHomOver (j ≫ fQ) fQ)),
      toG (mkP x z hxz) = x := fun x z hxz => Subtype.ext (pullback.lift_fst _ _ _)
  have toM_mkP : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x : SchemeHomOver t f) (z :
      SchemeHomOver t (j ≫ fQ))
      (hxz : NeronModelInfra.schemeHomOverComp x q = NeronModelInfra.schemeHomOverComp z (⟨j, rfl⟩ :
          SchemeHomOver (j ≫ fQ) fQ)),
      toM (mkP x z hxz) = z := fun x z hxz => Subtype.ext (pullback.lift_snd _ _ _)
  have toG_inj : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (a b : SchemeHomOver t (ι ≫
      f)),
      toG a = toG b → a = b := fun a b hab =>
    Subtype.ext ((cancel_mono ι).mp (congrArg Subtype.val hab))
  have toG_comp : ∀ {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (t' : T' ⟶ Spec
      (CommRingCat.of k))
      (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (c : SchemeHomOver t (ι ≫ f)),
      toG (GoodReductionJacobian.schemeHomOverComp ψ hψ c) = GoodReductionJacobian.schemeHomOverComp
          ψ hψ (toG c) :=
    fun t t' ψ hψ c => Subtype.ext (Category.assoc _ _ _)
  let LP : RelativeGroupLaw k (ι ≫ f) :=
    { mul := fun t a b => mkP (L.mul t (toG a) (toG b)) (LM.mul t (toM a) (toM b))
        (by rw [hq, hj, hGM, hGM])
      one := fun t => mkP (L.one t) (LM.one t)
        (by rw [Torsor.map_one L LQ q hq, Torsor.map_one LM LQ ⟨j, rfl⟩ hj])
      inv := fun t a => mkP (L.inv t (toG a)) (LM.inv t (toM a))
        (by rw [Torsor.map_inv L LQ q hq, Torsor.map_inv LM LQ ⟨j, rfl⟩ hj, hGM])
      mul_assoc := fun t a b c => toG_inj _ _ (by simp only [toG_mkP]; rw [L.mul_assoc])
      one_mul := fun t a => toG_inj _ _ (by simp only [toG_mkP]; rw [L.one_mul])
      mul_one := fun t a => toG_inj _ _ (by simp only [toG_mkP]; rw [L.mul_one])
      inv_mul_cancel := fun t a => toG_inj _ _ (by simp only [toG_mkP]; rw [L.inv_mul_cancel])
      mul_natural := fun t t' ψ hψ a b => toG_inj _ _ (by
        rw [toG_comp]
        simp only [toG_mkP]
        rw [L.mul_natural, toG_comp, toG_comp]) }
  refine ⟨P, ι, LP, inferInstance, hPaff, ?_, ?_, ?_, ?_⟩
  · exact GoodReductionJacobian.RelativeGroupLaw.connectedSpace_pullback_of_comp_eq_one_iff k f L i
      fQ LQ q hq hker h j
  · have : MorphismProperty.IsStableUnderBaseChange
        (@SmoothOfRelativeDimension h : MorphismProperty Scheme.{u}) :=
      smoothOfRelativeDimension_isStableUnderBaseChange h
    have : SmoothOfRelativeDimension h π :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := (@SmoothOfRelativeDimension h : MorphismProperty Scheme.{u}))
        (IsPullback.of_hasPullback q.1 j) inferInstance
    rw [hιf]; infer_instance
  · intro T t a b
    exact toG_mkP (L.mul t (toG a) (toG b)) (LM.mul t (toM a) (toM b)) (by rw [hq, hj, hGM, hGM])
  · intro T t x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨toM a, (hGM a).symm⟩
    · rintro ⟨z, hz⟩
      exact ⟨mkP x z hz.symm, toG_mkP x z hz.symm⟩

end GoodReductionJacobian.RelativeGroupLaw
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_isAffine_or_exists_isClosedImmersion_lt_of_not_isProper.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace GoodReductionJacobian.RelativeGroupLaw

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem isAffine_or_exists_isClosedImmersion_lt_of_not_isProper
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G]
    (L : RelativeGroupLaw k f) (g : ℕ) [SmoothOfRelativeDimension g f]
    (hG : ¬ IsProper f) :
    IsAffine G ∨
    ∃ (H : Scheme.{u}) (i : H ⟶ G) (LH : RelativeGroupLaw k (i ≫ f)) (h : ℕ),
      IsClosedImmersion i ∧ ConnectedSpace H ∧ SmoothOfRelativeDimension h (i ≫ f) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
        NeronModelInfra.schemeHomOverComp (LH.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
          L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
            (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))) ∧
      1 ≤ h ∧ h < g := by
  have : Smooth f := SmoothOfRelativeDimension.smooth g f
  obtain ⟨V, hVne, P, p, hPs, hPl, hPi, ι, hιo, hι, a, hc, hu, ha, W, hW, hst, hWg, P₀, hP₀, he⟩ :=
    GoodReductionJacobian.PartialAction.exists_compatible_stable_defined_one_of_not_isProper k f L g
        hG
  have : Nonempty (V : Scheme.{u}) := hVne
  have : IsSeparated p := hPs
  have : LocallyOfFiniteType p := hPl
  have : IsIntegral P := hPi
  have : IsOpenImmersion ι := hιo
  by_cases hmov : ∃ (γ₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) (hγ₀ : a.Defined γ₀ P₀),
      a.act γ₀ P₀ hγ₀ ≠ P₀
  · obtain ⟨γ₀, hγ₀, hne⟩ := hmov
    obtain ⟨H, i, LH, hi, hhom, hrange, hdim⟩ :=
      GoodReductionJacobian.PartialAction.exists_isClosedImmersion_range_ne_univ_of_act_ne k f L g p
          a hu ha W hW hWg hst
        P₀ hP₀ he γ₀ hγ₀ hne
    have : IsClosedImmersion i := hi
    exact Or.inr (exists_isClosedImmersion_connectedSpace_lt_of_range_ne_univ
      k f L g i LH hhom hrange hdim)
  · push Not at hmov
    refine Or.inl (GoodReductionJacobian.PartialAction.isAffine_of_forall_exists_defined_act_eq k f
        L p V ι hι a hc
      hu ha P₀ (fun t γ => ?_))
    exact GoodReductionJacobian.PartialAction.exists_defined_act_eq_of_forall_act_eq k f L p a ha P₀
        he
      (fun γ hd => hmov γ hd) t γ

end GoodReductionJacobian.RelativeGroupLaw
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_surjective_mul_of_isProper_of_isCommutative.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.RosenlichtDecomposition

noncomputable section

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian

universe u

namespace TorsionCounts

theorem natCard_torsion_eq_of_surjective {A B : Type*} [CommGroup A] [CommGroup B] (φ : A →* B)
    (hsurj : Function.Surjective φ) (n ℓ : ℕ) (hcop : ℓ.Coprime n)
    (hker : ∀ a, φ a = 1 → a ^ n = 1) :
    Nat.card {a : A // a ^ ℓ = 1} = Nat.card {b : B // b ^ ℓ = 1} := by
  apply Nat.card_eq_of_bijective (fun a => ⟨φ a.1, by rw [← map_pow, a.2, map_one]⟩)
  constructor
  · rintro ⟨a, ha⟩ ⟨a', ha'⟩ h
    simp only [Subtype.mk.injEq] at h ⊢
    have h1 : φ (a * a'⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
    have h2 : (a * a'⁻¹) ^ n = 1 := hker _ h1
    have h3 : (a * a'⁻¹) ^ ℓ = 1 := by rw [mul_pow, inv_pow, ha, ha', mul_inv_cancel]
    have h4 : (a * a'⁻¹) ^ (Nat.gcd ℓ n) = 1 := pow_gcd_eq_one.mpr ⟨h3, h2⟩
    rw [hcop, pow_one] at h4
    exact mul_inv_eq_one.mp h4
  · rintro ⟨y, hy⟩
    obtain ⟨a₁, rfl⟩ := hsurj y
    have h1 : (a₁ ^ ℓ) ^ n = 1 := hker _ (by rw [map_pow, hy])
    obtain ⟨α, β, hαβ⟩ : IsCoprime (ℓ : ℤ) (n : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
    refine ⟨⟨a₁ ^ (β * n), ?_⟩, ?_⟩
    · rw [← zpow_natCast, ← zpow_mul]
      have e : β * (n : ℤ) * (ℓ : ℤ) = ((ℓ * n : ℕ) : ℤ) * β := by push_cast; ring
      rw [e, zpow_mul, zpow_natCast, pow_mul, h1, one_zpow]
    · apply Subtype.ext
      simp only [map_zpow]
      have e : β * (n : ℤ) = 1 - (ℓ : ℤ) * α := by linarith
      rw [e, zpow_sub, zpow_one, zpow_mul, zpow_natCast, hy, one_zpow, inv_one, mul_one]

theorem exists_two_le_coprime_cast_ne_zero (k : Type u) [Field k] (n : ℕ) (hn : 0 < n) :
    ∃ ℓ : ℕ, 2 ≤ ℓ ∧ ℓ.Coprime n ∧ (ℓ : k) ≠ 0 := by
  let p := ringChar k
  refine ⟨n * max p 1 + 1, ?_, ?_, ?_⟩
  · have : 1 ≤ n * max p 1 := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hn.ne' (by omega))
    omega
  · rw [Nat.coprime_mul_left_add_left]
    exact Nat.coprime_one_left n
  · intro h
    rw [CharP.cast_eq_zero_iff k p] at h
    rcases CharP.char_is_prime_or_zero k p with hp | hp
    · have h2 : p ∣ n * max p 1 := Dvd.dvd.mul_left (by rw [max_eq_left hp.one_lt.le]) n
      have h3 : p ∣ 1 := (Nat.dvd_add_right h2).mp h
      exact hp.one_lt.ne' (Nat.dvd_one.mp h3)
    · rw [hp, zero_dvd_iff] at h
      omega

end TorsionCounts

namespace Decomposition
open _root_.GoodReductionJacobian.RelativeGroupLaw hiding fibre IsHom
open _root_.GoodReductionJacobian

open AbelianVarieties.NOSProofs.RosenlichtRetractions.RetractionConstruction
  (comp_eq_transition comp_lawMul comp_lawOne comp_lawNsmul comp_lawInv
   IsHom eq_of_comp_mono_eq isCommutative_of_isHom_mono
   castLaw castLaw_mul_val castLaw_isCommutative castLaw_isHom
   idPt constPt constPt_coe comp_constPt constPt_id comp_idPt)
open AbelianVarieties.NOSProofs.GaloisTorsorTrace.TorsorConstruction (nsmul_eq_pow)

section Kernel

variable {k : Type u} [Field k] {G A : Scheme.{u}}
  {f : G ⟶ Spec (CommRingCat.of k)} {fA : A ⟶ Spec (CommRingCat.of k)}

/-- The kernel scheme of a homomorphism of relative groups. -/
abbrev kerScheme (LA : RelativeGroupLaw k fA) (π : SchemeHomOver f fA) : Scheme.{u} :=
  pullback π.1 (LA.one (𝟙 (Spec (CommRingCat.of k)))).1

/-- The structural morphism of the kernel scheme. -/
abbrev kerStr (LA : RelativeGroupLaw k fA) (π : SchemeHomOver f fA) :
    kerScheme LA π ⟶ Spec (CommRingCat.of k) :=
  pullback.snd π.1 (LA.one (𝟙 (Spec (CommRingCat.of k)))).1

theorem kerι_comp (LA : RelativeGroupLaw k fA) (π : SchemeHomOver f fA) :
    pullback.fst π.1 (LA.one (𝟙 (Spec (CommRingCat.of k)))).1 ≫ f = kerStr LA π := by
  have h1 : pullback.fst π.1 (LA.one (𝟙 (Spec (CommRingCat.of k)))).1 ≫ f =
      pullback.fst π.1 (LA.one (𝟙 (Spec (CommRingCat.of k)))).1 ≫ π.1 ≫ fA := by rw [π.2]
  rw [h1, pullback.condition_assoc, (LA.one (𝟙 (Spec (CommRingCat.of k)))).2, Category.comp_id]

/-- The kernel inclusion as a relative point. -/
def kerIncl (LA : RelativeGroupLaw k fA) (π : SchemeHomOver f fA) : SchemeHomOver (kerStr LA π) f :=
  ⟨pullback.fst π.1 (LA.one (𝟙 (Spec (CommRingCat.of k)))).1, kerι_comp LA π⟩

@[scoped simp]
theorem kerIncl_coe (LA : RelativeGroupLaw k fA) (π : SchemeHomOver f fA) :
    (kerIncl LA π).1 = pullback.fst π.1 (LA.one (𝟙 (Spec (CommRingCat.of k)))).1 :=
  rfl

scoped instance (LA : RelativeGroupLaw k fA) : IsClosedImmersion (LA.one (𝟙 (Spec (CommRingCat.of
    k)))).1 :=
  isClosedImmersion_of_comp_eq_id fA _ (LA.one (𝟙 (Spec (CommRingCat.of k)))).2

scoped instance (LA : RelativeGroupLaw k fA) (π : SchemeHomOver f fA) : IsClosedImmersion (kerIncl
    LA π).1 := by
  rw [kerIncl_coe]; infer_instance

theorem exists_kerLaw (L : RelativeGroupLaw k f) (LA : RelativeGroupLaw k fA) (π : SchemeHomOver f
    fA)
    (hπ : IsHom L LA π) :
    ∃ L₀ : RelativeGroupLaw k (kerStr LA π),
      IsHom L₀ L (kerIncl LA π) ∧ (L.IsCommutative → L₀.IsCommutative) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (y : SchemeHomOver t (kerStr LA π)),
        NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp y (kerIncl LA π)) π =
          LA.one t) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
        NeronModelInfra.schemeHomOverComp x π = LA.one t →
          ∃ y : SchemeHomOver t (kerStr LA π), NeronModelInfra.schemeHomOverComp y (kerIncl LA π) =
              x) := by
  obtain ⟨e, he⟩ :=
    exists_schemeHomOver_pullback_unit_equiv_ker LA π
  have he' : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (y : SchemeHomOver t (kerStr LA
      π)),
      ((e t y : {x : SchemeHomOver t f // _}) : SchemeHomOver t f) =
        NeronModelInfra.schemeHomOverComp y (kerIncl LA π) :=
    fun t y => Subtype.ext (he t y)
  have hnat : ∀ {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
      (t' : T' ⟶ Spec (CommRingCat.of k)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
      (y : SchemeHomOver t (kerStr LA π)),
      ((e t' (GoodReductionJacobian.schemeHomOverComp ψ hψ y) : {x : SchemeHomOver t' f // _}) :
          SchemeHomOver t' f) =
        GoodReductionJacobian.schemeHomOverComp ψ hψ ((e t y : {x : SchemeHomOver t f // _}) :
          SchemeHomOver t f) := by
    intro T T' t t' ψ hψ y
    rw [he', he']
    apply Subtype.ext
    simp only [NeronModelInfra.schemeHomOverComp_coe, GoodReductionJacobian.schemeHomOverComp_coe,
      Category.assoc]
  let L₀ : RelativeGroupLaw k (kerStr LA π) :=
    { mul := fun t y y' => (e t).symm ⟨L.mul t (e t y).1 (e t y').1, by
          rw [hπ, (e t y).2, (e t y').2, LA.one_mul]⟩
      one := fun t => (e t).symm ⟨L.one t, hπ.one t⟩
      inv := fun t y => (e t).symm ⟨L.inv t (e t y).1, by
          let : Group (SchemeHomOver t fA) := LA.pointGroup t
          rw [hπ.inv, (e t y).2]
          exact inv_one⟩
      mul_assoc := fun t x y z => by
        apply (e t).injective
        apply Subtype.ext
        simp only [Equiv.apply_symm_apply]
        exact L.mul_assoc t _ _ _
      one_mul := fun t x => by
        apply (e t).injective
        apply Subtype.ext
        simp only [Equiv.apply_symm_apply]
        exact L.one_mul t _
      mul_one := fun t x => by
        apply (e t).injective
        apply Subtype.ext
        simp only [Equiv.apply_symm_apply]
        exact L.mul_one t _
      inv_mul_cancel := fun t x => by
        apply (e t).injective
        apply Subtype.ext
        simp only [Equiv.apply_symm_apply]
        exact L.inv_mul_cancel t _
      mul_natural := fun t t' ψ hψ x y => by
        apply (e t').injective
        apply Subtype.ext
        rw [hnat]
        simp only [Equiv.apply_symm_apply]
        rw [L.mul_natural t t' ψ hψ, ← hnat t t' ψ hψ x, ← hnat t t' ψ hψ y] }
  refine ⟨L₀, ?_, ?_, ?_, ?_⟩
  · intro T t y y'
    rw [← he', ← he', ← he']
    change ((e t ((e t).symm _) : {x : SchemeHomOver t f // _}) : SchemeHomOver t f) = _
    rw [Equiv.apply_symm_apply]
  · intro hc T t y y'
    apply (e t).injective
    apply Subtype.ext
    change ((e t ((e t).symm _) : {x : SchemeHomOver t f // _}) : SchemeHomOver t f) =
      ((e t ((e t).symm _) : {x : SchemeHomOver t f // _}) : SchemeHomOver t f)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact hc t _ _
  · intro T t y
    rw [← he']
    exact (e t y).2
  · intro T t x hx
    exact ⟨(e t).symm ⟨x, hx⟩, by rw [← he', Equiv.apply_symm_apply]⟩

end Kernel

section Translate

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}

/-- Translation by a rational point of the relative group. -/
def translate (L : RelativeGroupLaw k f) (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    SchemeHomOver f f :=
  L.mul f (idPt f) (constPt f s)

theorem comp_translate (L : RelativeGroupLaw k f) (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of k)))
    f)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x : SchemeHomOver t f) :
    NeronModelInfra.schemeHomOverComp x (translate L s) = L.mul t x (constPt t s) := by
  rw [translate, comp_lawMul, comp_idPt, comp_constPt]

theorem translate_comp_translate_inv (L : RelativeGroupLaw k f)
    (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    (translate L s).1 ≫ (translate L (L.inv _ s)).1 = 𝟙 G := by
  have key : constPt f (L.inv _ s) = L.inv f (constPt f s) :=
    L.inv_natural (𝟙 (Spec (CommRingCat.of k))) f f (Category.comp_id f) s
  have h : NeronModelInfra.schemeHomOverComp (translate L s) (translate L (L.inv _ s)) = idPt f
      := by
    rw [comp_translate, translate, L.mul_assoc, key, L.mul_inv_cancel, L.mul_one]
  exact congrArg Subtype.val h

/-- The underlying geometric point of a rational section. -/
abbrev pt (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) : G :=
  x.1.base (IsLocalRing.closedPoint k)

theorem pt_comp {H : Scheme.{u}} {fH : H ⟶ Spec (CommRingCat.of k)}
    (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) (φ : SchemeHomOver f fH) :
    pt (NeronModelInfra.schemeHomOverComp x φ) = φ.1.base (pt x) := by
  exact Scheme.Hom.comp_apply x.1 φ.1
    (show Spec (CommRingCat.of k) from IsLocalRing.closedPoint k)

theorem isClosed_pt [IsAlgClosed k] [LocallyOfFiniteType f]
    (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) : IsClosed ({pt x} : Set G) :=
  ((pointEquivClosedPoint f) x).2

theorem eq_of_pt_eq [IsAlgClosed k] [LocallyOfFiniteType f]
    {x y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f} (h : pt x = pt y) : x = y :=
  (pointEquivClosedPoint f).injective (Subtype.ext h)

theorem exists_pt_eq [IsAlgClosed k] [LocallyOfFiniteType f] {z : G} (hz : IsClosed ({z} : Set G)) :
    ∃ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f, pt x = z :=
  ⟨(pointEquivClosedPoint f).symm ⟨z, hz⟩, by
    have := (pointEquivClosedPoint f).apply_symm_apply ⟨z, hz⟩
    exact congrArg Subtype.val this⟩

end Translate

section Main

variable (k : Type u) [Field k] [IsAlgClosed k]

theorem exists_complement {G : Scheme.{u}}
    (f : G ⟶ Spec (CommRingCat.of k)) [IsSeparated f] [QuasiCompact f] [ConnectedSpace G]
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (g : ℕ) [SmoothOfRelativeDimension g f]
    {A : Scheme.{u}} (j : A ⟶ G) [IsClosedImmersion j] [ConnectedSpace A] [IsProper (j ≫ f)]
    (LA : RelativeGroupLaw k (j ≫ f)) (a : ℕ) [SmoothOfRelativeDimension a (j ≫ f)]
    (hj : IsHom LA L ⟨j, rfl⟩) (n : ℕ) (hn : 0 < n) (π : SchemeHomOver f (j ≫ f)) (hπ : IsHom L LA
        π)
    (hπj : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t (j ≫ f)),
      NeronModelInfra.schemeHomOverComp
        (NeronModelInfra.schemeHomOverComp x (⟨j, rfl⟩ : SchemeHomOver (j ≫ f) f)) π = LA.nsmul t n
            x) :
    ∃ (N : Scheme.{u}) (i : N ⟶ G) (LN : RelativeGroupLaw k (i ≫ f)),
      IsClosedImmersion i ∧ ConnectedSpace N ∧ SmoothOfRelativeDimension (g - a) (i ≫ f) ∧
      a ≤ g ∧ IsHom LN L ⟨i, rfl⟩ ∧
      Surjective
        (L.mul (pullback.fst (j ≫ f) (i ≫ f) ≫ j ≫ f)
          ⟨pullback.fst (j ≫ f) (i ≫ f) ≫ j, Category.assoc _ _ _⟩
          ⟨pullback.snd (j ≫ f) (i ≫ f) ≫ i,
            (Category.assoc _ _ _).trans pullback.condition.symm⟩).1 := by
  classical
  have : Smooth f := SmoothOfRelativeDimension.smooth g f
  have : Smooth (j ≫ f) := SmoothOfRelativeDimension.smooth a (j ≫ f)
  have hAc : LA.IsCommutative := isCommutative_of_isHom_mono hc ⟨j, rfl⟩ hj
  set jG : SchemeHomOver (j ≫ f) f := ⟨j, rfl⟩ with hjG
  obtain ⟨L₀, h0hom, h0comm, h0ker, h0lift⟩ := exists_kerLaw L LA π hπ
  set ι₀ : SchemeHomOver (kerStr LA π) f := kerIncl LA π with hι₀
  have hf₀ : ι₀.1 ≫ f = kerStr LA π := ι₀.2
  have : LocallyOfFiniteType (kerStr LA π) := by rw [← hf₀]; infer_instance
  have : QuasiCompact (kerStr LA π) := by rw [← hf₀]; infer_instance
  obtain ⟨N, i₁, L₁, h, hci₁, hirr, hsm₁, -, -, -, -, hhom₁, -, S, hSfin, hcov⟩ :=
    exists_isClosedImmersion_smoothOfRelativeDimension_range_eq_connectedComponent_of_perfectField
      k L₀
  have : IsClosedImmersion i₁ := hci₁
  have : IrreducibleSpace N := hirr
  set i : N ⟶ G := i₁ ≫ ι₀.1 with hi
  have ei : i₁ ≫ kerStr LA π = i ≫ f := by rw [hi, Category.assoc, hf₀]
  set LN : RelativeGroupLaw k (i ≫ f) := castLaw ei L₁ with hLN
  have h1hom : IsHom L₁ L₀ ⟨i₁, rfl⟩ := hhom₁
  have hLNhom : IsHom LN L ⟨i, rfl⟩ :=
    castLaw_isHom ei L₁ L (NeronModelInfra.schemeHomOverComp ⟨i₁, rfl⟩ ι₀) (h1hom.comp h0hom)
  have : IsClosedImmersion i := by rw [hi]; infer_instance
  have hsmN : SmoothOfRelativeDimension h (i ≫ f) := by rw [← ei]; exact hsm₁
  have hNker : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp y ⟨i, rfl⟩) π =
        LA.one t := by
    intro T t y
    have : NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        NeronModelInfra.schemeHomOverComp
          (NeronModelInfra.schemeHomOverComp (⟨y.1, by rw [ei]; exact y.2⟩ : SchemeHomOver t (i₁ ≫
              kerStr LA π))
            (⟨i₁, rfl⟩ : SchemeHomOver (i₁ ≫ kerStr LA π) (kerStr LA π))) ι₀ := by
      apply Subtype.ext
      simp only [NeronModelInfra.schemeHomOverComp_coe, Category.assoc, hi]
    rw [this, h0ker]
  have hnormal : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f)
      (m : SchemeHomOver t (i ≫ f)), ∃ m' : SchemeHomOver t (i ≫ f),
        NeronModelInfra.schemeHomOverComp m' (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
          L.mul t (L.mul t x (NeronModelInfra.schemeHomOverComp m (⟨i, rfl⟩ : SchemeHomOver (i ≫ f)
              f)))
            (L.inv t x) := by
    intro T t x m
    refine ⟨m, ?_⟩
    let : CommGroup (SchemeHomOver t f) := L.pointCommGroup hc t
    change _ = x * _ * x⁻¹
    rw [mul_right_comm, _root_.mul_inv_cancel, _root_.one_mul]
  obtain ⟨Q, fQ, LQ, q, hQsep, hQqc, hQsm, hhg, hqsm, hqsurj, hqhom, hQcomm, hqker⟩ :=
    exists_quotient_smoothOfRelativeDimension_sub_of_isClosedImmersion_of_isAlgClosed
      k f L g i LN h hLNhom hnormal
  have : IsSeparated fQ := hQsep
  have : QuasiCompact fQ := hQqc
  have : SmoothOfRelativeDimension (g - h) fQ := hQsm
  have : Surjective q.1 := hqsurj
  have : Smooth fQ := SmoothOfRelativeDimension.smooth (g - h) fQ
  have : Smooth q.1 := SmoothOfRelativeDimension.smooth h q.1
  have hqH : IsHom L LQ q := hqhom
  set u : A ⟶ Q := j ≫ q.1 with hu_def
  have hu : u ≫ fQ = j ≫ f := by rw [hu_def, Category.assoc, q.2]
  have : IsProper (u ≫ fQ) := by rw [hu]; infer_instance
  have : IsProper u := IsProper.of_comp u fQ
  have hCA : IsClosed (Set.range u.base) := u.isClosedMap.isClosed_range
  have hAab : AbelianSchemePropertyBundle k (j ≫ f) :=
    ⟨inferInstance, inferInstance, fun s => by
      have : (j ≫ f).base ⁻¹' {s} = Set.univ :=
        Set.eq_univ_of_forall fun _w => Subsingleton.elim _ _
      rw [this]; exact isConnected_univ, ⟨LA⟩⟩
  have hnsurj : Function.Surjective (LA.schemeNsmul n) :=
    (isFinite_schemeKerStr_and_finrank_eq_pow_and_finrank_schemeNsmul_eq_pow
      k (j ≫ f) LA hAc hAab a n hn.ne').2.2.2.2.1
  have : Surjective (LA.schemeNsmul n) := ⟨hnsurj⟩
  have : LocallyOfFiniteType (LA.schemeNsmul n) := by
    have e : LA.schemeNsmul n ≫ (j ≫ f) = j ≫ f := LA.schemeNsmul_over n
    have : LocallyOfFiniteType (LA.schemeNsmul n ≫ j ≫ f) := by rw [e]; infer_instance
    exact locallyOfFiniteType_of_comp _ (j ≫ f)
  have hdec₀ : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
      ∃ s ∈ S, ∃ (a' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (j ≫ f))
        (y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (i ≫ f)),
        let : CommGroup (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) := L.pointCommGroup hc (𝟙
            (Spec (CommRingCat.of k)))
        x * (NeronModelInfra.schemeHomOverComp s ι₀)⁻¹ =
          NeronModelInfra.schemeHomOverComp a' jG * NeronModelInfra.schemeHomOverComp y ⟨i, rfl⟩
              := by
    intro x
    let : CommGroup (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) := L.pointCommGroup hc (𝟙 (Spec
        (CommRingCat.of k)))
    let : CommGroup (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (j ≫ f)) := LA.pointCommGroup hAc
        (𝟙 (Spec (CommRingCat.of k)))
    obtain ⟨a₀, ha₀⟩ :=
      AlgebraicGeometry.exists_comp_eq_of_surjective_of_locallyOfFiniteType_of_isAlgClosed
        (LA.schemeNsmul n) (NeronModelInfra.schemeHomOverComp x π).1
    let a' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (j ≫ f) :=
      ⟨a₀, by rw [← LA.schemeNsmul_over n, ← Category.assoc, ha₀]; exact
          (NeronModelInfra.schemeHomOverComp x π).2⟩
    have ha' : LA.nsmul _ n a' = NeronModelInfra.schemeHomOverComp x π := by
      have := comp_lawNsmul LA a' n (idPt (j ≫ f))
      rw [comp_idPt] at this
      rw [← this]
      exact Subtype.ext ha₀
    have hk : NeronModelInfra.schemeHomOverComp (x * (NeronModelInfra.schemeHomOverComp a' jG)⁻¹) π
        =
        LA.one _ := by
      change NeronModelInfra.schemeHomOverComp
        (L.mul _ x (L.inv _ (NeronModelInfra.schemeHomOverComp a' jG))) π = _
      rw [hπ, hπ.inv]
      change NeronModelInfra.schemeHomOverComp x π *
        (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp a' jG) π)⁻¹ = 1
      rw [hπj, ha', _root_.mul_inv_cancel]
    obtain ⟨y₁, hy₁⟩ := h0lift _ _ hk
    obtain ⟨s, hs, y, hy⟩ := hcov y₁
    refine ⟨s, hs, a', ⟨y.1, by rw [← ei]; exact y.2⟩, ?_⟩
    have hy' : NeronModelInfra.schemeHomOverComp y₁ ι₀ =
        NeronModelInfra.schemeHomOverComp s ι₀ *
          NeronModelInfra.schemeHomOverComp ⟨y.1, by rw [← ei]; exact y.2⟩ ⟨i, rfl⟩ := by
      rw [hy, h0hom]
      congr 1
    rw [hy₁] at hy'
    set Y := NeronModelInfra.schemeHomOverComp
      (⟨y.1, by rw [← ei]; exact y.2⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (i ≫ f))
      (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) with hY
    set Aa := NeronModelInfra.schemeHomOverComp a' jG with hAa
    set s' := NeronModelInfra.schemeHomOverComp s ι₀ with hs'
    calc x * s'⁻¹ = x * Aa⁻¹ * Aa * s'⁻¹ := by rw [inv_mul_cancel_right]
      _ = Aa * Y := by
          rw [hy', mul_inv_eq_iff_eq_mul, mul_comm s' Y, _root_.mul_assoc Y s' Aa, mul_comm s' Aa,
            ← _root_.mul_assoc, mul_comm Y Aa]
  let Z : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (kerStr LA π) → Set G := fun s =>
    (translate L (L.inv _ (NeronModelInfra.schemeHomOverComp s ι₀))).1.base ⁻¹'
      (q.1.base ⁻¹' Set.range u.base)
  have hZcl : ∀ s, IsClosed (Z s) := fun s =>
    (hCA.preimage q.1.continuous).preimage (Scheme.Hom.continuous _)
  have hZmem : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f, ∃ s ∈ S, pt x ∈ Z s := by
    intro x
    obtain ⟨s, hs, a', y, hxy⟩ := hdec₀ x
    refine ⟨s, hs, ?_⟩
    let : CommGroup (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) := L.pointCommGroup hc (𝟙 (Spec
        (CommRingCat.of k)))
    let : CommGroup (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) fQ) := LQ.pointCommGroup (hQcomm
        hc) (𝟙 (Spec (CommRingCat.of k)))
    change (translate L _).1.base (pt x) ∈ q.1.base ⁻¹' Set.range u.base
    have e1 : (translate L (L.inv _ (NeronModelInfra.schemeHomOverComp s ι₀))).1.base (pt x) =
        pt (x * (NeronModelInfra.schemeHomOverComp s ι₀)⁻¹) := by
      rw [← pt_comp x (translate L _), comp_translate, constPt_id]
      rfl
    rw [e1, Set.mem_preimage, ← pt_comp _ q, hxy]
    change pt (NeronModelInfra.schemeHomOverComp (L.mul _ (NeronModelInfra.schemeHomOverComp a' jG)
      (NeronModelInfra.schemeHomOverComp y ⟨i, rfl⟩)) q) ∈ _
    rw [hqH, (hqker _ (NeronModelInfra.schemeHomOverComp y ⟨i, rfl⟩)).mpr ⟨y, rfl⟩, LQ.mul_one]
    refine ⟨pt a', ?_⟩
    rw [pt_comp, pt_comp, hu_def, Scheme.Hom.comp_apply]
  have : JacobsonSpace G := LocallyOfFiniteType.jacobsonSpace f
  have : JacobsonSpace A := LocallyOfFiniteType.jacobsonSpace (j ≫ f)
  have hUnion : (⋃ s ∈ S, Z s) = Set.univ := by
    have hcl : IsClosed (⋃ s ∈ S, Z s) := hSfin.isClosed_biUnion fun s _ => hZcl s
    apply Set.eq_univ_of_univ_subset
    rw [← closure_closedPoints (X := G)]
    refine closure_minimal ?_ hcl
    intro z hz
    obtain ⟨x, rfl⟩ := exists_pt_eq (f := f) hz
    obtain ⟨s, hs, hmem⟩ := hZmem x
    exact Set.mem_biUnion hs hmem
  have : IrreducibleSpace G := by
    obtain ⟨G₀, i₀', -, hoi, -, hirr', hrange', -⟩ :=
      exists_isOpenImmersion_irreducibleSpace_range_eq_connectedComponent_finiteIndex
        k L
    rw [PreconnectedSpace.connectedComponent_eq_univ, Set.range_eq_univ] at hrange'
    rw [irreducibleSpace_def, Set.top_eq_univ, ← Set.image_univ_of_surjective hrange']
    exact IsIrreducible.image (IrreducibleSpace.isIrreducible_univ G₀) _ i₀'.continuous.continuousOn
  obtain ⟨s₀, -, hZs₀⟩ : ∃ s ∈ S, Z s = Set.univ := by
    have hirrG := (IrreducibleSpace.isIrreducible_univ G)
    rw [isIrreducible_iff_sUnion_isClosed] at hirrG
    obtain ⟨z, hz, hz'⟩ := hirrG (hSfin.toFinset.image Z)
      (fun z hz => by
        obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hz
        exact hZcl s)
      (by
        intro w _
        have hw : w ∈ ⋃ s ∈ S, Z s := hUnion.symm ▸ Set.mem_univ w
        obtain ⟨s, hs, hws⟩ := Set.mem_iUnion₂.mp hw
        exact Set.mem_sUnion.mpr ⟨Z s, Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨s,
            hSfin.mem_toFinset.mpr hs, rfl⟩), hws⟩)
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨s, hSfin.mem_toFinset.mp hs, Set.eq_univ_of_univ_subset hz'⟩
  have hall : ∀ z : G, q.1.base z ∈ Set.range u.base := by
    intro z
    have h2 : (translate L (L.inv _ (NeronModelInfra.schemeHomOverComp s₀ ι₀))).1.base
        ((translate L (NeronModelInfra.schemeHomOverComp s₀ ι₀)).1.base z) = z := by
      rw [← Scheme.Hom.comp_apply, translate_comp_translate_inv]
      rfl
    have h1 : (translate L (NeronModelInfra.schemeHomOverComp s₀ ι₀)).1.base z ∈ Z s₀ :=
      hZs₀.symm ▸ Set.mem_univ _
    change (translate L (L.inv _ (NeronModelInfra.schemeHomOverComp s₀ ι₀))).1.base
        ((translate L (NeronModelInfra.schemeHomOverComp s₀ ι₀)).1.base z) ∈
      q.1.base ⁻¹' Set.range u.base at h1
    rw [h2] at h1
    exact h1
  have hdec : ∀ z : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
      ∃ (a' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (j ≫ f))
        (y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (i ≫ f)),
        z = L.mul _ (NeronModelInfra.schemeHomOverComp a' jG) (NeronModelInfra.schemeHomOverComp y
            ⟨i, rfl⟩) := by
    intro z
    obtain ⟨p, hp⟩ := hall (pt z)
    have hqz : IsClosed ({q.1.base (pt z)} : Set Q) := by
      rw [← pt_comp z q]; exact isClosed_pt (f := fQ) _
    have hF : IsClosed (u.base ⁻¹' {q.1.base (pt z)}) := hqz.preimage u.continuous
    have hFne : (u.base ⁻¹' {q.1.base (pt z)} ∩ closedPoints A).Nonempty := by
      by_contra hcon
      rw [Set.not_nonempty_iff_eq_empty] at hcon
      have := closure_inter_closedPoints hF
      rw [hcon, closure_empty] at this
      have hpF : p ∈ u.base ⁻¹' {q.1.base (pt z)} := hp
      rw [← this] at hpF
      exact hpF
    obtain ⟨p₀, hp₀F, hp₀cl⟩ := hFne
    obtain ⟨a', ha'⟩ := exists_pt_eq (f := j ≫ f) (mem_closedPoints_iff.mp hp₀cl)
    have hQpt : NeronModelInfra.schemeHomOverComp z q =
        NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp a' jG) q := by
      apply eq_of_pt_eq (f := fQ)
      rw [pt_comp, pt_comp, pt_comp, hjG, ha']
      change _ = q.1.base (j.base p₀)
      rw [← Scheme.Hom.comp_apply]
      exact hp₀F.symm
    let : CommGroup (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) := L.pointCommGroup hc (𝟙 (Spec
        (CommRingCat.of k)))
    let : CommGroup (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) fQ) := LQ.pointCommGroup (hQcomm
        hc) (𝟙 (Spec (CommRingCat.of k)))
    have hk : NeronModelInfra.schemeHomOverComp (z * (NeronModelInfra.schemeHomOverComp a' jG)⁻¹) q
        =
        LQ.one _ := by
      change NeronModelInfra.schemeHomOverComp
        (L.mul _ z (L.inv _ (NeronModelInfra.schemeHomOverComp a' jG))) q = _
      rw [hqH, hqH.inv, hQpt]
      exact _root_.mul_inv_cancel _
    obtain ⟨y, hy⟩ := (hqker _ _).mp hk
    refine ⟨a', y, ?_⟩
    change z = NeronModelInfra.schemeHomOverComp a' jG * NeronModelInfra.schemeHomOverComp y ⟨i,
        rfl⟩
    rw [hy, mul_comm, inv_mul_cancel_right]
  set tT : pullback (j ≫ f) (i ≫ f) ⟶ Spec (CommRingCat.of k) := pullback.fst (j ≫ f) (i ≫ f) ≫ j ≫
      f
    with htT
  set xA : SchemeHomOver tT f := ⟨pullback.fst (j ≫ f) (i ≫ f) ≫ j, Category.assoc _ _ _⟩ with hxA
  set xN : SchemeHomOver tT f := ⟨pullback.snd (j ≫ f) (i ≫ f) ≫ i,
    (Category.assoc _ _ _).trans pullback.condition.symm⟩ with hxN
  set m := L.mul tT xA xN with hm
  have : LocallyOfFiniteType tT := by rw [htT]; infer_instance
  have : LocallyOfFiniteType (m.1 ≫ f) := by rw [m.2]; infer_instance
  have : LocallyOfFiniteType m.1 := locallyOfFiniteType_of_comp _ f
  have : QuasiCompact tT := by rw [htT]; infer_instance
  have : QuasiCompact (m.1 ≫ f) := by rw [m.2]; infer_instance
  have : QuasiCompact m.1 := MorphismProperty.of_postcomp (W := @QuasiCompact) (W' :=
      @QuasiSeparated)
    m.1 f inferInstance inferInstance
  have hsurjm : Surjective m.1 := by
    apply AlgebraicGeometry.surjective_of_forall_exists_comp_eq_of_isAlgClosed m.1 f
    intro zpt hz
    obtain ⟨a', y, hzy⟩ := hdec ⟨zpt, hz⟩
    refine ⟨pullback.lift a'.1 y.1 (by rw [a'.2, y.2]), ?_⟩
    set x' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) tT :=
      ⟨pullback.lift a'.1 y.1 (by rw [a'.2, y.2]), by rw [htT, pullback.lift_fst_assoc, a'.2]⟩ with
          hx'
    have e := congrArg Subtype.val (comp_lawMul L x' xA xN)
    have eA : NeronModelInfra.schemeHomOverComp x' xA = NeronModelInfra.schemeHomOverComp a' jG :=
      Subtype.ext (by simp only [NeronModelInfra.schemeHomOverComp_coe, hxA, hjG, hx',
          pullback.lift_fst_assoc])
    have eN : NeronModelInfra.schemeHomOverComp x' xN =
        NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) :=
      Subtype.ext (by simp only [NeronModelInfra.schemeHomOverComp_coe, hxN, hx',
          pullback.lift_snd_assoc])
    rw [eA, eN, ← hzy] at e
    simpa only [NeronModelInfra.schemeHomOverComp_coe, hm] using e
  have : Surjective u := ⟨by
    rw [← Set.range_eq_univ, Set.eq_univ_iff_forall]
    intro w
    obtain ⟨z, rfl⟩ := q.1.surjective w
    exact hall z⟩
  have : UniversallyClosed fQ := by
    have : UniversallyClosed (u ≫ fQ) := by rw [hu]; infer_instance
    exact UniversallyClosed.of_comp_surjective u fQ
  have : IsProper fQ := ⟨⟩
  have : ConnectedSpace Q := Function.Surjective.connectedSpace q.1.surjective q.1.continuous
  have hQab : AbelianSchemePropertyBundle k fQ :=
    ⟨inferInstance, inferInstance, fun s => by
      have : fQ.base ⁻¹' {s} = Set.univ := Set.eq_univ_of_forall fun _w => Subsingleton.elim _ _
      rw [this]; exact isConnected_univ, ⟨LQ⟩⟩
  obtain ⟨ℓ, h2ℓ, hcop, hℓk⟩ := TorsionCounts.exists_two_le_coprime_cast_ne_zero k n hn
  have hcardA :=
    natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero
      k (j ≫ f) LA hAc hAab a ℓ hℓk
  have hcardQ :=
    natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero
      k fQ LQ (hQcomm hc) hQab (g - h) ℓ hℓk
  let : CommGroup (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (j ≫ f)) := LA.pointCommGroup hAc (𝟙
      (Spec (CommRingCat.of k)))
  let : CommGroup (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) fQ) := LQ.pointCommGroup (hQcomm hc)
      (𝟙 (Spec (CommRingCat.of k)))
  let : CommGroup (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) := L.pointCommGroup hc (𝟙 (Spec
      (CommRingCat.of k)))
  have huH : IsHom LA LQ (NeronModelInfra.schemeHomOverComp jG q) := hj.comp hqH
  let φ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (j ≫ f) →*
      SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) fQ :=
    { toFun := fun a' => NeronModelInfra.schemeHomOverComp a' (NeronModelInfra.schemeHomOverComp jG
        q)
      map_one' := huH.one _
      map_mul' := fun x y => huH _ x y }
  have hφ : ∀ a', φ a' = NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp a' jG)
      q :=
    fun a' => (NeronModelInfra.schemeHomOverComp_assoc _ _ _).symm
  have hφsurj : Function.Surjective φ := by
    intro w
    have : LocallyOfFiniteType q.1 := inferInstance
    obtain ⟨zpt, hz⟩ :=
      AlgebraicGeometry.exists_comp_eq_of_surjective_of_locallyOfFiniteType_of_isAlgClosed q.1 w.1
    let z : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f :=
      ⟨zpt, by rw [← q.2, ← Category.assoc, hz]; exact w.2⟩
    obtain ⟨a', y, hzy⟩ := hdec z
    refine ⟨a', ?_⟩
    rw [hφ]
    have : NeronModelInfra.schemeHomOverComp z q = w := Subtype.ext hz
    rw [← this, hzy, hqH, (hqker _ (NeronModelInfra.schemeHomOverComp y ⟨i, rfl⟩)).mpr ⟨y, rfl⟩,
      LQ.mul_one]
  have hφker : ∀ a', φ a' = 1 → a' ^ n = 1 := by
    intro a' h1
    rw [hφ] at h1
    obtain ⟨y, hy⟩ := (hqker _ _).mp h1
    have := hNker _ y
    rw [hy, hjG, hπj] at this
    rw [← nsmul_eq_pow LA hAc]
    exact this
  have hcard := TorsionCounts.natCard_torsion_eq_of_surjective φ hφsurj n ℓ hcop hφker
  have eA : Nat.card {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (j ≫ f) //
      LA.IsTorsionPoint (𝟙 (Spec (CommRingCat.of k))) ℓ x} =
      Nat.card {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (j ≫ f) // x ^ ℓ = 1} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => by
      rw [isTorsionPoint_def, nsmul_eq_pow LA hAc]; rfl)
  have eQ : Nat.card {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) fQ //
      LQ.IsTorsionPoint (𝟙 (Spec (CommRingCat.of k))) ℓ x} =
      Nat.card {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) fQ // x ^ ℓ = 1} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => by
      rw [isTorsionPoint_def, nsmul_eq_pow LQ (hQcomm hc)]; rfl)
  have hpow : ℓ ^ (2 * a) = ℓ ^ (2 * (g - h)) := by rw [← hcardA, ← hcardQ, eA, eQ, hcard]
  have hag : 2 * a = 2 * (g - h) := Nat.pow_right_injective h2ℓ hpow
  have hh : h = g - a := by omega
  subst hh
  exact ⟨N, i, LN, inferInstance, inferInstance, hsmN, by omega, hLNhom, hsurjm⟩

end Main

end Decomposition
end
end AbelianVarieties.NOSProofs.RosenlichtDecomposition

namespace GoodReductionJacobian.RelativeGroupLaw

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open AbelianVarieties.NOSProofs.RosenlichtDecomposition.Decomposition

universe u

theorem exists_isClosedImmersion_surjective_mul_of_isProper_of_isCommutative
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G]
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    {A : Scheme.{u}} (j : A ⟶ G) [IsClosedImmersion j] [ConnectedSpace A] [IsProper (j ≫ f)]
    (LA : RelativeGroupLaw k (j ≫ f)) (a : ℕ) [SmoothOfRelativeDimension a (j ≫ f)]
    (hj : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (j ≫ f)),
      NeronModelInfra.schemeHomOverComp (LA.mul t x y) (⟨j, rfl⟩ : SchemeHomOver (j ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨j, rfl⟩ : SchemeHomOver (j ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨j, rfl⟩ : SchemeHomOver (j ≫ f) f))) :
    ∃ (N : Scheme.{u}) (i : N ⟶ G) (LN : RelativeGroupLaw k (i ≫ f)),
      IsClosedImmersion i ∧ ConnectedSpace N ∧ SmoothOfRelativeDimension (g - a) (i ≫ f) ∧
      a ≤ g ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
        NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
          L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
            (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))) ∧
      Surjective
        (L.mul (pullback.fst (j ≫ f) (i ≫ f) ≫ j ≫ f)
          ⟨pullback.fst (j ≫ f) (i ≫ f) ≫ j, Category.assoc _ _ _⟩
          ⟨pullback.snd (j ≫ f) (i ≫ f) ≫ i,
            (Category.assoc _ _ _).trans pullback.condition.symm⟩).1 := by
  have : Smooth f := SmoothOfRelativeDimension.smooth g f
  have : Smooth (j ≫ f) := SmoothOfRelativeDimension.smooth a (j ≫ f)
  obtain ⟨n, π, hn, hπ, hπj⟩ :=
    exists_retraction_up_to_nsmul_of_proper_subgroup
      k f L hc j LA hj
  obtain ⟨N, i, LN, h1, h2, h3, h4, h5, h6⟩ :=
    exists_complement k f L hc g j LA a hj n hn π hπ hπj
  exact ⟨N, i, LN, h1, h2, h3, h4, h5, h6⟩

end GoodReductionJacobian.RelativeGroupLaw
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_isProper_of_forall_isAffine_isClosedImmersion_eq_zero.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.PropernessCriterion

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian

universe u

namespace Core
open AbelianVarieties.NOSProofs.RosenlichtRetractions.RetractionConstruction
  (castLaw castLaw_mul_val)
open _root_.GoodReductionJacobian.RelativeGroupLaw
open _root_.GoodReductionJacobian

section Laws

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}

/-- The inclusion of a subgroup respects its relative group law. -/
abbrev IsHom (L : RelativeGroupLaw k f) {N : Scheme.{u}} (i : N ⟶ G)
    (LN : RelativeGroupLaw k (i ≫ f)) : Prop :=
  AbelianVarieties.NOSProofs.RosenlichtRetractions.RetractionConstruction.IsHom LN L ⟨i, rfl⟩

/-- Every connected smooth affine subgroup has relative dimension zero. -/
def NoAffSub (L : RelativeGroupLaw k f) : Prop :=
  ∀ (N : Scheme.{u}) (i : N ⟶ G) (LN : RelativeGroupLaw k (i ≫ f)) (h : ℕ),
    IsClosedImmersion i → IsAffine N → ConnectedSpace N → SmoothOfRelativeDimension h (i ≫ f) →
    IsHom L i LN → h = 0

theorem eq_of_comp_incl_eq {N : Scheme.{u}} (i : N ⟶ G) [Mono i] {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of k)} {x y : SchemeHomOver t (i ≫ f)}
    (hxy : NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
      NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)) : x = y :=
  AbelianVarieties.NOSProofs.RosenlichtRetractions.RetractionConstruction.eq_of_comp_mono_eq
    ⟨i, rfl⟩ hxy

theorem isCommutative_of_isHom (L : RelativeGroupLaw k f) (hc : L.IsCommutative)
    {N : Scheme.{u}} (i : N ⟶ G) [Mono i] (LN : RelativeGroupLaw k (i ≫ f))
    (hi : IsHom L i LN) : LN.IsCommutative :=
AbelianVarieties.NOSProofs.RosenlichtRetractions.RetractionConstruction.isCommutative_of_isHom_mono
    hc ⟨i, rfl⟩ hi

end Laws

section Subgroups

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}

theorem isHom_id (L : RelativeGroupLaw k f) :
    IsHom L (𝟙 G) (castLaw (Category.id_comp f).symm L) := by
  intro T t x y
  apply Subtype.ext
  rw [NeronModelInfra.schemeHomOverComp_coe, castLaw_mul_val, Category.comp_id]
  congr 2

theorem noAffSub_of_isHom (L : RelativeGroupLaw k f) (hG : NoAffSub L)
    {H : Scheme.{u}} (i : H ⟶ G) [IsClosedImmersion i] (LH : RelativeGroupLaw k (i ≫ f))
    (hi : IsHom L i LH) : NoAffSub LH := by
  intro N i' LN h hci hNa hNc hNs hhom
  have e : i' ≫ i ≫ f = (i' ≫ i) ≫ f := (Category.assoc i' i f).symm
  have hs : SmoothOfRelativeDimension h ((i' ≫ i) ≫ f) := by rw [Category.assoc]; exact hNs
  refine hG N (i' ≫ i) (castLaw e LN) h inferInstance hNa hNc hs ?_
  intro T t x y
  apply Subtype.ext
  rw [NeronModelInfra.schemeHomOverComp_coe, castLaw_mul_val]
  set x' : SchemeHomOver t (i' ≫ i ≫ f) := ⟨x.1, by rw [e]; exact x.2⟩ with hx'
  set y' : SchemeHomOver t (i' ≫ i ≫ f) := ⟨y.1, by rw [e]; exact y.2⟩ with hy'
  have h1 := congrArg Subtype.val (hhom t x' y')
  simp only [NeronModelInfra.schemeHomOverComp_coe] at h1
  have h2 := congrArg Subtype.val
    (hi t (NeronModelInfra.schemeHomOverComp x' (⟨i', rfl⟩ : SchemeHomOver (i' ≫ i ≫ f) (i ≫ f)))
      (NeronModelInfra.schemeHomOverComp y' (⟨i', rfl⟩ : SchemeHomOver (i' ≫ i ≫ f) (i ≫ f))))
  simp only [NeronModelInfra.schemeHomOverComp_coe] at h2
  rw [← Category.assoc, h1, h2]
  congr 2

end Subgroups

section Induction

theorem isProper_of_noAffSub (k : Type u) [Field k] [IsAlgClosed k] :
    ∀ (g : ℕ) {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
      [IsSeparated f] [QuasiCompact f] [ConnectedSpace G]
      (L : RelativeGroupLaw k f) (_ : L.IsCommutative) [SmoothOfRelativeDimension g f]
      (_ : NoAffSub L), IsProper f := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
    intro G f _ _ _ L hc _ hG
    by_contra hnp
    rcases isAffine_or_exists_isClosedImmersion_lt_of_not_isProper
        k f L g hnp with hAff | ⟨H, i, LH, h, hci, hHc, hHs, hhom, h1, hlt⟩
    · have hs : SmoothOfRelativeDimension g (𝟙 G ≫ f) := by rw [Category.id_comp]; infer_instance
      have hg0 : g = 0 := hG G (𝟙 G) (castLaw (Category.id_comp f).symm L) g inferInstance hAff
        inferInstance hs (isHom_id L)
      subst hg0
      have : IsFinite f :=
        AlgebraicGeometry.IsFinite.of_smoothOfRelativeDimension_zero_of_field f
      exact hnp inferInstance
    · have hHcomm : LH.IsCommutative := isCommutative_of_isHom L hc i LH hhom
      have hHno : NoAffSub LH := noAffSub_of_isHom L hG i LH hhom
      have hHproper : IsProper (i ≫ f) := ih h hlt (i ≫ f) LH hHcomm hHno
      obtain ⟨N, i₂, LN, hci₂, hNc, hNs, -, hhom₂, hsurj⟩ :=
        exists_isClosedImmersion_surjective_mul_of_isProper_of_isCommutative
          k f L hc g i LH h hhom
      have hNcomm : LN.IsCommutative := isCommutative_of_isHom L hc i₂ LN hhom₂
      have hNno : NoAffSub LN := noAffSub_of_isHom L hG i₂ LN hhom₂
      have hNproper : IsProper (i₂ ≫ f) := ih (g - h) (by omega) (i₂ ≫ f) LN hNcomm hNno
      set m := L.mul (pullback.fst (i ≫ f) (i₂ ≫ f) ≫ i ≫ f)
          ⟨pullback.fst (i ≫ f) (i₂ ≫ f) ≫ i, Category.assoc _ _ _⟩
          ⟨pullback.snd (i ≫ f) (i₂ ≫ f) ≫ i₂,
            (Category.assoc _ _ _).trans pullback.condition.symm⟩ with hm
      have : Surjective m.1 := hsurj
      have hmf : m.1 ≫ f = pullback.fst (i ≫ f) (i₂ ≫ f) ≫ i ≫ f := m.2
      have huc : UniversallyClosed (m.1 ≫ f) := by rw [hmf]; infer_instance
      have hucf : UniversallyClosed f := UniversallyClosed.of_comp_surjective m.1 f
      have hsm : Smooth f := SmoothOfRelativeDimension.smooth g f
      exact hnp ((isProper_iff f).mpr ⟨inferInstance, hucf, inferInstance⟩)

end Induction

end Core
end AbelianVarieties.NOSProofs.PropernessCriterion

namespace GoodReductionJacobian.RelativeGroupLaw

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open AbelianVarieties.NOSProofs.PropernessCriterion.Core

universe u
theorem isProper_of_forall_isAffine_isClosedImmersion_eq_zero
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G]
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    (hG : ∀ (N : Scheme.{u}) (i : N ⟶ G) (LN : RelativeGroupLaw k (i ≫ f)) (h : ℕ),
      IsClosedImmersion i → IsAffine N → ConnectedSpace N → SmoothOfRelativeDimension h (i ≫ f) →
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
        NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
          L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
            (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))) →
      h = 0) :
    IsProper f :=
  isProper_of_noAffSub k g f L hc hG

end GoodReductionJacobian.RelativeGroupLaw
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_isAffine_isClosedImmersion_abelianSchemePropertyBundle_of_not_isProper.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.ChevalleyAssembly

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian

universe u

namespace Assembly
open AbelianVarieties.NOSProofs.PropernessCriterion.Core
  (IsHom eq_of_comp_incl_eq isCommutative_of_isHom)
open _root_.GoodReductionJacobian.RelativeGroupLaw
open _root_.GoodReductionJacobian

section Subgroups

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}

theorem exists_conj_eq_of_isCommutative (L : RelativeGroupLaw k f) (hc : L.IsCommutative)
    {N : Scheme.{u}} (i : N ⟶ G) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (x : SchemeHomOver t f) (n : SchemeHomOver t (i ≫ f)) :
    ∃ n' : SchemeHomOver t (i ≫ f),
      NeronModelInfra.schemeHomOverComp n' (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (L.mul t x (NeronModelInfra.schemeHomOverComp n (⟨i, rfl⟩ : SchemeHomOver (i ≫ f)
            f)))
          (L.inv t x) :=
  ⟨n, by rw [hc t x, L.mul_assoc, L.mul_inv_cancel, L.mul_one]⟩

theorem geometricallyConnected_of_connectedSpace {N : Scheme.{u}}
    {fN : N ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType fN] [QuasiCompact fN] [ConnectedSpace N]
    (LN : RelativeGroupLaw k fN) : GeometricallyConnected fN := by
  obtain ⟨G₀, i₀, L₀, hopen, _, _, _, hgc, hrange, _⟩ :=
    exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent
      k LN
  have hsurj : Surjective i₀ := ⟨by
    rw [← Set.range_eq_univ, hrange]
    exact PreconnectedSpace.connectedComponent_eq_univ _⟩
  have : IsIso i₀ := (isIso_iff_isOpenImmersion_and_surjective i₀).mpr ⟨hopen, hsurj⟩
  have : MorphismProperty.RespectsIso
      (@GeometricallyConnected : MorphismProperty Scheme.{u}) := by
    rw [GeometricallyConnected.eq_geometrically, geometrically_eq_universally]
    exact MorphismProperty.universally_respectsIso _
  exact (MorphismProperty.cancel_left_of_respectsIso
    (@GeometricallyConnected : MorphismProperty Scheme.{u}) i₀ fN).mp hgc

end Subgroups

section Family

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}

/-- A connected affine subgroup of the specified relative dimension. -/
def AffSub (L : RelativeGroupLaw k f) (h : ℕ) : Prop :=
  ∃ (N : Scheme.{u}) (i : N ⟶ G) (LN : RelativeGroupLaw k (i ≫ f)),
    IsClosedImmersion i ∧ IsAffine N ∧ ConnectedSpace N ∧ SmoothOfRelativeDimension h (i ≫ f) ∧
      IsHom L i LN

end Family

section Assembly

theorem exists_affSub_ne_zero (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}}
    (f : G ⟶ Spec (CommRingCat.of k)) [IsSeparated f] [QuasiCompact f] [ConnectedSpace G]
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (g : ℕ) [SmoothOfRelativeDimension g f]
    (hG : ¬ IsProper f) : ∃ h, AffSub L h ∧ h ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hG
  refine isProper_of_forall_isAffine_isClosedImmersion_eq_zero
    k f L hc g ?_
  intro N i LN h hci hNa hNc hNs hhom
  exact hcon h ⟨N, i, LN, hci, hNa, hNc, hNs, hhom⟩

theorem le_of_affSub (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}}
    (f : G ⟶ Spec (CommRingCat.of k)) [IsSeparated f] [QuasiCompact f]
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (g : ℕ) [SmoothOfRelativeDimension g f]
    (h : ℕ) (hh : AffSub L h) : h ≤ g := by
  obtain ⟨N, i, LN, hci, hNa, hNc, hNs, hhom⟩ := hh
  obtain ⟨Q, fQ, LQ, q, -, -, -, hle, -⟩ :=
    exists_quotient_smoothOfRelativeDimension_sub_of_isClosedImmersion_of_isAlgClosed
      k f L g i LN h hhom (exists_conj_eq_of_isCommutative L hc i)
  exact hle

end Assembly

end Assembly
end AbelianVarieties.NOSProofs.ChevalleyAssembly

namespace GoodReductionJacobian.RelativeGroupLaw

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open AbelianVarieties.NOSProofs.ChevalleyAssembly.Assembly
open AbelianVarieties.NOSProofs.PropernessCriterion.Core (isCommutative_of_isHom)

universe u
theorem exists_isAffine_isClosedImmersion_abelianSchemePropertyBundle_of_not_isProper
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G]
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative)
    (g : ℕ) [SmoothOfRelativeDimension g f] (hG : ¬ IsProper f) :
    ∃ (N : Scheme.{u}) (i : N ⟶ G) (LN : RelativeGroupLaw k (i ≫ f)) (h : ℕ)
      (A : Scheme.{u}) (fA : A ⟶ Spec (CommRingCat.of k)) (LA : RelativeGroupLaw k fA) (a : ℕ)
      (q : SchemeHomOver f fA),
      IsClosedImmersion i ∧ IsAffine N ∧ ConnectedSpace N ∧ SmoothOfRelativeDimension h (i ≫ f) ∧
      LN.IsCommutative ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
        NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
          L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
            (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))) ∧
      AbelianSchemePropertyBundle k fA ∧ SmoothOfRelativeDimension a fA ∧ LA.IsCommutative ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
        NeronModelInfra.schemeHomOverComp (L.mul t x y) q =
          LA.mul t (NeronModelInfra.schemeHomOverComp x q) (NeronModelInfra.schemeHomOverComp y q))
              ∧
      Surjective q.1 ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
        NeronModelInfra.schemeHomOverComp x q = LA.one t ↔
          ∃ y : SchemeHomOver t (i ≫ f),
            NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) = x) ∧
      g = h + a ∧ 1 ≤ h := by
  classical
  obtain ⟨h₁, hh₁, hh₁0⟩ := exists_affSub_ne_zero k f L hc g hG
  have hbound : ∀ h, AffSub L h → h ≤ g := le_of_affSub k f L hc g
  set h₀ := Nat.findGreatest (fun h => AffSub L h) g with hh₀def
  have hmem : AffSub L h₀ := Nat.findGreatest_spec (hbound h₁ hh₁) hh₁
  have hmax : ∀ h, AffSub L h → h ≤ h₀ := fun h hh => Nat.le_findGreatest (hbound h hh) hh
  have h₀pos : 1 ≤ h₀ := by
    have := hmax h₁ hh₁
    omega
  have h₀le : h₀ ≤ g := hbound h₀ hmem
  obtain ⟨N, i, LN, hci, hNa, hNc, hNs, hhom⟩ := hmem
  obtain ⟨Q, fQ, LQ, q, hsep, hqc, hQs, -, hqs, hsurj, hqhom, hQcomm, hker⟩ :=
    exists_quotient_smoothOfRelativeDimension_sub_of_isClosedImmersion_of_isAlgClosed
      k f L g i LN h₀ hhom (exists_conj_eq_of_isCommutative L hc i)
  have hqqc : QuasiCompact q.1 := by
    have : QuasiCompact (q.1 ≫ fQ) := by rw [q.2]; infer_instance
    exact QuasiCompact.of_comp q.1 fQ
  have hNsm : Smooth (i ≫ f) := SmoothOfRelativeDimension.smooth h₀ (i ≫ f)
  have hNgc : GeometricallyConnected (i ≫ f) := geometricallyConnected_of_connectedSpace LN
  have hQcore : ∀ (M : Scheme.{u}) (j : M ⟶ Q) (LM : RelativeGroupLaw k (j ≫ fQ)) (m : ℕ),
      IsClosedImmersion j → IsAffine M → ConnectedSpace M → SmoothOfRelativeDimension m (j ≫ fQ) →
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (j ≫ fQ)),
        NeronModelInfra.schemeHomOverComp (LM.mul t x y) (⟨j, rfl⟩ : SchemeHomOver (j ≫ fQ) fQ) =
          LQ.mul t (NeronModelInfra.schemeHomOverComp x (⟨j, rfl⟩ : SchemeHomOver (j ≫ fQ) fQ))
            (NeronModelInfra.schemeHomOverComp y (⟨j, rfl⟩ : SchemeHomOver (j ≫ fQ) fQ))) →
      m = 0 := by
    intro M j LM m hcj hMa hMc hMs hjhom
    obtain ⟨P, ι, LP, hcι, hPa, hPc, hPs, hιhom, -⟩ :=
      exists_isAffine_isClosedImmersion_of_isAffine_of_comp_eq_one_iff
        k f L i fQ LQ q h₀ hqhom hker j LM m hjhom
    have hle := hmax (h₀ + m) ⟨P, ι, LP, hcι, hPa, hPc, hPs, hιhom⟩
    omega
  have hQconn : ConnectedSpace Q := by
    have hr : Set.range q.1.base = Set.univ := Set.range_eq_univ.mpr q.1.surjective
    exact connectedSpace_iff_univ.mpr (hr ▸ isConnected_range q.1.continuous)
  have hproper : IsProper fQ :=
    isProper_of_forall_isAffine_isClosedImmersion_eq_zero
      k fQ LQ (hQcomm hc) (g - h₀) hQcore
  have hbundle : AbelianSchemePropertyBundle k fQ :=
    { smooth := SmoothOfRelativeDimension.smooth (g - h₀) fQ
      proper := hproper
      connectedFibres := fun s => by
        have huniv : fQ.base ⁻¹' {s} = Set.univ :=
          Set.eq_univ_of_forall fun _ => Subsingleton.elim (α := PrimeSpectrum k) _ _
        rw [huniv]
        exact isConnected_univ
      hasGroupLaw := ⟨LQ⟩ }
  exact ⟨N, i, LN, h₀, Q, fQ, LQ, g - h₀, q, hci, hNa, hNc, hNs,
    isCommutative_of_isHom L hc i LN hhom, hhom, hbundle, hQs, hQcomm hc, hqhom, hsurj, hker,
    by omega, h₀pos⟩

end GoodReductionJacobian.RelativeGroupLaw
end
